/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlaced
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `<SessionFiles as SessionStore>::store_session::{closure#0}`

Proves budget-threaded `sessStorePollSpecPlaced` on Block `570` (`lsProg_570 H`) under
`[LibsignalPlacement]`, together with its caller-block-polymorphic transfer.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost okTagVec protocolAddressAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.E2E.Record (RecordGhost encodeRecord sessionRecordAt)
open CryptoVerification.E2E.Record.Serialization (CanonRecord SerializeGhost serializeStack)
open CryptoVerification.E2E.InMem.SessionStoreImpl (record_sessionRecordAt_eq toRecordGhost)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.SignalSession.Cli
  (AddrTextGhost DirGhost DirPutGhost SessStorePollGhost addressText dirAt sessStoreBoxAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_570 blkPl_570 lsProg_570)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
  (canonRecord_of_satisfies_sessionRecordAt memRegion_24_cells memRegion_32_cells
   memRegion_40_cells memRegion_48_cells memRegion_bound_of_pointsTo64
   stackAt_storePoll_frame stackAt_sub_split storePollSlack)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers.CliStorePollNorm
  (extractLsb_append_hi extractLsb_append_lo readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   readVReg128_setMem_pre readVReg128_setMem_setPC_pre readVReg128_setPC_pre
   readVReg128_setPState_pre readVReg128_writeReg64_pre sp_setMem_setPC_pre sp_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
  (SerializeEnv serializeCanonSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced addrTextSpecPlaced dirPutSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
  (CliStorePollEnv addrTextCellsSpec cliStorePollInnerSpec dirPutCellsSpec serializeCellsSpec)

section Placed

attribute [local irreducible] Program.fetch Program.externAt? FitsEnv
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre extractLsb_append_lo extractLsb_append_hi

private theorem cells_26_split_placed (sp : BitVec 64) :
    cells (sp - 208#64) 26 =
      storePollSlack sp ∗
        cells (sp - 200#64) 6 ∗ cells (sp - 144#64) 4 ∗
        cells (sp - 96#64) 5 ∗ cells (sp - 48#64) 6 := by
  rw [show (26 : Nat) = 1 + 25 from rfl, cells_split_sub sp 208 200 1 25,
    show (25 : Nat) = 6 + 19 from rfl, cells_split_sub sp 200 152 6 19,
    show (19 : Nat) = 1 + 18 from rfl, cells_split_sub sp 152 144 1 18,
    show (18 : Nat) = 4 + 14 from rfl, cells_split_sub sp 144 112 4 14,
    show (14 : Nat) = 2 + 12 from rfl, cells_split_sub sp 112 96 2 12,
    show (12 : Nat) = 5 + 7 from rfl, cells_split_sub sp 96 56 5 7,
    show (7 : Nat) = 1 + 6 from rfl, cells_split_sub sp 56 48 1 6]
  dsimp only [storePollSlack]
  sep_ac_rfl

private theorem cells_sub_4_eq_placed (sp : BitVec 64) :
    cells (sp - 144#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗
        ((sp - 128#64) ↦₆₄ v2) ∗ ((sp - 120#64) ↦₆₄ v3) := by
  cells_unfold

private theorem cells_sub_5_eq_placed (sp : BitVec 64) :
    cells (sp - 96#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) := by
  cells_unfold

private theorem cells_sub_6_200_eq_placed (sp : BitVec 64) :
    cells (sp - 200#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) ∗
        ((sp - 176#64) ↦₆₄ v3) ∗ ((sp - 168#64) ↦₆₄ v4) ∗ ((sp - 160#64) ↦₆₄ v5) := by
  cells_unfold

private theorem cells_sub_6_48_eq_placed (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) := by
  cells_unfold

theorem addrText_cells_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {addrStk calleeStk : Nat}
    (hAddr : subroutine_ok prog entry (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hle : addrStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (addrTextCellsSpec A lim AddrEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨⟨addrA, g, ret, o0, o1, o2, fsp⟩, st⟩ R s0
    hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [addrTextCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp, hlen, hfit, hlr_ls⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - addrStk)
  let callG : AddrTextGhost × M.σ := (⟨addrA, g, ret⟩, st)
  have hpre0 : s0.mem ⊨ (addrTextSpecPlaced A lim AddrEnv addrStk).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold addrTextSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlen, hfit, hlr_ls⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hAddr.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, addrTextSpecPlaced, addrTextCellsSpec, callG] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    refine ⟨⟨htr, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [addrTextSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [addrTextSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [addrTextSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem serialize_cells_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {calleeStk : Nat}
    (hSer : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializeCanonSpec M A lim)))
    (hle : serializeStack ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializeCellsSpec A lim SerializeEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩, st⟩ R s0
    hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - serializeStack)
  let callG : SerializeGhost × M.σ := (⟨recA, out, g, r⟩, st)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (serializeCanonSpec M A lim)).pre callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [serializeCanonSpec, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon, hlen, hfit⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hSer.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, serializeCanonSpec, serializeCellsSpec, callG] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq
    rcases hq with ⟨bCap, bPtr, hq⟩
    refine ⟨evs, bCap, bPtr, ?_⟩
    rw [vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, serializeCanonSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializeCanonSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializeCanonSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem vecU8_intro_placed (A : RustAlloc) (v bCap bPtr : BitVec 64)
    (bs : List (BitVec 8)) :
    ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      vecU8Buf A bCap bPtr bs ⊢ vecU8 A v bs := by
  have heq :
      ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        vecU8Buf A bCap bPtr bs =
      vecU8At A v bCap bPtr bs := by
    rw [vecU8At_eq_header_sep_buf]
    rfl
  rw [heq]
  exact Entails.sepExists_right bCap (Entails.sepExists_right bPtr (Entails.refl _))

theorem dirPut_cells_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {putStk calleeStk : Nat}
    (hPut : subroutine_ok prog entry (dirPutSpecPlaced A lim PutEnv putStk))
    (hle : putStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (dirPutCellsSpec A lim PutEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨self, dir, nameV, name, bytesV, bCap, bPtr, bytes, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [dirPutCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen, hfit, hlr_ls⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - putStk)
  let callG : DirPutGhost × M.σ := (⟨self, dir, nameV, name, bytesV, bytes⟩, st)
  have hmem_vec : s0.mem ⊨ vecU8 A.repAlloc bytesV bytes ∗
      (dirAt A.repAlloc self dir ∗ vecU8 A.repAlloc nameV name ∗ stackAt s0.sp putStk ∗
        A.pool lim st s0 ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left (vecU8_intro_placed A.repAlloc bytesV bCap bPtr bytes)) ?_
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  have hpre0 : s0.mem ⊨ (dirPutSpecPlaced A lim PutEnv putStk).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold dirPutSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hfit, hlr_ls⟩, ?_⟩
    convert hmem_vec using 1; sep_ac_rfl
  refine hPut.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, dirPutSpecPlaced, dirPutCellsSpec, callG] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hq
    rcases hq with ⟨m2, m1, m0, n2, n1, n0, hq⟩
    refine ⟨evs, n0, n1, n2, m0, m1, m2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [dirPutSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [dirPutSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [dirPutSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessStorePollInner_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {SerEnv : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {calleeStk : Nat}
    (hAddrCells : subroutine_ok (lsProg_570 H) (lsmpl.base 594)
      (withLsCodeRoLoaded lsmpl (addrTextCellsSpec A lim AddrEnv calleeStk)))
    (hSerCells : subroutine_ok (lsProg_570 H) (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCellsSpec A lim SerEnv calleeStk)))
    (hPutCells : subroutine_ok (lsProg_570 H) (lsmpl.base 542)
      (withLsCodeRoLoaded lsmpl (dirPutCellsSpec A lim PutEnv calleeStk))) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl (cliStorePollInnerSpec A lim AddrEnv SerEnv PutEnv calleeStk)) := by
  unfold withLsCodeRoLoaded
  simp (config := { maxSteps := 2000000 }) only [cliStorePollInnerSpec,
    memRegion_48_cells, memRegion_40_cells,
    cells_26_split_placed, cells_sub_4_eq_placed, cells_sub_5_eq_placed,
    cells_sub_6_200_eq_placed, cells_sub_6_48_eq_placed,
    sepExists_sepConj_left, sepExists_sepConj_right]
  change subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (blkPl_570).base _
  wp_init xs s0
  obtain ⟨x, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (CliStorePollEnv AddrEnv SerEnv PutEnv x) := by assumption
  have hfit_addr : FitsEnv M lim st (AddrEnv x.call.call.addr) := hfit0.seq_left
  apply sepWP_seq_lscro (mid := lsmpl.base 594) hcrl0
  wp_steps_sync_pool (lsmpl.base 594)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 594)
      (withLsCodeRoLoaded lsmpl (addrTextCellsSpec A lim AddrEnv calleeStk)) from hAddrCells)
    hcrl1
    ((x.call.call.addrA, x.call.call.addr, s0.sp - 200#64, _, _, _, s0.sp - 208#64), st)
  have hfit_rest : FitsEnv M lim (M.stepEvents w st)
      (SeqEnv (SerEnv (toRecordGhost x.call.call.g) x.call.call.record)
        (PutEnv x.dir (addressText x.call.call.addr.val) (encodeRecord x.call.call.record))) :=
    hfit0.seq_right (by assumption)
  have hfit_ser : FitsEnv M lim (M.stepEvents w st)
      (SerEnv (toRecordGhost x.call.call.g) x.call.call.record) :=
    hfit_rest.seq_left
  apply sepWP_seq_lscro (mid := lsmpl.base 52) hcrl_sf
  wp_steps_sync_pool (lsmpl.base 52)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl2
  wp_call_lscro
    (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCellsSpec A lim SerEnv calleeStk)) from hSerCells)
    hcrl2
    ((x.call.call.recA, s0.sp - 144#64,
      toRecordGhost x.call.call.g, x.call.call.record,
      _, _, _, _, s0.sp - 208#64), M.stepEvents w st)
  have hfit_put : FitsEnv M lim (M.stepEvents w_1 (M.stepEvents w st))
      (PutEnv x.dir (addressText x.call.call.addr.val) (encodeRecord x.call.call.record)) :=
    hfit_rest.seq_right (by assumption)
  apply sepWP_seq_lscro (mid := lsmpl.base 542) hcrl_sf_1
  wp_steps_sync_pool (lsmpl.base 542)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl3
  wp_call_lscro
    (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 542)
      (withLsCodeRoLoaded lsmpl (dirPutCellsSpec A lim PutEnv calleeStk)) from hPutCells)
    hcrl3
    ((x.self, x.dir, s0.sp - 200#64, addressText x.call.call.addr.val,
      s0.sp - 176#64, w_2, w_3, encodeRecord x.call.call.record, s0.sp - 208#64),
      M.stepEvents w_1 (M.stepEvents w st))
  have hcli_evs : CliStorePollEnv AddrEnv SerEnv PutEnv x (w ++ (w_1 ++ w_4)) :=
    SeqEnv.append (by assumption) (SeqEnv.append (by assumption) (by assumption))
  rw [← M.stepEvents_append, ← M.stepEvents_append]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

theorem sessStorePoll_placed_of_inner [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {SerEnv : RecordGhost → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (withLsCodeRoLoaded lsmpl
          (cliStorePollInnerSpec A lim AddrEnv SerEnv PutEnv calleeStk)))
    (hstk : 0xd0 + calleeStk ≤ stk) :
    subroutine_ok prog entry
      (sessStorePollSpecPlaced A lim (CliStorePollEnv AddrEnv SerEnv PutEnv) stk) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessStorePollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, henc, hdir, hfit⟩, hmem⟩
  dsimp only [sessStoreBoxAt] at hmem
  have hcanon : CanonRecord (toRecordGhost x.call.call.g) x.call.call.record := by
    refine canonRecord_of_satisfies_sessionRecordAt A.repAlloc x.call.call.recA
      x.call.call.g x.call.call.record
      ((x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        memRegion (x.call.fut + 25#64) 7 ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        A.pool lim st s0 ∗ stackAt s0.sp stk ∗ R) s0.mem ?_
    convert hmem using 1; sep_ac_rfl
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.call.fut) (v := x.self)
      (R := ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        memRegion (x.call.fut + 25#64) 7 ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        sessionRecordAt A.repAlloc x.call.call.recA x.call.call.g x.call.call.record ∗
        A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 208 ≤ 2 ^ 64 := by omega
  rw [← record_sessionRecordAt_eq] at hmem
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
    stackAt_storePoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.call.fut + 25#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 208))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliStorePollInnerSpec A lim AddrEnv SerEnv PutEnv calleeStk)).pre (x, st) s0 ∗
        (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [cliStorePollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc, hdir, hcanon, hfit⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; sep_ac_rfl
  refine (hInner hcal_hi).mono_outcome (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, cliStorePollInnerSpec, sessStorePollSpecPlaced,
      sessStoreBoxAt] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    refine ⟨⟨htr, hevs⟩, ?_⟩
    rw [record_sessionRecordAt_eq] at hq
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
      stackAt_storePoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, cliStorePollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliStorePollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliStorePollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Block `570` (`store_session::{closure#0}`) meets `sessStorePollSpecPlaced`
given `address_text`, `SessionRecord::serialize`, and `Dir::put::<String>`. -/
theorem sessStorePoll_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (_hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCanonSpec M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hstk : 0xd0 + max (max addrStk serializeStack) (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim (CliStorePollEnv AddrEnv SerializeEnv PutEnv) stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_570 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hSer' := ls_transfer_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_570 H) hPut (by decide) hPutBlk hPutUnmut
  refine sessStorePoll_placed_of_inner (fun hhi => ?_) hstk
  exact sessStorePollInner_placed_ok
    (addrText_cells_placed_ok hAddr' (by omega) hhi)
    (serialize_cells_placed_ok hSer' (by omega) hhi)
    (dirPut_cells_placed_ok hPut' (by omega) hhi)

/-- Caller-block-polymorphic form of `sessStorePoll_placed_ok_of_deps`. -/
theorem sessStorePoll_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg addrProg serProg putProg : Program}
    {callerBlk addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCanonSpec M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hstk : 0xd0 + max (max addrStk serializeStack) (max putStk extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim (CliStorePollEnv AddrEnv SerializeEnv PutEnv) stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 570)
    (sessStorePoll_placed_ok_of_deps hC hAddr hSer hPut hstk
      hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget
