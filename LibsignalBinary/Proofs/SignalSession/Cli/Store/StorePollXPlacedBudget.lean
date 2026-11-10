/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `store_session::{closure#0}` at `serializeStackX`

Proves budget-threaded `sessStorePollSpecPlaced` on Block `570` (`lsProg_570 H`) at
`serializeStackX` under `[LibsignalPlacement]`, plus its caller-block-polymorphic transfer.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecHeader vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost okTagVec)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.E2E.Record.Serialization (SerializeGhost)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf)
open CryptoVerification.SignalSession.Cli (DirGhost)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_570)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_cl_to_lscro ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
  (memRegion_32_cells stackAt_sub_split)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
  (SerializeEnvX serializeCanonSpecX serializeStackX)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced addrTextSpecPlaced dirPutSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
  (CliStorePollEnv serializeCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget
  (addrText_cells_placed_ok dirPut_cells_placed_ok sessStorePollInner_placed_ok
   sessStorePoll_placed_of_inner)

section Placed

theorem serialize_cells_placed_okX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {entry : BitVec 64} {calleeStk : Nat}
    (hSer : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hle : serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializeCellsSpec A lim SerializeEnvX calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩, st⟩ R s0
    hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - serializeStackX)
  let callG : SerializeGhost × M.σ := (⟨recA, out, g, r⟩, st)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (serializeCanonSpecX M A lim)).pre callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [serializeCanonSpecX, callG]
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
    dsimp only [withLsCodeRoLoaded, serializeCanonSpecX, serializeCellsSpec, callG] at hq ⊢
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
  · dsimp only [withLsCodeRoLoaded, serializeCanonSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializeCanonSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializeCanonSpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Block `570` (`store_session::{closure#0}`) meets `sessStorePollSpecPlaced`
at `serializeStackX` (`withLsCodeLoaded` `serializeCanonSpecX`). -/
theorem sessStorePoll_placed_ok_of_depsX [LibsignalPlacement] {M : AllocCostModel}
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
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hstk : 0xd0 + max (max addrStk serializeStackX) (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim (CliStorePollEnv AddrEnv SerializeEnvX PutEnv) stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_570 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hSer' := ls_transfer_cl_to_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_570 H) hPut (by decide) hPutBlk hPutUnmut
  refine sessStorePoll_placed_of_inner (fun hhi => ?_) hstk
  exact sessStorePollInner_placed_ok
    (addrText_cells_placed_ok hAddr' (by omega) hhi)
    (serialize_cells_placed_okX hSer' (by omega) hhi)
    (dirPut_cells_placed_ok hPut' (by omega) hhi)

/-- Caller-block-polymorphic form of `sessStorePoll_placed_ok_of_depsX`. -/
theorem sessStorePoll_placed_caller_ok_of_depsX [LibsignalPlacement] {M : AllocCostModel}
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
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hstk : 0xd0 + max (max addrStk serializeStackX) (max putStk extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim (CliStorePollEnv AddrEnv SerializeEnvX PutEnv) stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 570)
    (sessStorePoll_placed_ok_of_depsX hC hAddr hSer hPut hstk
      hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
