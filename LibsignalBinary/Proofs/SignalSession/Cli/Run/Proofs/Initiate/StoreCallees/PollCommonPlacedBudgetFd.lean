/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `FdsGe3Closed`-Threaded Store Poll Helpers (`[LibsignalPlacement]`)

`FdsGe3Closed`-preserving cell-oriented wrappers for `Dir::get` (Block `589`), `__rust_dealloc`,
and `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`), plus shared Block `567` frame
helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles extract_withLsCodeRoLoaded subroutine_ok_rocl_of_withLsCodeRoLoaded
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speAt speWord strRefAt vecResultAt)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RecordCodecsBinary (DecodeGhost identityKeyPairResultAt)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (DirGetGhost DirGhost ReadRule getResultAt pathOf utf8)
open CryptoVerification.SignalSession.Cli.RunDrop (speOwnedAt)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon
  (DirGetRoCellsGhost IkpTryFromCellsGhost pointsToBytes72_split_qwords)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs (idKeyPairOutAt)
open CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
  (stackAt_sub_split vecU8At_eq_expose vecU8BufRest)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget RustLayoutOk)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (identityKeyPairTryFromPlacedSpec identityKeyPairTryFromRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (dealloc_keepsFs_lscro_of_fs subroutine_ok_withFdsGe3Closed_of_keepsFs
   subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed extract_withFdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonBudget
  (dirGetRoCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudget
  (dirGetRawSpec dirGetRoFsCellsSpec ikpTryFromCellsPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirGetSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.CalleesBudget (deallocVecBufSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

section Placed

theorem extract_withFdsGe3Closed_post {α : Type} {spec : Spec α} {x : α}
    {s0 sf : State} {R : SepProp}
    (hq : sf.mem ⊨ (withFdsGe3Closed spec).post x s0 sf ∗ R) :
    FdsGe3Closed sf.fs ∧ sf.mem ⊨ spec.post x s0 sf ∗ R := by
  change sf.mem ⊨ (⌜FdsGe3Closed sf.fs⌝ ∗ spec.post x s0 sf) ∗ R at hq
  rwa [sepConj_assoc, satisfies_pure_sepConj] at hq

/-! ## Read-Only `Dir::get` Cell Wrappers with `withFdsGe3Closed` (Block `589`) -/

/-- Two-sided `FdsGe3Closed` wrapper around `PollCommonPlacedBudget.dirGetRoFsCellsSpec`. -/
abbrev dirGetRoFsCellsSpec_fd {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DirGetRoCellsGhost × M.σ) :=
  withFdsGe3Closed (dirGetRoFsCellsSpec rd pathOk A lim GetEnv calleeStk)

theorem dirGetRo_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DirGetEnv : DirGetGhost → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withFdsGe3Closed
        (withLsCodeRoLoaded lsmpl (dirGetRawSpec rd pathOk A lim DirGetEnv getStk))))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed (dirGetRoCellsSpec M A lim DirGetEnv rd pathOk calleeStk))) := by
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨ret, self, dir, nameA, name, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  simp only [dirGetRoCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnl, hpl, hpok, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, true⟩
  have hif : (if true = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ᵣ name) := rfl
  have hpre0 : s0.mem ⊨
      (withFdsGe3Closed
        (withLsCodeRoLoaded lsmpl (dirGetRawSpec rd pathOk A lim DirGetEnv getStk))).pre
        (callG, st) s0 ∗ (stkRem ∗ R) := by
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, satisfies_lscro_pre hcrl ?_⟩
    dsimp only [dirGetRawSpec, bytesAt, callG, stkRem]
    rw [hif, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnl, hpl, hpok, hfit⟩, ?_⟩
    convert hmem using 1; sep_ac_rfl
  refine hGet.mono_outcome (callG, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfdsf, hq⟩ := extract_withFdsGe3Closed_post hq
    dsimp only [withLsCodeRoLoaded, withFdsGe3Closed, dirGetRawSpec, dirGetRoCellsSpec,
      bytesAt, callG] at hq ⊢
    rw [hif] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, r, hq⟩
    refine ⟨evs, r, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, dirGetRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, dirGetRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, dirGetRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem dirGetRo_cells_rocl_placed_ok_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DirGetEnv : DirGetGhost → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withFdsGe3Closed
        (withLsCodeRoLoaded lsmpl (dirGetRawSpec rd pathOk A lim DirGetEnv getStk))))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsRoCl lsmpl
        (withFdsGe3Closed (dirGetRoCellsSpec M A lim DirGetEnv rd pathOk calleeStk))) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (dirGetRo_cells_placed_ok_fd hGet hle hhi)

theorem dirGetRoFs_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (dirGetRoFsCellsSpec_fd rd pathOk A lim GetEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨ret, self, dir, nameA, name, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  simp only [dirGetRoFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnl, hpl, hpok, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, true⟩
  have hif : (if true = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ᵣ name) := rfl
  have hpre0 : s0.mem ⊨
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)).pre
        (callG, st) s0 ∗ (stkRem ∗ R) := by
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, ?_⟩
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [bytesAt, callG, stkRem]
    rw [hif, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnl, hpl, hpok, hfit⟩, ?_⟩
    convert hmem using 1; sep_ac_rfl
  refine hGet.mono_outcome (callG, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfdsf, hq⟩ := extract_withFdsGe3Closed_post hq
    dsimp only [withLsCodeRoLoaded, dirGetRoFsCellsSpec_fd, withFdsGe3Closed, dirGetSpecPlaced,
      dirGetRoFsCellsSpec, bytesAt, callG] at hq ⊢
    rw [hif] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, r, hq⟩
    refine ⟨evs, r, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem dirGetRoFs_cells_rocl_placed_ok_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsRoCl lsmpl
        (dirGetRoFsCellsSpec_fd rd pathOk A lim GetEnv calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (dirGetRoFs_cells_placed_ok_fd hGet hle hhi)

theorem dirGetRo_cells_placed_of_dirGetSpecPlaced_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DirGetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim (fun _ => DirGetEnv) getStk)))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (withFdsGe3Closed
          (dirGetRoCellsSpec M A lim (fun g => DirGetEnv g.dir g.name) rd pathOk calleeStk))) :=
  dirGetRoFs_cells_placed_ok_fd hGet hle hhi

/-! ## `Vec<u8>` Buffer Deallocation Cell Wrappers (`AllocContractsFsPlaced`) -/

theorem deallocAt_cells_keepsFs_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocVecBufSpec A lim calleeStk).keepsFs) := by
  have hDealloc := dealloc_keepsFs_lscro_of_fs (callerProg := prog) hC hi
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨bPtr, bCap, bs, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [Spec.keepsFs] at hpre
  simp only [deallocVecBufSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen, hlt, hnz, hlr⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  dsimp only [vecU8BufRest] at hmem
  simp only [hnz, ↓reduceIte] at hmem
  have hreg :
      (bPtr ↦ₛ bs) ∗ memRegion (bPtr + BitVec.ofNat 64 bs.length) (bCap.toNat - bs.length) ⊢
      memRegion bPtr bCap.toNat := by
    have hsplit : memRegion bPtr bCap.toNat =
        memRegion bPtr bs.length ∗
        memRegion (bPtr + BitVec.ofNat 64 bs.length) (bCap.toNat - bs.length) := by
      have heq : bCap.toNat = bs.length + (bCap.toNat - bs.length) := by omega
      conv_lhs => rw [heq]
      rw [memRegion_split bPtr bs.length (bCap.toNat - bs.length) (by omega)]
    rw [hsplit]
    exact sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsToBytes bPtr bs))
  have hlay : RustLayoutOk bCap.toNat 1 := ⟨⟨by bv_omega, ⟨0, rfl⟩, by omega⟩, by omega⟩
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hmem_reg : s0.mem ⊨
      memRegion bPtr bCap.toNat ∗
      (A.live bPtr bCap.toNat 1 ∗ A.pool lim st s0 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left hreg) ?_
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack M A lim extHookStack).keepsFs).pre
        (bPtr, bCap.toNat, 1, st) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetSpecWithStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, by rw [hx1], by rw [hx2]; rfl, hlay, hlr⟩, ?_⟩
    convert hmem_reg using 1; sep_ac_rfl
  refine hDealloc.mono_outcome (bPtr, bCap.toNat, 1, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetSpecWithStack,
      deallocVecBufSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨hfs, htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem deallocAt_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (deallocVecBufSpec A lim calleeStk))) := by
  have hk := deallocAt_cells_keepsFs_placed_ok (prog := prog) hC hi hle hhi
  have h1 : subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocVecBufSpec A lim calleeStk)).keepsFs :=
    subroutine_ok_mono hk (fun _ _ _ hp => hp) fun _ _ _ _ hq => by
      dsimp only [withLsCodeRoLoaded, Spec.keepsFs] at hq ⊢
      exact hq
  exact subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed
    (subroutine_ok_withFdsGe3Closed_of_keepsFs h1)

theorem deallocAt_cells_rocl_placed_ok_fd [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (withFdsGe3Closed (deallocVecBufSpec A lim calleeStk))) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (deallocAt_cells_placed_ok_fd hC hi hle hhi)

/-! ## `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` Cell Wrappers (Block `84`) -/

/-- Two-sided `FdsGe3Closed` wrapper around `PollCommonPlacedBudget.ikpTryFromCellsPlacedSpec`. -/
abbrev ikpTryFromCellsPlacedSpec_fd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (calleeStk : Nat) :
    Spec (IkpTryFromCellsGhost × M.σ) :=
  withFdsGe3Closed (ikpTryFromCellsPlacedSpec A lim calleeStk)

theorem ikpTryFrom_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 84)
      (withFdsGe3Closed (identityKeyPairTryFromPlacedSpec A lim)))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 84)
      (withLsCodeRoLoaded lsmpl (ikpTryFromCellsPlacedSpec_fd A lim calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨bytesA, bytes, ret, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  obtain ⟨hfds0, hpre⟩ := extract_withFdsGe3Closed hpre
  simp only [ikpTryFromCellsPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hblt, hx8, hfsp, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  let callG : DecodeGhost := ⟨bytesA, bytes, ret⟩
  have hlog : lsLogOff = CryptoVerification.LibsignalTripleRatchet.lsLogOff := rfl
  have hpre0 : s0.mem ⊨
      (withFdsGe3Closed (identityKeyPairTryFromPlacedSpec A lim)).pre
        (callG, st) s0 ∗ (stkRem ∗ R) := by
    change s0.mem ⊨
      (⌜FdsGe3Closed s0.fs⌝ ∗ (identityKeyPairTryFromPlacedSpec A lim).pre (callG, st) s0) ∗
        (stkRem ∗ R)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, ?_⟩
    unfold identityKeyPairTryFromPlacedSpec
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [identityKeyPairTryFromRawSpec, callG, stkRem]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hblt, hx8, hfit⟩, ?_⟩
    rw [hlog] at hmem
    convert hmem using 1; sep_ac_rfl
  refine hDec.mono_outcome (callG, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfdsf, hq⟩ := extract_withFdsGe3Closed_post hq
    dsimp only [identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded, ikpTryFromCellsPlacedSpec_fd,
      withFdsGe3Closed, identityKeyPairTryFromRawSpec, ikpTryFromCellsPlacedSpec, callG] at hq ⊢
    rw [← hlog] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfdsf, ?_⟩
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hevs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem ikpTryFrom_cells_rocl_placed_ok_fd [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 84)
      (withFdsGe3Closed (identityKeyPairTryFromPlacedSpec A lim)))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 84)
      (withLsRoCl lsmpl (ikpTryFromCellsPlacedSpec_fd A lim calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (ikpTryFrom_cells_placed_ok_fd hDec hle hhi)

theorem ikpTryFrom_cells_keepsFs_placed_ok [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 84)
      (identityKeyPairTryFromPlacedSpec A lim).keepsFs)
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 84)
      (withLsCodeRoLoaded lsmpl (ikpTryFromCellsPlacedSpec_fd A lim calleeStk)) :=
  ikpTryFrom_cells_placed_ok_fd (subroutine_ok_withFdsGe3Closed_of_keepsFs hDec) hle hhi

/-! ## Shared Block `567` (`IdKeyPairPoll`) Frame Layout Helpers -/

private def kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r; fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni => rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem utf8_eq_kutf8 (s : String) : utf8 s = kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, kutf8, List.utf8Encode, byteArray_toList_eq_data]

private theorem utf8_read_len_eq_placed : BitVec.ofNat 64 (utf8 "read").length = 4#64 := by
  rw [utf8_eq_kutf8]; decide

theorem cells_22_kp_placed (sp : BitVec 64) :
    cells (sp - 176#64) 22 =
      (∃∗ v0 : BitVec 64, (sp - 176#64) ↦₆₄ v0) ∗ memRegion (sp - 168#64) 72 ∗
      memRegion (sp - 96#64) 48 ∗ (∃∗ s29 : BitVec 64, (sp - 48#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 40#64) ↦₆₄ s30) ∗ (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗ (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  conv_lhs =>
    rw [show (22 : Nat) = 1 + 21 from rfl, ProofLib.cells_split_sub sp 176 168 1 21,
        show (21 : Nat) = 9 + 12 from rfl, ProofLib.cells_split_sub sp 168 96 9 12,
        show (12 : Nat) = 6 + 6 from rfl, ProofLib.cells_split_sub sp 96 48 6 6,
        show (6 : Nat) = 1 + 5 from rfl, ProofLib.cells_split_sub sp 48 40 1 5,
        show (5 : Nat) = 1 + 4 from rfl, ProofLib.cells_split_sub sp 40 32 1 4,
        show (4 : Nat) = 1 + 3 from rfl, ProofLib.cells_split_sub sp 32 24 1 3,
        show (3 : Nat) = 1 + 2 from rfl, ProofLib.cells_split_sub sp 24 16 1 2,
        show (2 : Nat) = 1 + 1 from rfl, ProofLib.cells_split_sub sp 16 8 1 1,
        ← ProofLib.memRegion_cells (sp - 168#64) 9 (by decide),
        ← ProofLib.memRegion_cells (sp - 96#64) 6 (by decide)]
  cells_unfold

theorem getResultAt_err_sp_96_placed (A : RustAlloc) (sp : BitVec 64) :
    getResultAt A (sp - 96#64) (.error ()) =
      ∃∗ fnPtr : BitVec 64, ∃∗ sBs : List (BitVec 8), ∃∗ sCap : BitVec 64, ∃∗ sPtr : BitVec 64,
        ((sp - 96#64) ↦₆₄ speWord 1) ∗ ((sp - 88#64) ↦₆₄ sCap) ∗ ((sp - 80#64) ↦₆₄ sPtr) ∗
        ((sp - 72#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗ vecU8Buf A sCap sPtr sBs ∗
        ((sp - 64#64) ↦₆₄ fnPtr) ∗ ((sp - 56#64) ↦₆₄ 4#64) ∗ (fnPtr ↦ᵣ utf8 "read") := by
  dsimp only [getResultAt, speAt, vecU8, strRefAt]
  simp_rw [vecU8At_eq_header_sep_buf]; dsimp only [vecHeader]; rw [utf8_read_len_eq_placed]
  have e8 : sp - 96#64 + 8#64 = sp - 88#64 := by bv_omega
  have e16 : sp - 88#64 + 8#64 = sp - 80#64 := by bv_omega
  have e24 : sp - 88#64 + 16#64 = sp - 72#64 := by bv_omega
  have e32 : sp - 96#64 + 32#64 = sp - 64#64 := by bv_omega
  have e40 : sp - 64#64 + 8#64 = sp - 56#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, e8, e16, e24, e32, e40]

theorem getResultAt_ok_sp_96_placed (A : RustAlloc) (sp : BitVec 64)
    (bs : List (BitVec 8)) :
    getResultAt A (sp - 96#64) (.ok bs) =
      ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
        ⌜bs.length ≤ bCap.toNat ∧ bCap.toNat < 2 ^ 63 ∧ bPtr ≠ 0#64⌝ ∗
        ((sp - 96#64) ↦₆₄ okTagVec) ∗ ((sp - 88#64) ↦₆₄ bCap) ∗ ((sp - 80#64) ↦₆₄ bPtr) ∗
        ((sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bPtr ↦ₛ bs) ∗ vecU8BufRest A bCap bPtr bs.length ∗ memRegion (sp - 64#64) 16 := by
  dsimp only [getResultAt, vecResultAt, vecU8]; simp_rw [vecU8At_eq_expose]
  have e8 : sp - 96#64 + 8#64 = sp - 88#64 := by bv_omega
  have e16 : sp - 88#64 + 8#64 = sp - 80#64 := by bv_omega
  have e24 : sp - 88#64 + 16#64 = sp - 72#64 := by bv_omega
  have e32 : sp - 96#64 + 32#64 = sp - 64#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, e8, e16, e24, e32]
  congr 1; funext bCap; congr 1; funext bPtr; sep_ac_rfl

theorem sp_96_cells4_fold_48_placed (sp : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗
      ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3) ∗ memRegion (sp - 64#64) 16 ⊢
    memRegion (sp - 96#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 40) (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 32) (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 24) (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16) (b' := sp - 64#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
        (sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _)))))

theorem sp_96_cells6_fold_48_placed (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗ ((sp - 80#64) ↦₆₄ w2) ∗
      ((sp - 72#64) ↦₆₄ w3) ∗ ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ⊢
    memRegion (sp - 96#64) 48 := by
  have h16 : ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ⊢ memRegion (sp - 64#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 8) (b' := sp - 56#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h16))))
    (sp_96_cells4_fold_48_placed sp w0 w1 w2 w3)

theorem sp_168_err_split_placed (sp : BitVec 64) :
    memRegion (sp - 168#64) 72 =
      (∃∗ b0 : BitVec 8, (sp - 168#64) ↦₈ b0) ∗ memRegion (sp - 167#64) 7 ∗
      (∃∗ u0 : BitVec 64, (sp - 160#64) ↦₆₄ u0) ∗ (∃∗ u1 : BitVec 64, (sp - 152#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (sp - 144#64) ↦₆₄ u2) ∗ (∃∗ u3 : BitVec 64, (sp - 136#64) ↦₆₄ u3) ∗
      (∃∗ u4 : BitVec 64, (sp - 128#64) ↦₆₄ u4) ∗ (∃∗ u5 : BitVec 64, (sp - 120#64) ↦₆₄ u5) ∗
      memRegion (sp - 112#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp - 168#64) (n := 1) (k := 71) (b' := sp - 167#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 167#64) (n := 7) (k := 64) (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 8) (k := 56) (b' := sp - 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 8) (k := 48) (b' := sp - 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 40) (b' := sp - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 8) (k := 32) (b' := sp - 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 24) (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 16) (b' := sp - 112#64) rfl (by bv_omega) (by decide),
      memRegion_one (sp - 168#64), ProofLib.memRegion_eight (sp - 160#64),
      ProofLib.memRegion_eight (sp - 152#64), ProofLib.memRegion_eight (sp - 144#64),
      ProofLib.memRegion_eight (sp - 136#64), ProofLib.memRegion_eight (sp - 128#64),
      ProofLib.memRegion_eight (sp - 120#64)]

theorem sp_168_err_fold_placed (A : RustAlloc) (sp sCap sPtr fnPtr : BitVec 64)
    (sBs : List (BitVec 8)) :
    ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
      ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
      ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
      vecU8Buf A sCap sPtr sBs ∗ ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
      (fnPtr ↦ᵣ utf8 "read") ∗ memRegion (sp - 112#64) 16 ⊢
    idKeyPairOutAt A (sp - 168#64) (.error ()) := by
  dsimp only [idKeyPairOutAt]
  have e1 : sp - 168#64 + 1#64 = sp - 167#64 := by bv_omega
  have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
  have e56 : sp - 168#64 + 0x38#64 = sp - 112#64 := by bv_omega
  rw [e1, e8, e56]
  have htop :
      ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
        ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
        ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        vecU8Buf A sCap sPtr sBs ∗ ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
        (fnPtr ↦ᵣ utf8 "read") ∗ memRegion (sp - 112#64) 16 =
      ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
        (((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
          ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
          vecU8Buf A sCap sPtr sBs ∗ ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
          (fnPtr ↦ᵣ utf8 "read")) ∗ memRegion (sp - 112#64) 16 := by sep_ac_rfl
  rw [htop]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono ?_ (Entails.refl _)))
  refine Entails.sepExists_right (.proto (utf8 "read") .invalidState) ?_
  dsimp only [speOwnedAt, speAt]
  have h40 : ((sp - 120#64) ↦₆₄ 4#64) =
      ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) := by
    rw [utf8_read_len_eq_placed]; congr 1; bv_omega
  have s8 : sp - 160#64 + 8#64 = sp - 152#64 := by bv_omega
  have s32 : sp - 160#64 + 32#64 = sp - 128#64 := by bv_omega
  rw [h40, s8, s32]
  have hvec :
      (((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
        ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗ vecU8Buf A sCap sPtr sBs ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A (sp - 152#64) bs := by
    have heq :
        (((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
          ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗ vecU8Buf A sCap sPtr sBs =
        vecU8At A (sp - 152#64) sCap sPtr sBs := by
      rw [vecU8At_eq_header_sep_buf]; dsimp only [vecHeader]
      have v8 : sp - 152#64 + 8#64 = sp - 144#64 := by bv_omega
      have v16 : sp - 152#64 + 16#64 = sp - 136#64 := by bv_omega
      rw [v8, v16]
    rw [heq]
    exact Entails.sepExists_right sBs
      (Entails.sepExists_right sCap (Entails.sepExists_right sPtr (Entails.refl _)))
  have hstr :
      ((sp - 128#64) ↦₆₄ fnPtr) ∗
        ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") ⊢ strRefAt (sp - 128#64) (utf8 "read") :=
    Entails.sepExists_right fnPtr (Entails.refl _)
  have hgrp :
      ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
        ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        vecU8Buf A sCap sPtr sBs ∗ ((sp - 128#64) ↦₆₄ fnPtr) ∗
        ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") =
      ((sp - 160#64) ↦₆₄ speWord 1) ∗
        ((((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
          ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗ vecU8Buf A sCap sPtr sBs) ∗
        (((sp - 128#64) ↦₆₄ fnPtr) ∗
          ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
          (fnPtr ↦ᵣ utf8 "read")) := by sep_ac_rfl
  refine Entails.trans (Entails.of_eq (by sep_ac_rfl)) (Entails.trans (Entails.of_eq hgrp) ?_)
  exact sepConj_mono_right (sepConj_mono hvec hstr)

theorem tryFrom_to_idKeyPairOutAt_placed (A : RustAlloc) (p : BitVec 64)
    (r : Except SignalProtocolError IdentityKeyPair) :
    identityKeyPairResultAt A p r ⊢
      idKeyPairOutAt A p (match r with | .ok kp => .ok kp | .error _ => .error ()) := by
  cases r with
  | ok kp => exact Entails.refl _
  | error e =>
    dsimp only [identityKeyPairResultAt, idKeyPairOutAt]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
    exact Entails.sepExists_right (.proto [] e) (Entails.refl _)

theorem memRegion_72_eq_cells9_placed (p : BitVec 64) :
    memRegion p 72 =
      (∃∗ w0 : BitVec 64, p ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (p + 16#64) ↦₆₄ w2) ∗ (∃∗ w3 : BitVec 64, (p + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (p + 32#64) ↦₆₄ w4) ∗ (∃∗ w5 : BitVec 64, (p + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (p + 48#64) ↦₆₄ w6) ∗ (∃∗ w7 : BitVec 64, (p + 56#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (p + 64#64) ↦₆₄ w8) := by
  rw [memRegion_split p 8 64 (by decide), memRegion_split (p + 8#64) 8 56 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc]; rfl

theorem kp72_words_sp168_placed (sp out : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 72) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64),
      ((sp - 168#64) ↦ₛ bs) =
        ((sp - 168#64) ↦₆₄ w0) ∗ ((sp - 160#64) ↦₆₄ w1) ∗ ((sp - 152#64) ↦₆₄ w2) ∗
        ((sp - 144#64) ↦₆₄ w3) ∗ ((sp - 136#64) ↦₆₄ w4) ∗ ((sp - 128#64) ↦₆₄ w5) ∗
        ((sp - 120#64) ↦₆₄ w6) ∗ ((sp - 112#64) ↦₆₄ w7) ∗ ((sp - 104#64) ↦₆₄ w8) ∧
      (out ↦ₛ bs) =
        (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗ ((out + 16#64) ↦₆₄ w2) ∗
        ((out + 24#64) ↦₆₄ w3) ∗ ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
        ((out + 48#64) ↦₆₄ w6) ∗ ((out + 56#64) ↦₆₄ w7) ∗ ((out + 64#64) ↦₆₄ w8) := by
  obtain ⟨q3, q0, q1, q2, w8, hforall⟩ := pointsToBytes72_split_qwords hlen
  refine ⟨q3.extractLsb' 0 64, q3.extractLsb' 64 64, q0.extractLsb' 0 64, q0.extractLsb' 64 64,
    q1.extractLsb' 0 64, q1.extractLsb' 64 64, q2.extractLsb' 0 64, q2.extractLsb' 64 64, w8, ?_, ?_⟩
  · rw [hforall (sp - 168#64)]; unfold Arm64.pointsTo128
    have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
    have e16 : sp - 168#64 + 16#64 = sp - 152#64 := by bv_omega
    have e24 : sp - 152#64 + 8#64 = sp - 144#64 := by bv_omega
    have e32 : sp - 168#64 + 32#64 = sp - 136#64 := by bv_omega
    have e40 : sp - 136#64 + 8#64 = sp - 128#64 := by bv_omega
    have e48 : sp - 168#64 + 48#64 = sp - 120#64 := by bv_omega
    have e56 : sp - 120#64 + 8#64 = sp - 112#64 := by bv_omega
    have e64 : sp - 168#64 + 64#64 = sp - 104#64 := by bv_omega
    rw [e16, e32, e48, e64, e8, e24, e40, e56]; sep_ac_rfl
  · rw [hforall out]; unfold Arm64.pointsTo128
    have o24 : out + 16#64 + 8#64 = out + 24#64 := by bv_omega
    have o40 : out + 32#64 + 8#64 = out + 40#64 := by bv_omega
    have o56 : out + 48#64 + 8#64 = out + 56#64 := by bv_omega
    rw [o24, o40, o56]; sep_ac_rfl

theorem kp72_words_fold_memRegion_placed (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64) :
    ((sp - 168#64) ↦₆₄ w0) ∗ ((sp - 160#64) ↦₆₄ w1) ∗ ((sp - 152#64) ↦₆₄ w2) ∗
      ((sp - 144#64) ↦₆₄ w3) ∗ ((sp - 136#64) ↦₆₄ w4) ∗ ((sp - 128#64) ↦₆₄ w5) ∗
      ((sp - 120#64) ↦₆₄ w6) ∗ ((sp - 112#64) ↦₆₄ w7) ∗ ((sp - 104#64) ↦₆₄ w8) ⊢
    memRegion (sp - 168#64) 72 := by
  rw [memRegion_72_eq_cells9_placed (sp - 168#64)]
  have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
  have e16 : sp - 168#64 + 16#64 = sp - 152#64 := by bv_omega
  have e24 : sp - 168#64 + 24#64 = sp - 144#64 := by bv_omega
  have e32 : sp - 168#64 + 32#64 = sp - 136#64 := by bv_omega
  have e40 : sp - 168#64 + 40#64 = sp - 128#64 := by bv_omega
  have e48 : sp - 168#64 + 48#64 = sp - 120#64 := by bv_omega
  have e56 : sp - 168#64 + 56#64 = sp - 112#64 := by bv_omega
  have e64 : sp - 168#64 + 64#64 = sp - 104#64 := by bv_omega
  rw [e8, e16, e24, e32, e40, e48, e56, e64]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right w3 (Entails.refl _))
          (sepConj_mono (Entails.sepExists_right w4 (Entails.refl _))
            (sepConj_mono (Entails.sepExists_right w5 (Entails.refl _))
              (sepConj_mono (Entails.sepExists_right w6 (Entails.refl _))
                (sepConj_mono (Entails.sepExists_right w7 (Entails.refl _))
                  (Entails.sepExists_right w8 (Entails.refl _)))))))))

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudgetFd
