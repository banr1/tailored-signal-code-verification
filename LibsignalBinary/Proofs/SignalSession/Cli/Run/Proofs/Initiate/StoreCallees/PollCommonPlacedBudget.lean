/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Store Poll Helpers (`[LibsignalPlacement]`)

Budget-threaded cell-oriented wrappers for `Dir::get` (Block `589`), `__rust_dealloc`, and
`<IdentityKeyPair as TryFrom<&[u8]>>::try_from` (Block `84`) under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles extract_withLsCodeRoLoaded subroutine_ok_rocl_of_withLsCodeRoLoaded
   withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.RecordCodecsBinary (DecodeGhost identityKeyPairResultAt)
open CryptoVerification.SignalSession (CliHooks lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (DirGetGhost DirGhost ReadRule dirAt getResultAt pathOf)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.PollCommon
  (DirGetRoCellsGhost IkpTryFromCellsGhost)
open CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
  (DeallocVecBufGhost stackAt_sub_split vecU8BufRest)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk
   rustDeallocEvents)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (IdentityKeyPairTryFromEnv RecordCodecLoopEnv identityKeyPairTryFromPlacedSpec
   identityKeyPairTryFromRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonBudget
  (dirGetRoCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced dirGetSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.CalleesBudget (deallocVecBufSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)

section Placed

/-! ## Read-Only `Dir::get` Cell Wrappers (Block `589`) -/

/-- Image-free inner `Dir::get` specification parameterized by `DirGetEnv : DirGetGhost → ...`. -/
def dirGetRawSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DirGetEnv : DirGetGhost → List AllocEvent → Prop) (stk : Nat) :
    Spec (DirGetGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.self ∧ s.readReg64 .x2 = x.nameA ∧
      (s.readReg64 .x3).toNat = x.name.length ∧ x.name.length < 2 ^ 32 ∧
      x.dir.path.length < 2 ^ 32 ∧ pathOk (pathOf x.dir.path x.name) ∧
      FitsEnv M lim st (DirGetEnv x)⌝ ∗
      dirAt A.repAlloc x.self x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
      memRegion x.ret 48 ∗ stackAt s.sp stk ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      (∃∗ r : Except Unit (List (BitVec 8)),
        ⌜r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace ∧
          DirGetEnv x evs⌝ ∗
          getResultAt A.repAlloc x.ret r) ∗
        dirAt A.repAlloc x.self x.dir ∗ bytesAt x.nameRo x.nameA x.name ∗
        stackAt s0.sp stk ∗ A.pool lim (M.stepEvents evs st) sf

theorem dirGetRo_cells_placed_ok [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DirGetEnv : DirGetGhost → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl (dirGetRawSpec rd pathOk A lim DirGetEnv getStk)))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (dirGetRoCellsSpec M A lim DirGetEnv rd pathOk calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨ret, self, dir, nameA, name, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [dirGetRoCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnl, hpl, hpok, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, true⟩
  have hif : (if true = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ᵣ name) := rfl
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (dirGetRawSpec rd pathOk A lim DirGetEnv getStk)).pre
        (callG, st) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [dirGetRawSpec, bytesAt, callG, stkRem]
    rw [hif, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnl, hpl, hpok, hfit⟩, ?_⟩
    convert hmem using 1; sep_ac_rfl
  refine hGet.mono_outcome (callG, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, dirGetRawSpec, dirGetRoCellsSpec, bytesAt, callG] at hq ⊢
    rw [hif] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, r, hq⟩
    refine ⟨evs, r, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, dirGetRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, dirGetRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, dirGetRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem dirGetRo_cells_rocl_placed_ok [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DirGetEnv : DirGetGhost → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl (dirGetRawSpec rd pathOk A lim DirGetEnv getStk)))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsRoCl lsmpl
        (dirGetRoCellsSpec M A lim DirGetEnv rd pathOk calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (dirGetRo_cells_placed_ok hGet hle hhi)

/-- Read-only `Dir::get` cell wrapper specification directly matching
`SpecsPlacedBudget.dirGetSpecPlaced`'s `FsFiles`-indexed `GetEnv`. -/
def dirGetRoFsCellsSpec {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) : Spec (DirGetRoCellsGhost × M.σ) where
  pre := fun ((ret, self, dir, nameA, name, fsp), st) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nameA ∧
      (s.readReg64 .x3).toNat = name.length ∧ s.sp = fsp ∧
      name.length < 2 ^ 32 ∧ dir.path.length < 2 ^ 32 ∧ pathOk (pathOf dir.path name) ∧
      FitsEnv M lim st (GetEnv s.fs.files dir name)⌝ ∗
      dirAt A.repAlloc self dir ∗ (nameA ↦ᵣ name) ∗ memRegion ret 48 ∗
      stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((ret, self, dir, nameA, name, fsp), st) s0 sf =>
    (∃∗ evs : List AllocEvent, ∃∗ r : Except Unit (List (BitVec 8)),
      ⌜r = dir.get rd s0.fs.files name ∧ sf.trace = s0.trace ∧
        GetEnv s0.fs.files dir name evs⌝ ∗
        getResultAt A.repAlloc ret r ∗ A.pool lim (M.stepEvents evs st) sf) ∗
      dirAt A.repAlloc self dir ∗ (nameA ↦ᵣ name) ∗ stackAt fsp calleeStk

theorem dirGetRoFs_cells_placed_ok [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (dirGetRoFsCellsSpec rd pathOk A lim GetEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨ret, self, dir, nameA, name, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [dirGetRoFsCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hfsp, hnl, hpl, hpok, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let callG : DirGetGhost := ⟨ret, self, dir, nameA, name, true⟩
  have hif : (if true = true then (nameA ↦ᵣ name) else (nameA ↦ₛ name)) = (nameA ↦ᵣ name) := rfl
  have hpre0 : s0.mem ⊨
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk).pre (callG, st) s0 ∗ (stkRem ∗ R) := by
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [bytesAt, callG, stkRem]
    rw [hif, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hnl, hpl, hpok, hfit⟩, ?_⟩
    convert hmem using 1; sep_ac_rfl
  refine hGet.mono_outcome (callG, st) (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, dirGetSpecPlaced, dirGetRoFsCellsSpec,
      bytesAt, callG] at hq ⊢
    rw [hif] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, r, hq⟩
    refine ⟨evs, r, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem dirGetRoFs_cells_rocl_placed_ok [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsRoCl lsmpl
        (dirGetRoFsCellsSpec rd pathOk A lim GetEnv calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (dirGetRoFs_cells_placed_ok hGet hle hhi)

theorem dirGetRo_cells_placed_of_dirGetSpecPlaced [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DirGetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (fun _ => DirGetEnv) getStk))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (dirGetRoCellsSpec M A lim (fun g => DirGetEnv g.dir g.name) rd pathOk calleeStk)) :=
  dirGetRoFs_cells_placed_ok hGet hle hhi

/-! ## `Vec<u8>` Buffer Deallocation Cell Wrapper -/

theorem deallocAt_cells_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocVecBufSpec A lim calleeStk)) := by
  have hDealloc := dealloc_lscro_of_cli (callerProg := prog) hC hi
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨bPtr, bCap, bs, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
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
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)).pre
        (bPtr, bCap.toNat, 1, st) s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [rustDeallocExternSpecWithStack,
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
    dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetSpecWithStack,
      deallocVecBufSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem deallocAt_cells_rocl_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hi : i < 619 := by decide)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsRoCl lsmpl (deallocVecBufSpec A lim calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (deallocAt_cells_placed_ok hC hi hle hhi)

/-! ## `<IdentityKeyPair as TryFrom<&[u8]>>::try_from` Cell Wrapper (Block `84`) -/

def ikpTryFromCellsPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (calleeStk : Nat) :
    Spec (IkpTryFromCellsGhost × M.σ) where
  pre := fun ((bytesA, bytes, ret, fsp), st) s =>
    ⌜s.readReg64 .x0 = bytesA ∧ (s.readReg64 .x1).toNat = bytes.length ∧
      bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = ret ∧ s.sp = fsp ∧
      FitsEnv M lim st (RecordCodecLoopEnv (2 * bytes.length + 3) bytes.length)⌝ ∗
      (bytesA ↦ₛ bytes) ∗ memRegion ret 72 ∗ lsLogOff ∗
      stackAt fsp calleeStk ∗ A.pool lim st s
  post := fun ((bytesA, bytes, ret, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ IdentityKeyPairTryFromEnv bytes.length evs⌝ ∗
        identityKeyPairResultAt A.repAlloc ret (IdentityKeyPair.tryFrom bytes) ∗
        (bytesA ↦ₛ bytes) ∗ lsLogOff ∗ stackAt fsp calleeStk ∗
        A.pool lim (M.stepEvents evs st) sf

theorem ikpTryFrom_cells_placed_ok [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 84) (identityKeyPairTryFromPlacedSpec A lim))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 84)
      (withLsCodeRoLoaded lsmpl (ikpTryFromCellsPlacedSpec A lim calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun
    ⟨⟨bytesA, bytes, ret, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [ikpTryFromCellsPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hblt, hx8, hfsp, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  let callG : DecodeGhost := ⟨bytesA, bytes, ret⟩
  have hlog : lsLogOff = CryptoVerification.LibsignalTripleRatchet.lsLogOff := rfl
  have hpre0 : s0.mem ⊨
      (identityKeyPairTryFromPlacedSpec A lim).pre (callG, st) s0 ∗ (stkRem ∗ R) := by
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
    dsimp only [identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec, ikpTryFromCellsPlacedSpec, callG] at hq ⊢
    rw [← hlog] at hq
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
  · dsimp only [identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [identityKeyPairTryFromPlacedSpec, withLsCodeRoLoaded,
      identityKeyPairTryFromRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem ikpTryFrom_cells_rocl_placed_ok [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 84) (identityKeyPairTryFromPlacedSpec A lim))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 84)
      (withLsRoCl lsmpl (ikpTryFromCellsPlacedSpec A lim calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (ikpTryFrom_cells_placed_ok hDec hle hhi)

theorem ikpTryFrom_cells_cli_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {W : CliHooks} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hh : RunHooksPlaced W A lim H)
    (hi : i < 619 := by decide)
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 84)
      (withLsCodeRoLoaded lsmpl (ikpTryFromCellsPlacedSpec A lim calleeStk)) :=
  ikpTryFrom_cells_placed_ok
    (ls_transfer_lscro (callerProg := prog) (j := 84) hh.identityKeyPair_tryFrom_placed_ok hi)
    hle hhi

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlacedBudget
