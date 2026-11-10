/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Budget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable CLI `<SessionFiles as SessionStore>::store_session` on `Prev1`

Budget-threaded `[LibsignalPlacement]` `Prev1` `store_session` specifications and proofs on
Block `570` (`lsProg_570 H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1PlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (vecHeader vecU8)
open CryptoVerification.LibsignalPublicApiRepr (sessionStateReprAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost okTagVec protocolAddressAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.E2E.Record.Serialization (CanonSession)
open CryptoVerification.SpqrV1.Alloc (vecU8At_eq_header_sep_buf)
open CryptoVerification.SignalSession.Cli
  (DirGhost addressText dirAt sessStoreBoxAt)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_570 blkPl_570 lsProg_570)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_cl_to_lscro ls_transfer_lscro satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
  (memRegion_32_cells memRegion_40_cells memRegion_48_cells memRegion_bound_of_pointsTo64
   stackAt_storePoll_frame stackAt_sub_split storePollSlack)
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers.CliStorePollNorm
  (extractLsb_append_hi extractLsb_append_lo readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   readVReg128_setMem_pre readVReg128_setMem_setPC_pre readVReg128_setPC_pre
   readVReg128_setPState_pre readVReg128_writeReg64_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
  (SerializePrev1BodyGhost encodeRecordPrev1 encodeRecordPrev1Mem
   encodeRecordPrev1Mem_eq_of_canon prevVecAt sessionRecordPrevAt sessionRecordPrevAt_some_eq)
open CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1
  (SerPrev1CellsGhost SessStorePollPrev1Ghost)
open Proofs.libsignal.Hooks2 (serializeStackX)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (addrTextSpecPlaced dirPutSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
  (addrTextCellsSpec dirPutCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget
  (addrText_cells_placed_ok dirPut_cells_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Budget
  (CliStorePollPrev1Env cliStorePollPrev1InnerSpec serializePrev1CellsSpec)

section Placed

attribute [local irreducible] Program.fetch Program.externAt? FitsEnv
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre extractLsb_append_lo extractLsb_append_hi

/-! ## 1. Budget-Threaded Relocatable `[LibsignalPlacement]` `Prev1` Store Specifications -/

/-- Budget-threaded `SessionRecord::serialize` on a record with a current session and
`previous_sessions = [enc]`, at `serializeStackX` and a 32-byte `out`, parameterized by
`SerPrev1Env`. -/
def serializePrev1BodySpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop) : Spec (SerializePrev1BodyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
      FitsEnv M lim st (SerPrev1Env x.G x.sess x.enc)⌝ ∗
      prevVecAt A.repAlloc x.self x.prevCap x.prevPtr [x.enc] ∗
      sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
      memRegion x.out 32 ∗ A.pool lim st s ∗ stackAt s.sp serializeStackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ SerPrev1Env x.G x.sess x.enc evs⌝ ∗
        prevVecAt A.repAlloc x.self x.prevCap x.prevPtr [x.enc] ∗
        sessionStateReprAt A.repAlloc (x.self + 24#64) x.G x.sess ∗
        (x.out ↦₆₄ okTagVec) ∗
        vecU8 A.repAlloc (x.out + 8#64) (encodeRecordPrev1Mem x.G x.sess x.enc) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp serializeStackX

def sessStorePollPrev1MemSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (StorePrev1Env : SessStorePollPrev1Ghost → List AllocEvent → Prop)
    (stk : Nat) : Spec (SessStorePollPrev1Ghost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.addr.name.bytes.length < 2 ^ 32 ∧
          (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
          x.dir.changed.length < 2 ^ 32 ∧
          FitsEnv M lim st (StorePrev1Env x)⌝ ∗
          sessStoreBoxAt x.fut x.self x.addrA x.recA 0#8 ∗
          dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 48 ∗
          protocolAddressAt A.repAlloc x.addr x.addrA ∗
          prevVecAt A.repAlloc x.recA x.prevCap x.prevPtr [x.enc] ∗
          sessionStateReprAt A.repAlloc (x.recA + 24#64) x.G x.sess ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ StorePrev1Env x evs⌝ ∗
            sessStoreBoxAt x.fut x.self x.addrA x.recA 1#8 ∗
            dirAt A.repAlloc x.self
              (x.dir.put (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc)) ∗
            (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
            protocolAddressAt A.repAlloc x.addr x.addrA ∗
            prevVecAt A.repAlloc x.recA x.prevCap x.prevPtr [x.enc] ∗
            sessionStateReprAt A.repAlloc (x.recA + 24#64) x.G x.sess ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

def sessStorePollPrev1SpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (StorePrev1Env : SessStorePollPrev1Ghost → List AllocEvent → Prop)
    (stk : Nat) : Spec (SessStorePollPrev1Ghost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.addr.name.bytes.length < 2 ^ 32 ∧
          CanonSession x.G x.sess ∧
          (encodeRecordPrev1 x.sess x.enc).length < 2 ^ 32 ∧
          x.dir.changed.length < 2 ^ 32 ∧
          FitsEnv M lim st (StorePrev1Env x)⌝ ∗
          sessStoreBoxAt x.fut x.self x.addrA x.recA 0#8 ∗
          dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 48 ∗
          protocolAddressAt A.repAlloc x.addr x.addrA ∗
          sessionRecordPrevAt A.repAlloc x.recA
            ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
          A.pool lim st s ∗ stackAt s.sp stk
      post := fun (x, st) s0 sf =>
        ∃∗ evs : List AllocEvent,
          ⌜sf.trace = s0.trace ∧ StorePrev1Env x evs⌝ ∗
            sessStoreBoxAt x.fut x.self x.addrA x.recA 1#8 ∗
            dirAt A.repAlloc x.self
              (x.dir.put (addressText x.addr.val) (encodeRecordPrev1 x.sess x.enc)) ∗
            (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
            protocolAddressAt A.repAlloc x.addr x.addrA ∗
            sessionRecordPrevAt A.repAlloc x.recA
              ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
            A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk }

/-! ## 2. Cell-Unpacked `serializePrev1BodySpecX` & Poll Symbolic Execution -/

theorem serializePrev1_cells_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {calleeStk : Nat}
    (hSer : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A lim SerPrev1Env)))
    (hle : serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (serializePrev1CellsSpec A lim SerPrev1Env calleeStk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨g, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  simp only [serializePrev1CellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hlen, hfit⟩, hmem⟩
  rw [← hfsp] at hmem
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - serializeStackX)
  let callG : SerializePrev1BodyGhost × M.σ :=
    (⟨g.recA, g.out, g.prevCap, g.prevPtr, g.G, g.sess, g.enc⟩, st)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A lim SerPrev1Env)).pre callG s0 ∗
        (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [serializePrev1BodySpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨g.o3, g.o2, g.o1, g.o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hlen, hfit⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  refine hSer.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, serializePrev1BodySpecX, serializePrev1CellsSpec,
      callG] at hq ⊢
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
    rw [← hfsp, stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, serializePrev1BodySpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializePrev1BodySpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, serializePrev1BodySpecX] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem cells_26_split_prev1_placed (sp : BitVec 64) :
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

private theorem cells_sub_4_eq_prev1_placed (sp : BitVec 64) :
    cells (sp - 144#64) 4 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗
        ((sp - 128#64) ↦₆₄ v2) ∗ ((sp - 120#64) ↦₆₄ v3) := by
  cells_unfold

private theorem cells_sub_5_eq_prev1_placed (sp : BitVec 64) :
    cells (sp - 96#64) 5 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗ ((sp - 80#64) ↦₆₄ v2) ∗
        ((sp - 72#64) ↦₆₄ v3) ∗ ((sp - 64#64) ↦₆₄ v4) := by
  cells_unfold

private theorem cells_sub_6_200_eq_prev1_placed (sp : BitVec 64) :
    cells (sp - 200#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 200#64) ↦₆₄ v0) ∗ ((sp - 192#64) ↦₆₄ v1) ∗ ((sp - 184#64) ↦₆₄ v2) ∗
        ((sp - 176#64) ↦₆₄ v3) ∗ ((sp - 168#64) ↦₆₄ v4) ∗ ((sp - 160#64) ↦₆₄ v5) := by
  cells_unfold

private theorem cells_sub_6_48_eq_prev1_placed (sp : BitVec 64) :
    cells (sp - 48#64) 6 =
      ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
      ∃∗ v3 : BitVec 64, ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v0) ∗ ((sp - 40#64) ↦₆₄ v1) ∗ ((sp - 32#64) ↦₆₄ v2) ∗
        ((sp - 24#64) ↦₆₄ v3) ∗ ((sp - 16#64) ↦₆₄ v4) ∗ ((sp - 8#64) ↦₆₄ v5) := by
  cells_unfold

theorem sessStorePollPrev1Inner_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {calleeStk : Nat}
    (hAddrCells : subroutine_ok (lsProg_570 H) (lsmpl.base 594)
      (withLsCodeRoLoaded lsmpl (addrTextCellsSpec A lim AddrEnv calleeStk)))
    (hSerCells : subroutine_ok (lsProg_570 H) (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CellsSpec A lim SerPrev1Env calleeStk)))
    (hPutCells : subroutine_ok (lsProg_570 H) (lsmpl.base 542)
      (withLsCodeRoLoaded lsmpl (dirPutCellsSpec A lim PutEnv calleeStk))) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (cliStorePollPrev1InnerSpec A lim AddrEnv SerPrev1Env PutEnv calleeStk)) := by
  unfold withLsCodeRoLoaded
  simp (config := { maxSteps := 2000000 }) only [cliStorePollPrev1InnerSpec,
    memRegion_48_cells, memRegion_40_cells,
    cells_26_split_prev1_placed, cells_sub_4_eq_prev1_placed, cells_sub_5_eq_prev1_placed,
    cells_sub_6_200_eq_prev1_placed, cells_sub_6_48_eq_prev1_placed,
    sepExists_sepConj_left, sepExists_sepConj_right]
  change subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (blkPl_570).base _
  wp_init xs s0
  obtain ⟨x, st⟩ := xs
  dsimp only
  have hcrl0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hfit0 : FitsEnv M lim st (CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv x) := by
    assumption
  have hfit_addr : FitsEnv M lim st (AddrEnv x.addr) := hfit0.seq_left
  apply sepWP_seq_lscro (mid := lsmpl.base 594) hcrl0
  wp_steps_sync_pool (lsmpl.base 594)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro
    (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 594)
      (withLsCodeRoLoaded lsmpl (addrTextCellsSpec A lim AddrEnv calleeStk)) from hAddrCells)
    hcrl1
    ((x.addrA, x.addr, s0.sp - 200#64, _, _, _, s0.sp - 208#64), st)
  have hfit_rest : FitsEnv M lim (M.stepEvents w st)
      (SeqEnv (SerPrev1Env x.G x.sess x.enc)
        (PutEnv x.dir (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc))) :=
    hfit0.seq_right (by assumption)
  have hfit_ser : FitsEnv M lim (M.stepEvents w st) (SerPrev1Env x.G x.sess x.enc) :=
    hfit_rest.seq_left
  apply sepWP_seq_lscro (mid := lsmpl.base 52) hcrl_sf
  wp_steps_sync_pool (lsmpl.base 52)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl2
  wp_call_lscro
    (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1CellsSpec A lim SerPrev1Env calleeStk))
      from hSerCells)
    hcrl2
    (⟨x.recA, s0.sp - 144#64, x.prevCap, x.prevPtr, x.G, x.sess, x.enc,
      _, _, _, _, s0.sp - 208#64⟩, M.stepEvents w st)
  have hfit_put : FitsEnv M lim (M.stepEvents w_1 (M.stepEvents w st))
      (PutEnv x.dir (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc)) :=
    hfit_rest.seq_right (by assumption)
  apply sepWP_seq_lscro (mid := lsmpl.base 542) hcrl_sf_1
  wp_steps_sync_pool (lsmpl.base 542)
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl3
  wp_call_lscro
    (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 542)
      (withLsCodeRoLoaded lsmpl (dirPutCellsSpec A lim PutEnv calleeStk)) from hPutCells)
    hcrl3
    ((x.self, x.dir, s0.sp - 200#64, addressText x.addr.val,
      s0.sp - 176#64, w_2, w_3, encodeRecordPrev1Mem x.G x.sess x.enc, s0.sp - 208#64),
      M.stepEvents w_1 (M.stepEvents w st))
  have hcli_evs : CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv x (w ++ (w_1 ++ w_4)) :=
    SeqEnv.append (by assumption) (SeqEnv.append (by assumption) (by assumption))
  rw [← M.stepEvents_append, ← M.stepEvents_append]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

/-! ## 3. Top-Level Relocatable Hop Theorems (`sessStorePollPrev1{Mem,}SpecPlaced`) -/

theorem sessStorePollPrev1Mem_placed_of_inner [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (withLsCodeRoLoaded lsmpl
          (cliStorePollPrev1InnerSpec A lim AddrEnv SerPrev1Env PutEnv calleeStk)))
    (hstk : 0xd0 + calleeStk ≤ stk) :
    subroutine_ok prog entry
      (sessStorePollPrev1MemSpecPlaced A lim
        (CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv) stk) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessStorePollPrev1MemSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, henc, hdir, hfit⟩, hmem⟩
  dsimp only [sessStoreBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₆₄ x.addrA) ∗ ((x.fut + 16#64) ↦₆₄ x.recA) ∗
        ((x.fut + 24#64) ↦₈ 0#8) ∗ memRegion (x.fut + 25#64) 7 ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 48 ∗
        protocolAddressAt A.repAlloc x.addr x.addrA ∗
        prevVecAt A.repAlloc x.recA x.prevCap x.prevPtr [x.enc] ∗
        sessionStateReprAt A.repAlloc (x.recA + 24#64) x.G x.sess ∗
        A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 208 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
    stackAt_storePoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 25#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 208))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliStorePollPrev1InnerSpec A lim AddrEnv SerPrev1Env PutEnv calleeStk)).pre (x, st) s0 ∗
        (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [cliStorePollPrev1InnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc, hdir, hfit⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; sep_ac_rfl
  refine (hInner hcal_hi).mono_outcome (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, cliStorePollPrev1InnerSpec,
      sessStorePollPrev1MemSpecPlaced, sessStoreBoxAt] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    refine ⟨⟨htr, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
      stackAt_storePoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, cliStorePollPrev1InnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliStorePollPrev1InnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, cliStorePollPrev1InnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessStorePollPrev1Mem_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A lim SerPrev1Env)))
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
      (sessStorePollPrev1MemSpecPlaced A lim
        (CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv) stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_570 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hSer' := ls_transfer_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_570 H) hPut (by decide) hPutBlk hPutUnmut
  refine sessStorePollPrev1Mem_placed_of_inner (fun hhi => ?_) hstk
  exact sessStorePollPrev1Inner_placed_ok
    (addrText_cells_placed_ok hAddr' (by omega) hhi)
    (serializePrev1_cells_placed_ok hSer' (by omega) hhi)
    (dirPut_cells_placed_ok hPut' (by omega) hhi)

theorem sessStorePollPrev1Mem_placed_ok_of_deps_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1BodySpecX A lim SerPrev1Env)))
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
      (sessStorePollPrev1MemSpecPlaced A lim
        (CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv) stk) :=
  sessStorePollPrev1Mem_placed_ok_of_deps hAddr
    (ls_transfer_cl_to_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut)
    hPut hstk hAddrBlk hAddrUnmut (by decide) (by decide) hPutBlk hPutUnmut

theorem sessStorePollPrev1_placed_of_mem [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {StorePrev1Env : SessStorePollPrev1Ghost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {stk : Nat}
    (hMem : subroutine_ok prog entry
      (sessStorePollPrev1MemSpecPlaced A lim StorePrev1Env stk)) :
    subroutine_ok prog entry
      (sessStorePollPrev1SpecPlaced A lim StorePrev1Env stk) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  obtain ⟨hcrl, hpre'⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [sessStorePollPrev1SpecPlaced] at hpre'
  rw [sessionRecordPrevAt_some_eq A.repAlloc x.recA x.prevCap x.prevPtr x.G x.sess [x.enc],
    sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hname, hcanon, hlen, hdir, hfit⟩, hmem⟩
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon
  have hpre_mem : s0.mem ⊨
      (sessStorePollPrev1MemSpecPlaced A lim StorePrev1Env stk).pre (x, st) s0 ∗ R := by
    unfold sessStorePollPrev1MemSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc.symm ▸ hlen, hdir, hfit⟩, ?_⟩
    convert hmem using 1; sep_ac_rfl
  refine hMem.mono_outcome (x, st) R s0 hpc hrun hpre_mem hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessStorePollPrev1MemSpecPlaced, sessStorePollPrev1SpecPlaced,
      withLsCodeRoLoaded] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    rw [henc] at hq
    rw [sessionRecordPrevAt_some_eq A.repAlloc x.recA x.prevCap x.prevPtr x.G x.sess [x.enc]]
    refine ⟨⟨htr, hevs⟩, ?_⟩
    convert hq using 1; sep_ac_rfl
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem sessStorePollPrev1_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A lim SerPrev1Env)))
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
      (sessStorePollPrev1SpecPlaced A lim
        (CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv) stk) :=
  sessStorePollPrev1_placed_of_mem
    (sessStorePollPrev1Mem_placed_ok_of_deps hAddr hSer hPut hstk
      hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut)

theorem sessStorePollPrev1_placed_ok_of_deps_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {SerPrev1Env : SessionGhost → Session (List (BitVec 8)) → List (BitVec 8) →
      List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializePrev1BodySpecX A lim SerPrev1Env)))
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
      (sessStorePollPrev1SpecPlaced A lim
        (CliStorePollPrev1Env AddrEnv SerPrev1Env PutEnv) stk) :=
  sessStorePollPrev1_placed_of_mem
    (sessStorePollPrev1Mem_placed_ok_of_deps_cl hAddr hSer hPut hstk
      hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut)

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1PlacedBudget
