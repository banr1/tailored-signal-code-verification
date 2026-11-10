/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymB
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.Sym
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable `<SessionFiles as SessionStore>::store_session::{closure#0}`

Proves `sessStorePollSpecPlaced` on Block `570` (`lsProg_570 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.StorePoll

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoGames.LibsignalSessionApi
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers.CliStorePollNorm

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre extractLsb_append_lo extractLsb_append_hi

private theorem close_panic_subgoal_placed {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

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
  ac_rfl

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

theorem addrText_cells_placed_ok [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {addrStk calleeStk : Nat}
    (hAddr : subroutine_ok prog entry (addrTextSpecPlaced A addrStk))
    (hle : addrStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (addrTextCellsSpec A calleeStk)) := by
  intro ⟨addrA, g, ret, o0, o1, o2, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [addrTextCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hfsp, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - addrStk)
  let callG : AddrTextGhost := ⟨addrA, g, ret⟩
  have hpre0 : s0.mem ⊨ (addrTextSpecPlaced A addrStk).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold addrTextSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hAddr callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, addrTextSpecPlaced, addrTextCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, addrTextSpecPlaced, addrTextCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [addrTextSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem serialize_cells_placed_ok [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {calleeStk : Nat}
    (hSer : subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (E2E.Record.Serialization.serializeCanonSpec A)))
    (hle : E2E.Record.Serialization.serializeStack ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (serializeCellsSpec A calleeStk)) := by
  intro ⟨recA, out, g, r, o0, o1, o2, o3, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [serializeCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hcanon, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk)
    (calleeStk - E2E.Record.Serialization.serializeStack)
  let callG : E2E.Record.Serialization.SerializeGhost := ⟨recA, out, g, r⟩
  have hpre0 : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (E2E.Record.Serialization.serializeCanonSpec A)).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [E2E.Record.Serialization.serializeCanonSpec, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hcanon, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hSer callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, E2E.Record.Serialization.serializeCanonSpec,
      serializeCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨bCap, bPtr, hq⟩
    refine ⟨bCap, bPtr, ?_⟩
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, E2E.Record.Serialization.serializeCanonSpec,
      E2E.Record.Serialization.allocPanic, serializeCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem vecU8_intro_placed (A : RustAlloc) (v bCap bPtr : BitVec 64)
    (bs : List (BitVec 8)) :
    ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr bs ⊢ vecU8 A v bs := by
  have heq :
      ((v ↦₆₄ bCap) ∗ ((v + 8#64) ↦₆₄ bPtr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A bCap bPtr bs =
      vecU8At A v bCap bPtr bs := by
    rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
    rfl
  rw [heq]
  exact Entails.sepExists_right bCap (Entails.sepExists_right bPtr (Entails.refl _))

theorem dirPut_cells_placed_ok [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {putStk calleeStk : Nat}
    (hPut : subroutine_ok prog entry (dirPutSpecPlaced A putStk))
    (hle : putStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (dirPutCellsSpec A calleeStk)) := by
  intro ⟨self, dir, nameV, name, bytesV, bCap, bPtr, bytes, fsp⟩ R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [dirPutCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hlen⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - putStk)
  let callG : DirPutGhost := ⟨self, dir, nameV, name, bytesV, bytes⟩
  have hmem_vec : s0.mem ⊨ vecU8 A bytesV bytes ∗
      (dirAt A self dir ∗ vecU8 A nameV name ∗ stackAt s0.sp putStk ∗ A.pool ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left (vecU8_intro_placed A bytesV bCap bPtr bytes)) ?_
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  have hpre0 : s0.mem ⊨ (dirPutSpecPlaced A putStk).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold dirPutSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    convert hmem_vec using 1; ac_rfl
  rcases hPut callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dirPutSpecPlaced, dirPutCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hq ⊢
    rcases hq with ⟨m2, m1, m0, n2, n1, n0, hq⟩
    refine ⟨n0, n1, n2, m0, m1, m2, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, dirPutSpecPlaced, dirPutCellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [dirPutSpecPlaced, StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessStorePollInner_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {calleeStk : Nat}
    (hAddrCells : subroutine_ok (lsProg_570 H) (lsmpl.base 594)
      (StoreKit.withLsCodeRoLoaded lsmpl (addrTextCellsSpec A calleeStk)))
    (hSerCells : subroutine_ok (lsProg_570 H) (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl (serializeCellsSpec A calleeStk)))
    (hPutCells : subroutine_ok (lsProg_570 H) (lsmpl.base 542)
      (StoreKit.withLsCodeRoLoaded lsmpl (dirPutCellsSpec A calleeStk))) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (StoreKit.withLsCodeRoLoaded lsmpl (cliStorePollInnerSpec A calleeStk)) := by
  unfold StoreKit.withLsCodeRoLoaded
  simp (config := { maxSteps := 2000000 }) only [cliStorePollInnerSpec,
    memRegion_48_cells, memRegion_40_cells,
    cells_26_split_placed, cells_sub_4_eq_placed, cells_sub_5_eq_placed,
    cells_sub_6_200_eq_placed, cells_sub_6_48_eq_placed,
    sepExists_sepConj_left, sepExists_sepConj_right]
  change subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (blkPl_570).base _
  wpp_init x s0
  have hcrl0 : StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 594) hcrl0
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 594)
      (StoreKit.withLsCodeRoLoaded lsmpl (addrTextCellsSpec A calleeStk)) from hAddrCells) hcrl1
    (x.call.call.addrA, x.call.call.addr, s0.sp - 200#64, _, _, _, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 52) hcrl_sf
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl2
  wp_call_lscro (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl (serializeCellsSpec A calleeStk)) from hSerCells) hcrl2
    (x.call.call.recA, s0.sp - 144#64,
      E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g, x.call.call.record,
      _, _, _, _, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 542) hcrl_sf_1
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl3
  wp_call_lscro (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 542)
      (StoreKit.withLsCodeRoLoaded lsmpl (dirPutCellsSpec A calleeStk)) from hPutCells) hcrl3
    (x.self, x.dir, s0.sp - 200#64, addressText x.call.call.addr.val,
      s0.sp - 176#64, w, w_1, E2E.Record.encodeRecord x.call.call.record, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_subgoal_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

theorem sessStorePoll_placed_of_inner [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (StoreKit.withLsCodeRoLoaded lsmpl (cliStorePollInnerSpec A calleeStk)))
    (hstk : 0xd0 + calleeStk ≤ stk) :
    subroutine_ok prog entry (sessStorePollSpecPlaced A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [sessStorePollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, henc, hdir⟩, hmem⟩
  dsimp only [sessStoreBoxAt] at hmem
  have hcanon : E2E.Record.Serialization.CanonRecord
      (E2E.InMem.SessionStoreImpl.toRecordGhost x.call.call.g) x.call.call.record := by
    refine canonRecord_of_satisfies_sessionRecordAt A x.call.call.recA
      x.call.call.g x.call.call.record
      ((x.call.fut ↦₆₄ x.self) ∗ ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        memRegion (x.call.fut + 25#64) 7 ∗
        dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        A.pool ∗ stackAt s0.sp stk ∗ R) s0.mem ?_
    convert hmem using 1; ac_rfl
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.call.fut) (v := x.self)
      (R := ((x.call.fut + 8#64) ↦₆₄ x.call.call.addrA) ∗
        ((x.call.fut + 16#64) ↦₆₄ x.call.call.recA) ∗ ((x.call.fut + 24#64) ↦₈ 0#8) ∗
        memRegion (x.call.fut + 25#64) 7 ∗
        dirAt A x.self x.dir ∗ memRegion x.call.out 48 ∗
        protocolAddressAt A x.call.call.addr x.call.call.addrA ∗
        sessionRecordAt A x.call.call.recA x.call.call.g x.call.call.record ∗
        A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 208 ≤ 2 ^ 64 := by omega
  rw [← E2E.InMem.SessionStoreImpl.record_sessionRecordAt_eq] at hmem
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
    stackAt_storePoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.call.fut + 25#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 208))
  have hpre_in : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (cliStorePollInnerSpec A calleeStk)).pre x s0 ∗
        (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [cliStorePollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc, hdir, hcanon⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  rcases hInner hcal_hi x (F_extra ∗ R) s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliStorePollInnerSpec, sessStorePollSpecPlaced,
      sessStoreBoxAt] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [E2E.InMem.SessionStoreImpl.record_sessionRecordAt_eq] at hq
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
      stackAt_storePoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliStorePollInnerSpec, sessStorePollSpecPlaced] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- Block `570` (`store_session::{closure#0}`) meets `sessStorePollSpecPlaced A stk`
given `address_text`, `SessionRecord::serialize`, and `Dir::put::<String>`. -/
theorem sessStorePoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (_hC : AllocContractsXCliPlaced A H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl (E2E.Record.Serialization.serializeCanonSpec A)))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hstk : 0xd0 + max (max addrStk E2E.Record.Serialization.serializeStack)
      (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570) (sessStorePollSpecPlaced A stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_570 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hSer' := ls_transfer_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_570 H) hPut (by decide) hPutBlk hPutUnmut
  refine sessStorePoll_placed_of_inner (fun hhi => ?_) hstk
  exact sessStorePollInner_placed_ok
    (addrText_cells_placed_ok hAddr' (by omega) hhi)
    (serialize_cells_placed_ok hSer' (by omega) hhi)
    (dirPut_cells_placed_ok hPut' (by omega) hhi)

end Placed

end CryptoVerification.SignalSession.Cli.Store.StorePoll
