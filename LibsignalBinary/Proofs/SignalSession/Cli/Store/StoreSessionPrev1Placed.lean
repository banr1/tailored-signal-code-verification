/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreShimPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable CLI `<SessionFiles as SessionStore>::store_session` on `Prev1`

Relocatable `[LibsignalPlacement]` `Prev1` `store_session` specifications, symbolic execution on
Block `570` (`lsProg_570 H`), and `TraceFsSound` filesystem preservation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.Store.StorePoll
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers
open CryptoVerification.SignalSession.Cli.Store.StorePoll.Helpers.CliStorePollNorm
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

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
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre
  readVReg128_setMem_pre readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi

/-! ## 1. `TraceFsSound` for `cliExternsPlaced mmpl W` and `[IsLsBlockProg]` -/

theorem cliHookTablePlaced_fsT (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ∀ p ∈ cliHookTablePlaced mmpl W, HookFsTraced RunGlue.IsFsC p.2 :=
  RunGlue.cliHookTablePlaced_fsT mmpl W

theorem fsTHooks_cliExternsPlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    RunGlue.FsTHooks (cliExternsPlaced mmpl W) :=
  RunGlue.fsTHooks_cliExternsPlaced mmpl W

theorem traceFsSound_of_blockProg [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] (hH : RunGlue.FsTHooks H) :
    TraceFsSound prog := by
  rw [IsLsBlockProg.eq_blockProgram (prog := prog) (i := i) (H := H)]
  exact RunGlue.traceFsSound_of_fsTHooks hH RunGlue.fsTHooks_none

theorem traceFsSound_cli_placed [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (cliExternsPlaced mmpl W)] :
    TraceFsSound prog :=
  traceFsSound_of_blockProg (fsTHooks_cliExternsPlaced mmpl W)

theorem traceFsSound_cliProgPlaced [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    TraceFsSound (cliProgPlaced mmpl W) :=
  RunGlue.traceFsSound_cliProgPlaced mmpl W

/-! ## 2. Relocatable `[LibsignalPlacement]` `Prev1` Store Specifications -/

def sessStorePollPrev1MemSpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec SessStorePollPrev1Ghost :=
  StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.addr.name.bytes.length < 2 ^ 32 ∧
          (encodeRecordPrev1Mem x.G x.sess x.enc).length < 2 ^ 32 ∧
          x.dir.changed.length < 2 ^ 32⌝ ∗
          sessStoreBoxAt x.fut x.self x.addrA x.recA 0#8 ∗
          dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
          protocolAddressAt A x.addr x.addrA ∗
          prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
          sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          sessStoreBoxAt x.fut x.self x.addrA x.recA 1#8 ∗
          dirAt A x.self
            (x.dir.put (addressText x.addr.val) (encodeRecordPrev1Mem x.G x.sess x.enc)) ∗
          (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
          protocolAddressAt A x.addr x.addrA ∗
          prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
          sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf =>
        ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

def sessStorePollPrev1SpecPlaced [LibsignalPlacement] (A : RustAlloc) (stk : Nat) :
    Spec SessStorePollPrev1Ghost :=
  StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
          x.addr.name.bytes.length < 2 ^ 32 ∧
          E2E.Record.Serialization.CanonSession x.G x.sess ∧
          (encodeRecordPrev1 x.sess x.enc).length < 2 ^ 32 ∧
          x.dir.changed.length < 2 ^ 32⌝ ∗
          sessStoreBoxAt x.fut x.self x.addrA x.recA 0#8 ∗
          dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
          protocolAddressAt A x.addr x.addrA ∗
          sessionRecordPrevAt A x.recA ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
          A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
          sessStoreBoxAt x.fut x.self x.addrA x.recA 1#8 ∗
          dirAt A x.self
            (x.dir.put (addressText x.addr.val) (encodeRecordPrev1 x.sess x.enc)) ∗
          (x.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (x.out + 8#64) 40 ∗
          protocolAddressAt A x.addr x.addrA ∗
          sessionRecordPrevAt A x.recA ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
          A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf =>
        ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }

/-! ## 3. Cell-Unpacked `serializePrev1BodySpecX` & Poll Symbolic Execution -/

theorem serializePrev1_cells_placed_ok [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {calleeStk : Nat}
    (hSer : subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A)))
    (hle : Proofs.libsignal.Hooks2.serializeStackX ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog entry
      (StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1CellsSpec A calleeStk)) := by
  intro g R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [serializePrev1CellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hfsp, hlen⟩, hmem⟩
  rw [← hfsp] at hmem
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk)
    (calleeStk - Proofs.libsignal.Hooks2.serializeStackX)
  let callG : SerializePrev1BodyGhost :=
    ⟨g.recA, g.out, g.prevCap, g.prevPtr, g.G, g.sess, g.enc⟩
  have hpre0 : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A)).pre callG s0 ∗
        (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [serializePrev1BodySpecX, callG]
    simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨g.o3, g.o2, g.o1, g.o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hlen⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; ac_rfl
  rcases hSer callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, serializePrev1BodySpecX, serializePrev1CellsSpec,
      callG] at hq ⊢
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
    rw [← hfsp, stackAt_sub_split s0.sp hle hhi]
    dsimp only [okTagVec, stkRem] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, serializePrev1BodySpecX,
      serializePrev1CellsSpec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem close_panic_prev1_placed {s0 s_call sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn at hfail ⊢
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

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
  ac_rfl

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

set_option maxHeartbeats 600000 in
theorem sessStorePollPrev1Inner_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {calleeStk : Nat}
    (hAddrCells : subroutine_ok (lsProg_570 H) (lsmpl.base 594)
      (StoreKit.withLsCodeRoLoaded lsmpl (addrTextCellsSpec A calleeStk)))
    (hSerCells : subroutine_ok (lsProg_570 H) (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1CellsSpec A calleeStk)))
    (hPutCells : subroutine_ok (lsProg_570 H) (lsmpl.base 542)
      (StoreKit.withLsCodeRoLoaded lsmpl (dirPutCellsSpec A calleeStk))) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (StoreKit.withLsCodeRoLoaded lsmpl (cliStorePollPrev1InnerSpec A calleeStk)) := by
  unfold StoreKit.withLsCodeRoLoaded
  simp (config := { maxSteps := 2000000 }) only [cliStorePollPrev1InnerSpec,
    memRegion_48_cells, memRegion_40_cells,
    cells_26_split_prev1_placed, cells_sub_4_eq_prev1_placed, cells_sub_5_eq_prev1_placed,
    cells_sub_6_200_eq_prev1_placed, cells_sub_6_48_eq_prev1_placed,
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
    (x.addrA, x.addr, s0.sp - 200#64, _, _, _, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_prev1_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 52) hcrl_sf
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl2
  wp_call_lscro (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1CellsSpec A calleeStk)) from hSerCells) hcrl2
    ⟨x.recA, s0.sp - 144#64, x.prevCap, x.prevPtr, x.G, x.sess, x.enc,
      _, _, _, _, s0.sp - 208#64⟩
  case panic =>
    intro sf _ hm
    exact close_panic_prev1_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 542) hcrl_sf_1
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm]) (by wp_norm_lhs)
  intro hcrl3
  wp_call_lscro (show subroutine_ok ((blkPC_570).rebase (blkPl_570).base H) (lsmpl.base 542)
      (StoreKit.withLsCodeRoLoaded lsmpl (dirPutCellsSpec A calleeStk)) from hPutCells) hcrl3
    (x.self, x.dir, s0.sp - 200#64, addressText x.addr.val,
      s0.sp - 176#64, w, w_1, encodeRecordPrev1Mem x.G x.sess x.enc, s0.sp - 208#64)
  case panic =>
    intro sf _ hm
    exact close_panic_prev1_placed (by simp only [wp_norm, arm64_norm, *]) hm
  apply SepWPp.of_sepWP_ret
  wp_steps
  wp_done

/-! ## 4. Top-Level Relocatable Hop Theorems & Filesystem Preservation -/

theorem sessStorePollPrev1Mem_placed_of_inner [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (StoreKit.withLsCodeRoLoaded lsmpl (cliStorePollPrev1InnerSpec A calleeStk)))
    (hstk : 0xd0 + calleeStk ≤ stk) :
    subroutine_ok prog entry (sessStorePollPrev1MemSpecPlaced A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [sessStorePollPrev1MemSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, henc, hdir⟩, hmem⟩
  dsimp only [sessStoreBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₆₄ x.addrA) ∗ ((x.fut + 16#64) ↦₆₄ x.recA) ∗
        ((x.fut + 24#64) ↦₈ 0#8) ∗ memRegion (x.fut + 25#64) 7 ∗
        dirAt A x.self x.dir ∗ memRegion x.out 48 ∗
        protocolAddressAt A x.addr x.addrA ∗
        prevVecAt A x.recA x.prevCap x.prevPtr [x.enc] ∗
        sessionStateReprAt A (x.recA + 24#64) x.G x.sess ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 208 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
    stackAt_storePoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 25#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 208))
  have hpre_in : s0.mem ⊨
      (StoreKit.withLsCodeRoLoaded lsmpl (cliStorePollPrev1InnerSpec A calleeStk)).pre x s0 ∗
        (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [cliStorePollPrev1InnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc, hdir⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; ac_rfl
  rcases hInner hcal_hi x (F_extra ∗ R) s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliStorePollPrev1InnerSpec,
      sessStorePollPrev1MemSpecPlaced, sessStoreBoxAt] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 208) (by omega) hstk_hi,
      stackAt_storePoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; ac_rfl
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [StoreKit.withLsCodeRoLoaded, cliStorePollPrev1InnerSpec,
      sessStorePollPrev1MemSpecPlaced] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem sessStorePollPrev1Mem_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A)))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hstk : 0xd0 + max (max addrStk Proofs.libsignal.Hooks2.serializeStackX)
      (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570) (sessStorePollPrev1MemSpecPlaced A stk) := by
  have hAddr' := ls_transfer_lscro (callerProg := lsProg_570 H) hAddr (by decide) hAddrBlk hAddrUnmut
  have hSer' := ls_transfer_lscro (callerProg := lsProg_570 H) hSer (by decide) hSerBlk hSerUnmut
  have hPut' := ls_transfer_lscro (callerProg := lsProg_570 H) hPut (by decide) hPutBlk hPutUnmut
  refine sessStorePollPrev1Mem_placed_of_inner (fun hhi => ?_) hstk
  exact sessStorePollPrev1Inner_placed_ok
    (addrText_cells_placed_ok hAddr' (by omega) hhi)
    (serializePrev1_cells_placed_ok hSer' (by omega) hhi)
    (dirPut_cells_placed_ok hPut' (by omega) hhi)

theorem sessStorePollPrev1_placed_of_mem [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {entry : BitVec 64} {stk : Nat}
    (hMem : subroutine_ok prog entry (sessStorePollPrev1MemSpecPlaced A stk)) :
    subroutine_ok prog entry (sessStorePollPrev1SpecPlaced A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl, hpre'⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [sessStorePollPrev1SpecPlaced] at hpre'
  rw [sessionRecordPrevAt_some_eq A x.recA x.prevCap x.prevPtr x.G x.sess [x.enc],
    sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx8, hname, hcanon, hlen, hdir⟩, hmem⟩
  have henc := encodeRecordPrev1Mem_eq_of_canon x.enc hcanon
  have hpre_mem : s0.mem ⊨ (sessStorePollPrev1MemSpecPlaced A stk).pre x s0 ∗ R := by
    unfold sessStorePollPrev1MemSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, henc.symm ▸ hlen, hdir⟩, ?_⟩
    convert hmem using 1; ac_rfl
  rcases hMem x R s0 hpc hrun hpre_mem hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [sessStorePollPrev1MemSpecPlaced, sessStorePollPrev1SpecPlaced,
      StoreKit.withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    rw [henc] at hq
    rw [sessionRecordPrevAt_some_eq A x.recA x.prevCap x.prevPtr x.G x.sess [x.enc]]
    refine ⟨htr, ?_⟩
    convert hq using 1; ac_rfl
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, hq⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨code, hex, hq⟩))⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))⟩

theorem sessStorePollPrev1_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {addrProg serProg putProg : Program} {addrBlk serBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H]
    [IsLsBlockProg serProg serBlk H]
    [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (hAddr : subroutine_ok addrProg (lsmpl.base 594) (addrTextSpecPlaced A addrStk))
    (hSer : subroutine_ok serProg (lsmpl.base 52)
      (StoreKit.withLsCodeRoLoaded lsmpl (serializePrev1BodySpecX A)))
    (hPut : subroutine_ok putProg (lsmpl.base 542) (dirPutSpecPlaced A putStk))
    (hstk : 0xd0 + max (max addrStk Proofs.libsignal.Hooks2.serializeStackX)
      (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hSerBlk : serBlk < 619 := by decide)
    (hSerUnmut : (serBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570) (sessStorePollPrev1SpecPlaced A stk) :=
  sessStorePollPrev1_placed_of_mem
    (sessStorePollPrev1Mem_placed_ok_of_deps hAddr hSer hPut hstk
      hAddrBlk hAddrUnmut hSerBlk hSerUnmut hPutBlk hPutUnmut)

theorem cli_placed_steps_files_eq_of_trace_eq [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (cliExternsPlaced mmpl W)]
    {s0 sf : State} (hsteps : Steps prog s0 sf) (htr : sf.trace = s0.trace) :
    sf.fs.files = s0.fs.files :=
  (traceFsSound_cli_placed mmpl W (prog := prog)).files_eq hsteps (evs := [])
    (by simp [htr]) NoFsEv.nil

theorem cli_placed_steps_fsInv [LibsignalPlacement] (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (cliExternsPlaced mmpl W)]
    {F0 : FsFiles} {T0 : List TraceEvent} {s0 sf : State}
    (hinv : FsInv F0 T0 s0) (hsteps : Steps prog s0 sf) :
    FsInv F0 T0 sf :=
  hinv.of_steps (traceFsSound_cli_placed mmpl W (prog := prog)) hsteps

theorem cli_placed_steps_fsInv_of_trace_eq [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (W : CliHooks)
    {prog : Program} {i : Nat} [IsLsBlockProg prog i (cliExternsPlaced mmpl W)]
    {F0 : FsFiles} {T0 : List TraceEvent} {s0 sf : State}
    (hinv : FsInv F0 T0 s0) (hsteps : Steps prog s0 sf) (_htr : sf.trace = s0.trace) :
    FsInv F0 T0 sf :=
  cli_placed_steps_fsInv mmpl W hinv hsteps

end Placed

end CryptoVerification.SignalSession.Cli.Store.StoreSessionPrev1
