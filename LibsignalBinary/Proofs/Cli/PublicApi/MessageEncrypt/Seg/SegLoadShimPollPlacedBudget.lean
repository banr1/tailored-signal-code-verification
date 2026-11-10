/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPoll
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.SymWP
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs -- shake: keep

/-!
# Budget-Threaded Relocatable `segLoad` Prologue, Load Shim, and Poll (`+0x000..+0x160`)

Proves `segLoad_to_dispatch_budget` on Block `464` (`lsProg_464 Hk`) under `RustCliAllocBudget M`
and `[LibsignalPlacement]`, threading allocation budgets across `E0`, `kit.loadShim`, `kit.loadPoll`,
and `E1` up to the `+0x160` dispatch seam.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlacedBudget

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  LibsignalCodeRoLoaded withLsCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommonPlacedBudget
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] spAligned_writeVReg128 loadBoxSize_ofNat_toNat

/-! ## 1. `WithStoresEncEnv` Reassociation & `LoadRemEnv` -/

/-- Remaining allocation envelope after `loadShim` + `loadPoll` + `Box` dealloc (`+0x160` dispatch). -/
def LoadRemEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : WithStoresEncGhost) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
  FromCurEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 Scope x evs

theorem seqEnv3_reassoc {E1 E2 E3 E4 : List AllocEvent → Prop} :
    ∀ evs, SeqEnv E1 (SeqEnv E2 (SeqEnv E3 E4)) evs →
      SeqEnv (SeqEnv E1 (SeqEnv E2 E3)) E4 evs := by
  rintro evs (h1 | ⟨e1, er1, rfl, he1, h2 | ⟨e2, er2, rfl, he2, h3 | ⟨e3, e4, rfl, he3, he4⟩⟩⟩)
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr ⟨e1, er1, rfl, he1, Or.inl h2⟩)
  · exact Or.inl (Or.inr ⟨e1, e2 ++ er2, rfl, he1, Or.inr ⟨e2, er2, rfl, he2, h3⟩⟩)
  · refine Or.inr ⟨e1 ++ (e2 ++ e3), e4, ?_, ?_, he4⟩
    · simp only [List.append_assoc]
    · exact Or.inr ⟨e1, e2 ++ e3, rfl, he1, Or.inr ⟨e2, e3, rfl, he2, he3⟩⟩

private theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
private theorem cs_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x20 = s0.readReg64 .x20 := h.2.1
private theorem cs_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x21 = s0.readReg64 .x21 := h.2.2.1
private theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
private theorem cs_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x23 = s0.readReg64 .x23 := h.2.2.2.2.1
private theorem cs_x24 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x24 = s0.readReg64 .x24 := h.2.2.2.2.2.1
private theorem cs_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x25 = s0.readReg64 .x25 := h.2.2.2.2.2.2.1
private theorem cs_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x27 = s0.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
private theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
private theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
private theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

theorem loadOutResPlaced_atState_eq {M : AllocCostModel}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
    (w0 w1 w2 w3 w4 w5 w6 : BitVec 64) (tail : List (BitVec 8)) :
    LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail =
    LoadOutResPlaced Scope (A.atState lim st s) ans w0 w1 w2 w3 w4 w5 w6 tail := by
  rcases ans with ⟨⟩ | (_ | _) <;> rfl

theorem dispatchFramePlaced_retag_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (kit : SessionStoreSpec A.repAlloc 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ist0 : ikit.IdState)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (s0 : State) (v50 : BitVec 64) :
    dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50 =
    dispatchFramePlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
      (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 ctl x s0 v50 := rfl

/-! ## 2. Straight-Line `by_vm_steps` Blocks (`E0`, Pre-Poll, and `E1` Sub-Blocks) -/

private theorem sepWP_mono_post {P : Program} {tgt : BitVec 64} {s0 : State}
    {Pre : SepProp} {Post1 Post2 : State → SepProp → Prop}
    (h1 : SepWP P tgt s0 Pre Post1)
    (h2 : ∀ sm Pm, Post1 sm Pm → Post2 sm Pm) :
    SepWP P tgt s0 Pre Post2 := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sa, hs1, ⟨hpc1, hrun1, Pa, hma, hp1⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h1 hm hL
  · exact ⟨sa, hs1, Or.inl ⟨hpc1, hrun1, Pa, hma, h2 sa Pa hp1⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem sepWP_trans {P : Program} {mid tgt : BitVec 64} {s0 : State}
    {Pre : SepProp} {Post1 Post2 : State → SepProp → Prop}
    (h1 : SepWP P mid s0 Pre Post1)
    (h2 : ∀ sa Pa, sa.pc = mid → sa.status = .Running → Post1 sa Pa → SepWP P tgt sa Pa Post2) :
    SepWP P tgt s0 Pre Post2 := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sa, hs1, ⟨hpc1, hrun1, Pa, hma, hp1⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h1 hm hL
  · obtain ⟨sb, hs2, hout2⟩ :=
      SepWP.to_reaches_pc (h2 sa Pa hpc1 hrun1 hp1) hma (hs1.codeLoaded hL)
    exact ⟨sb, hs1.trans hs2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

set_option maxHeartbeats 800000 in
private theorem segLoad_shim_prologue_wp_vm [LibsignalPlacement]
    {A : RustAlloc} {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {Hk : LibsignalHooks}
    (x : WithStoresEncGhost) (s0 : State) (F : SepProp)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hpc : s0.pc = encEntryPlaced)
    (hrun : s0.status = .Running)
    (hal : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ptA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length)
    (hx2 : s0.readReg64 .x2 = x.remA)
    (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.ssA)
    (hx5 : s0.readReg64 .x5 = kit.ss_vt)
    (hx6 : s0.readReg64 .x6 = x.idA)
    (hx7 : s0.readReg64 .x7 = ikit.id_vt)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x28#64) s0
      (nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ loadVtablesAt kit ∗ F)
      (fun sa Pa =>
        VmPreserved s0 sa ∧
        sa.sp = s0.sp - 0xbe0#64 ∧ sa.spAligned = true ∧
        sa.fs = s0.fs ∧ sa.trace = s0.trace ∧
        sa.readReg64 .x0 = x.ptA ∧
        sa.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length ∧
        sa.readReg64 .x2 = x.remA ∧
        sa.readReg64 .x3 = x.locA ∧
        sa.readReg64 .x4 = x.ssA ∧
        sa.readReg64 .x5 = kit.ss_vt ∧
        sa.readReg64 .x6 = x.idA ∧
        sa.readReg64 .x7 = ikit.id_vt ∧
        sa.readReg64 .x8 = x.now.tvSec ∧
        sa.readReg64 .x19 = x.ret ∧
        sa.readReg64 .x29 = s0.sp - 0x60#64 ∧
        calleeSavedVRegs sa = calleeSavedVRegs s0 ∧
        Pa = (nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          memRegion (s0.sp - 3040#64) 0xb80 ∗
          stackAt (s0.sp - 3040#64) (encSubStackV kit ikit) ∗
          loadVtablesAt kit ∗ F)) := by
  have hal_norm : (s0.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8
  by_vm_steps (
    wp_conv_pre =>
      unfold nowAt
      rw [stackAt_withStoresEncStack_split kit ikit s0.sp hsp_le]
    wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      bv_sub_add_lit, sepConj_assoc]
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    apply SepWP.exists_elim; intro _
    wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    apply SepWP.fold (encSavedRegs_fold s0.sp s0) (by sep_focus)
    wp_steps
    apply SepWP.fold (nowAt_fold s0.sp x.now) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm,
        hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hal_norm, true_and]
      sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem segLoad_shim_spills_wp_vm [LibsignalPlacement]
    {A : RustAlloc} {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {Hk : LibsignalHooks}
    (x : WithStoresEncGhost) (s0 sa : State) (F : SepProp)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hpc : sa.pc = encEntryPlaced + 0x28#64)
    (hrun : sa.status = .Running)
    (hspa : sa.sp = s0.sp - 0xbe0#64)
    (hal0 : s0.spAligned = true)
    (hfsa : sa.fs = s0.fs)
    (htra : sa.trace = s0.trace)
    (hx0 : sa.readReg64 .x0 = x.ptA)
    (hx1 : sa.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length)
    (hx2 : sa.readReg64 .x2 = x.remA)
    (hx3 : sa.readReg64 .x3 = x.locA)
    (hx4 : sa.readReg64 .x4 = x.ssA)
    (hx5 : sa.readReg64 .x5 = kit.ss_vt)
    (hx6 : sa.readReg64 .x6 = x.idA)
    (hx7 : sa.readReg64 .x7 = ikit.id_vt)
    (hx8 : sa.readReg64 .x8 = x.now.tvSec)
    (hx19 : sa.readReg64 .x19 = x.ret)
    (hx29 : sa.readReg64 .x29 = s0.sp - 0x60#64)
    (hvregs : calleeSavedVRegs sa = calleeSavedVRegs s0) :
    SepWP (lsProg_464 Hk) (0#64 + kit.loadShimOff) sa
      (nowAt s0.sp x.now ∗
        encSavedRegs s0.sp s0 ∗
        memRegion (s0.sp - 3040#64) 0xb80 ∗
        stackAt (s0.sp - 3040#64) (encSubStackV kit ikit) ∗
        loadVtablesAt kit ∗ F)
      (fun sm P_m =>
        VmPreserved sa sm ∧
        ∃ v50 v470 v478 waker0 waker1 v830 v838 v840 : BitVec 64,
          sm.sp = s0.sp - 0xbe0#64 ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧
          sm.trace = s0.trace ∧
          sm.readReg64 .x0 = x.ssA ∧
          sm.readReg64 .x1 = x.remA ∧
          sm.readReg64 .x19 = x.ret ∧
          sm.readReg64 .x29 = s0.sp - 0x60#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x30 = encEntryPlaced + 0x90#64 ∧
          P_m = (nowAt s0.sp x.now ∗
            encSavedRegs s0.sp s0 ∗
            stackAt sm.sp kit.loadShimStack ∗
            memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
              (encSubStackV kit ikit - kit.loadShimStack) ∗
            memRegion (s0.sp - 0xbe0#64) 0x50 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
            encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
            ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
            ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
            ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
            ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
            loadVtablesAt kit ∗ F)) := by
  have hsub := encSubStackV_le_two_pow_64 kit ikit hsp_le
  have hal_norm : (s0.sp &&& 15#64 == 0#64) = true := hal0
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hspa hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8 hx19 hx29
  wp_step
  have hvm_pair : ∀ sm, VmPreserved sa sm ↔
      VmPreserved ((sa.writeReg64 (Reg.gpr 10#5)
        (blkPl_464.ρ "libsignal_cli_ratchet:.rodata..Lanon.8")).setPC (blkPl_464.base + 48#64)) sm := by
    intro sm
    have hstep : VmPreserved sa ((sa.writeReg64 (Reg.gpr 10#5)
        (blkPl_464.ρ "libsignal_cli_ratchet:.rodata..Lanon.8")).setPC (blkPl_464.base + 48#64)) := by
      simp only [wp_norm, arm64_norm]
    exact ⟨fun h => hstep.symm.trans h, fun h => hstep.trans h⟩
  simp only [hvm_pair]
  by_vm_steps (
    wp_conv_pre =>
      unfold nowAt loadVtablesAt
      rw [memRegion_0xb80_split (s0.sp - 3040#64),
          exists_pointsTo128_eq_two_pointsTo64 (s0.sp - 3040#64 + 0x830#64)]
      simp (config := { maxSteps := 400000 }) only [cells_succ, cells_zero, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        bv_sub_add_lit, sepConj_assoc]
    repeat (apply SepWP.exists_elim; intro v_tmp)
    wp_steps
    wp_clear_temps
    rename_i v1 v2 v3 v4 v5 v6
    apply SepWP.fold (nowAt_fold s0.sp x.now) (by sep_focus)
    apply SepWP.fold (fold_sp50_sub s0.sp) (by sep_focus)
    apply SepWP.fold (encSpillsInit_sub_fold kit.ss_vt ikit.id_vt s0.sp x) (by sep_focus)
    apply SepWP.fold (pointsTo16_zero_sub s0.sp) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_encSub_shim kit ikit (s0.sp - 3040#64) hsub)) (by sep_focus)
    have hvt :
        ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
        ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
        ((0#64 + (kit.loadFutVtOff + 8#64)) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + (kit.loadFutVtOff + 16#64)) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + (kit.loadFutVtOff + 24#64)) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ⊢
          loadVtablesAt kit := by
      unfold loadVtablesAt
      simp only [BitVec.add_assoc]
      exact Entails.refl _
    apply SepWP.fold hvt (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, v_tmp, v5, v6,
      lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.8",
      lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.8",
      v4, v3, v2, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, bv_sub_add_lit,
        hspa, hfsa, htra, hx19, hx29, hvregs, hal_norm, true_and]
      sep_ac_rfl)

theorem segLoad_shim_budget_wp_vm [LibsignalPlacement]
    {A : RustAlloc} {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {Hk : LibsignalHooks}
    (x : WithStoresEncGhost) (s0 : State) {sp : BitVec 64} (F : SepProp)
    (hsp_le : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hsp0 : sp = s0.sp - 0xbe0#64)
    (hpc : s0.pc = encEntryPlaced)
    (hrun : s0.status = .Running)
    (hal : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ptA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length)
    (hx2 : s0.readReg64 .x2 = x.remA)
    (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.ssA)
    (hx5 : s0.readReg64 .x5 = kit.ss_vt)
    (hx6 : s0.readReg64 .x6 = x.idA)
    (hx7 : s0.readReg64 .x7 = ikit.id_vt)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP (lsProg_464 Hk) (0#64 + kit.loadShimOff) s0
      (nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ loadVtablesAt kit ∗ F)
      (fun sm P_m =>
        VmPreserved s0 sm ∧
        ∃ v50 v470 v478 waker0 waker1 v830 v838 v840 : BitVec 64,
          sm.sp = sp ∧ sm.spAligned = true ∧
          sm.fs = s0.fs ∧
          sm.trace = s0.trace ∧
          sm.readReg64 .x0 = x.ssA ∧
          sm.readReg64 .x1 = x.remA ∧
          sm.readReg64 .x19 = x.ret ∧
          sm.readReg64 .x29 = s0.sp - 0x60#64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0 ∧
          sm.readReg64 .x30 = encEntryPlaced + 0x90#64 ∧
          P_m = (nowAt s0.sp x.now ∗
            encSavedRegs s0.sp s0 ∗
            stackAt sm.sp kit.loadShimStack ∗
            memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
            memRegion sp 0x50 ∗
            ((sp + 0x50#64) ↦₆₄ v50) ∗
            encSpillsInit kit.ss_vt ikit.id_vt sp x ∗
            ((sp + 0x108#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 0x110#64) 0x358 ∗
            ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
            memRegion (sp + 0x46a#64) 6 ∗
            ((sp + 0x470#64) ↦₆₄ v470) ∗ ((sp + 0x478#64) ↦₆₄ v478) ∗
            ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
            ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8 ∗
            memRegion (sp + 0x580#64) 368 ∗
            memRegion (sp + 0x6f0#64) 8 ∗
            memRegion (sp + 0x6f8#64) 312 ∗
            ((sp + 0x830#64) ↦₆₄ v830) ∗ ((sp + 0x838#64) ↦₆₄ v838) ∗
            ((sp + 0x840#64) ↦₆₄ v840) ∗
            memRegion (sp + 0x848#64) 0x338 ∗
            loadVtablesAt kit ∗ F)) := by
  subst hsp0
  refine sepWP_trans
    (segLoad_shim_prologue_wp_vm x s0 F hsp_le hpc hrun hal hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8) ?_
  rintro sa Pa hpca hruna
    ⟨hvma, hspa, _hala, hfsa, htra, hx0a, hx1a, hx2a, hx3a, hx4a, hx5a, hx6a, hx7a, hx8a,
      hx19a, hx29a, hvregsa, rfl⟩
  exact sepWP_mono_post
    (segLoad_shim_spills_wp_vm x s0 sa F hsp_le hpca hruna hspa hal hfsa htra
      hx0a hx1a hx2a hx3a hx4a hx5a hx6a hx7a hx8a hx19a hx29a hvregsa)
    (fun _ _ ⟨hvm2, hrest⟩ => ⟨hvma.trans hvm2, hrest⟩)

theorem segLoad_pre_poll_budget_wp_vm [LibsignalPlacement]
    {A : RustAlloc} {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {Hk : LibsignalHooks}
    {s : State} {sp box v470 v478 : BitVec 64} {F : SepProp}
    (hsub : encSubStackV kit ikit ≤ 2 ^ 64)
    (hpc : s.pc = encEntryPlaced + 0x90#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = box)
    (hx1 : s.readReg64 .x1 = 0#64 + kit.loadFutVtOff) :
    SepWP (lsProg_464 Hk) (0#64 + kit.loadPollOff) s
      (((sp + 0x470#64) ↦₆₄ v470) ∗ ((sp + 0x478#64) ↦₆₄ v478) ∗
        stackAt s.sp kit.loadShimStack ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
        loadVtablesAt kit ∗ F)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.fs = s.fs ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧
        sf.readReg64 .x8 = sp + 0x580#64 ∧
        sf.readReg64 .x20 = sp + 0x580#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xac#64 ∧
        P_f = (((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
          memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadPollStack) ∗
          stackAt sp kit.loadPollStack ∗
          loadVtablesAt kit ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx0 hx1
  by_vm_steps (
    apply SepWP.fold (Entails.of_eq (stack_encSub_shim_to_poll_eq kit ikit hsub rfl)) (by sep_focus)
    wp_conv_pre => unfold loadVtablesAt
    wp_simp_pre [sepConj_assoc]
    wp_steps
    have hvt :
        ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
        ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
        ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ⊢
          loadVtablesAt kit :=
      Entails.refl _
    apply SepWP.fold hvt (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx0, hal_norm, true_and]
      sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem segLoad_e1_to_memcpy_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp w0 w1 w2 w3 w4 w5 w6 v830 v838 v840 : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xac#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x580#64)
    (hw0_ne : w0 ≠ 0xFFFFFFFFFFFFFFFD#64) :
    SepWP (lsProg_464 Hk) (lsmpl.ρ "memcpy") s
      (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
        ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
        ((sp + 0x5b0#64) ↦₆₄ w6) ∗
        ((sp + 0x830#64) ↦₆₄ v830) ∗ ((sp + 0x838#64) ↦₆₄ v838) ∗ ((sp + 0x840#64) ↦₆₄ v840))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
          ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
          ((sp + 0x5b0#64) ↦₆₄ w6) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6)) ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x6f8#64 ∧
        sf.readReg64 .x1 = sp + 0x5b8#64 ∧
        sf.readReg64 .x2 = 0x138#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x12c#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x24 = w0 ∧ sf.readReg64 .x27 = w1 ∧
        sf.readReg64 .x21 = w2 ∧ sf.readReg64 .x23 = w3 ∧
        sf.readReg64 .x25 = sp + 0x580#64 ∧
        sf.readReg64 .x28 = sp + 0x4a0#64) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hw0_b : (w0 + 3#64 == 0#64) = false := ne_neg3_add3_ne_zero hw0_ne
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx20
  by_vm_steps (
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · sep_ac_rfl
    · simp only [wp_norm, arm64_norm, hal_norm, true_and])

theorem segLoad_e1_to_drop_wp_vm [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) {Hk : LibsignalHooks}
    {s : State} {sp box : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x12c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true) :
    SepWP (lsProg_464 Hk) (0#64 + kit.loadFutDropOff) s
      (((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
        ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
          ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff))) ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧
        sf.readReg64 .x20 = box ∧
        sf.readReg64 .x22 = 0#64 + kit.loadFutVtOff ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x144#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x28 = s.readReg64 .x28) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hdz' : (0#64 + kit.loadFutDropOff == 0#64) = false := loadFutDrop_placed_ne_zero kit
  have hdz'' : (kit.loadFutDropOff == 0#64) = false := by simpa only [BitVec.zero_add] using hdz'
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  by_vm_steps (
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · sep_ac_rfl
    · simp only [wp_norm, arm64_norm, hal_norm, true_and])

theorem segLoad_e1_to_dealloc_wp_vm [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) {Hk : LibsignalHooks}
    {s : State} {sp box : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x144#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = box)
    (hx22 : s.readReg64 .x22 = 0#64 + kit.loadFutVtOff) :
    SepWP (lsProg_464 Hk) (lsmpl.ρ lsRustDeallocSym) s
      (((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
          ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧
        sf.readReg64 .x1 = BitVec.ofNat 64 kit.loadBoxSize ∧
        sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x158#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x28 = s.readReg64 .x28) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hsz' : (BitVec.ofNat 64 kit.loadBoxSize == 0#64) = false :=
    beq_false_of_ne kit.loadBoxSize_ne_zero
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsRustDeallocSym, lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx20 hx22
  by_vm_steps (
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · sep_ac_rfl
    · simp only [wp_norm, arm64_norm, hal_norm, true_and])

theorem segLoad_e1_tail_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp w0 : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x158#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = w0) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x160#64) s
      emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = emp ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x24 = w0 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.pstate = addsPState64 w0 2#64) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx24
  by_vm_steps (
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, rfl, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx24, hal_norm, true_and])

/-! ## 3. Combined `E0` + `loadShim` + `loadPoll` + `E1` to `+0x160` (`segLoad_to_dispatch_budget`) -/

set_option maxHeartbeats 1600000 in
theorem segLoad_to_dispatch_budget [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s0)
    (hpc0 : s0.pc = encEntryPlaced) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).pre
        (x, st_init) s0 ∗ R)
    (hcont : ∀ (s : State) (st3 : M.σ) (sp : BitVec 64)
      (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
      (w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8)),
      SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
        st_init st3 (LoadRemEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x) →
      sp = s0.sp - 0xbe0#64 →
      s.pc = encEntryPlaced + 0x160#64 →
      encMidMetaPlaced x s0 s →
      x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStackV kit ikit ≤ s0.sp.toNat →
      w0 ≠ 0xFFFFFFFFFFFFFFFD#64 → tail.length = 312 →
      kit.loadRel st0 x.rem.val ans →
      s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans →
      s.readReg64 .x24 = w0 → s.readReg64 .x27 = w1 →
      s.readReg64 .x21 = w2 → s.readReg64 .x23 = w3 →
      s.readReg64 .x25 = sp + 0x580#64 →
      s.readReg64 .x26 = sp + 0x9d0#64 →
      s.readReg64 .x28 = sp + 0x4a0#64 →
      s.pstate = addsPState64 w0 2#64 →
      (s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st3 s ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R s0 s
        (fun s' => ∃ st' r g sess,
          CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
            x st_init st' r g sess R s0 s')) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s0
      (fun s' => ∃ st' r g sess,
        CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r g sess R s0 s') := by
  obtain ⟨hcrl0, hm0⟩ := StoreKit.extract_withLsCodeRoLoaded hm0
  dsimp only [withStoresEncBudgetSpecV] at hm0
  rw [cliTapeAt_eq_pure_sep_cliTapeAfter_zero] at hm0
  have hpull0 :
      (⌜FitsEnv M lim st_init
            (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) ∧
          s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
          s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗
        (⌜x.rest.length < 2 ^ 63⌝ ∗ cliTapeAfter ctl x.cur x.rest 0) ∗
        FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
        A.pool lim st_init s0) ∗ R =
      ⌜FitsEnv M lim st_init
          (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) ∧
        s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
        x.locA ≠ 0#64 ∧
        s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
        s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
        withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
        kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
      (⌜x.rest.length < 2 ^ 63⌝ ∗
      ((nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
        (protocolAddressAt A.repAlloc x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool lim st_init s0 ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗
            cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0))) ∗ R)) := by
    sep_ac_rfl
  rw [hpull0] at hm0
  obtain ⟨⟨hfit0, hx0, hx1_nat, hpt_lt, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hnsec, hx8,
    hsp_le, haddr_ss, _haddr_id⟩, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  obtain ⟨hrest_lt, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  have hbud0 :
      SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st_init
        (SeqEnv (BoxAllocEnv kit.loadBoxSize)
          (SeqEnv (kitEnv.loadPollEnv st0 x.rem.val)
            (SeqEnv (· = rustDeallocEvents kit.loadBoxSize 8)
              (LoadRemEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x)))) :=
    (_root_.LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SeamBudget.init
      hfit0).narrow fun evs h => seqEnv3_reassoc evs h
  have hsub := encSubStackV_le_two_pow_64 kit ikit hsp_le
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm_vt := loadVtablesPlaced_intro env.vtables hcrl0.2 hm0
  let F_e0 : SepProp :=
    protocolAddressAt A.repAlloc x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool lim st_init s0 ∗
      ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗
        cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0)
  have hm_e0 : s0.mem ⊨
      (nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ loadVtablesAt kit ∗ emp) ∗
      (F_e0 ∗ R) := by
    dsimp only [F_e0]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_vt
  refine SegExitBudget.of_sepWP (R0 := R) hm_e0
    (segLoad_shim_budget_wp_vm x s0 emp hsp_le rfl hpc0 hrun0 hal0
      hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8) ?_
  intro sm P_m _ hsteps_e0 hpcm hrunm hmm hpostm
  rcases hpostm with ⟨hvm0, v50, v470, v478, waker0, waker1, v830, v838, v840,
    hspm, halm, _hfsm, htrm, hx0m, hx1m, hx19m, hx29m, hvregsm, hx30m, rfl⟩
  have hcrlm : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem := hcrl0.of_keepsFrozen hsteps_e0.keepsFrozen
  have hprefm : s0.trace <+: sm.trace := by rw [htrm]
  let F_shim : SepProp :=
    shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      kit.storeAt x.ssA st0 ∗
      loadVtablesAt kit
  have hm_shim : sm.mem ⊨
      (kitLoadShimBudgetSpec M A lim kit).pre (⟨x.ssA, x.remA⟩, st_init) sm ∗ (F_shim ∗ R) := by
    dsimp only [kitLoadShimBudgetSpec, F_shim, F_e0, shimFramePlaced] at hmm ⊢
    rw [← A.pool_transport lim st_init s0 sm hvm0] at hmm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0m, hx1m, hbud0.1.seq_left⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmm⟩
  refine call_rocl_alloc_placed (R0 := R)
    (env.kitOk.loadShim (callerProg := lsProg_464 Hk) (callerBlk := 464) (by decide))
    (⟨x.ssA, x.remA⟩, st_init) hpcm hrunm halm hx30m hprefm hcrlm hm_shim ?_
  intro sf1 hsteps_shim hpc1 hrun1 hsp1 hal1 hcs1 hcrl1 hm1
  dsimp only [kitLoadShimBudgetSpec] at hm1
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm1
  obtain ⟨evs_shim, ⟨hx1_1, _hbox_ne, _hbox_align, htr1, hevs_shim⟩, hm1⟩ := hm1
  have hbud1 := hbud0.advance hevs_shim
  set st1 := M.stepEvents evs_shim st_init
  set box := sf1.readReg64 .x0
  have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
  let F_pre : SepProp :=
    A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
      A.pool lim st1 sf1 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      kit.storeAt x.ssA st0
  have hm_pre : sf1.mem ⊨
      (((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
        stackAt sf1.sp kit.loadShimStack ∗
        memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - kit.loadShimStack) ∗
        loadVtablesAt kit ∗ emp) ∗ (F_pre ∗ R) := by
    dsimp only [F_pre, F_shim] at hm1 ⊢
    rw [hsp1]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
  refine SegExitBudget.of_sepWP (R0 := R) hm_pre
    (segLoad_pre_poll_budget_wp_vm hsub hpc1 hrun1 hsp1' hal1 rfl hx1_1) ?_
  intro sm2 P_m2 _ hsteps_pre hpcm2 hrunm2 hmm2 hpostm2
  rcases hpostm2 with ⟨hvm_pre, hspm2, halm2, _hfsm2, htrm2, hx0m2, hx8m2, hx20m2,
    hx19m2, hx29m2, hvregsm2, hx30m2, rfl⟩
  have hcrlm2 : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem := hcrl1.of_keepsFrozen hsteps_pre.keepsFrozen
  have hprefm2 : s0.trace <+: sm2.trace := by rw [htrm2, htr1, htrm]
  have henv2 : kit.envOk sm2.fs.files :=
    ((hfs.of_steps ((hsteps_e0.trans hsteps_shim).trans hsteps_pre)).envOk_at (evs := [])
      (by rw [htrm2, htr1, htrm, List.append_nil]) (fun _ => NoFsEv.nil)).1
  let pollCall : LoadPollCall × BitVec 64 × kit.StoreState × M.σ :=
    (⟨box, s0.sp - 0xbe0#64 + 0x580#64, x.remA, x.rem⟩, x.ssA, st0, st1)
  let F_poll : SepProp :=
    ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
      ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      loadVtablesAt kit ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840)
  have hm_poll : sm2.mem ⊨
      (kitLoadPollBudgetSpecS M A lim kit kitEnv Scope encRecord).pre pollCall sm2 ∗ (F_poll ∗ R) := by
    dsimp only [kitLoadPollBudgetSpecS, pollCall, F_poll, F_pre] at hmm2 ⊢
    rw [← A.pool_transport lim st1 sf1 sm2 hvm_pre] at hmm2
    rw [hspm2, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0m2, hx8m2, haddr_ss, hbud1.1.seq_left⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmm2⟩
  refine call_rocl_alloc_placed (R0 := R)
    (env.kitOk.loadPoll (callerProg := lsProg_464 Hk) (callerBlk := 464) (by decide))
    pollCall hpcm2 hrunm2 halm2 hx30m2 hprefm2 hcrlm2
    (withEnvPre_pre_intro (φ := fun s => kit.envOk s.fs.files) henv2 hm_poll) ?_
  intro sf2 hsteps_poll hpc2 hrun2 hsp2 hal2 hcs2 hcrl2 hm2
  dsimp only [kitLoadPollBudgetSpecSE, withEnvPre, kitLoadPollBudgetSpecS, pollCall] at hm2
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm2
  obtain ⟨ans, evs_poll, ⟨hl, htr2, hevs_poll⟩, hm2⟩ := hm2
  have hbud2 := hbud1.advance hevs_poll
  set st2 := M.stepEvents evs_poll st1
  have hsp2' : sf2.sp = s0.sp - 0xbe0#64 := by rw [hsp2, hspm2]
  have hx20_2 : sf2.readReg64 .x20 = s0.sp - 0xbe0#64 + 0x580#64 := by rw [cs_x20 hcs2, hx20m2]
  have hm2_out : sf2.mem ⊨
      loadPollPlacedOutAtS Scope A.repAlloc (s0.sp - 0xbe0#64 + 0x580#64) ans ∗
      ((kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st2 sf2 ∗ stackAt (s0.sp - 0xbe0#64) kit.loadPollStack ∗ F_poll) ∗ R) := by
    rw [hspm2] at hm2
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  have hm2_dec := Satisfies.mono
    (sepConj_mono_left (loadPollPlacedOutAtS_decompose_sp Scope A.repAlloc (s0.sp - 0xbe0#64) ans))
    hm2_out
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm2_dec
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, tail, ⟨hw0_ne, htail_len⟩, hm2_dec⟩ := hm2_dec
  let sp := s0.sp - 0xbe0#64
  let F_5a : SepProp :=
    ((sp + 0x5b8#64) ↦ₛ tail) ∗
      memRegion (sp + 0x6f8#64) 312 ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      ((sp + 0x470#64) ↦₆₄ box) ∗
      ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      loadVtablesAt kit ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (sp + 0x46a#64) 6 ∗
      ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
      ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8
  have hm_5a : sf2.mem ⊨
      (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
        ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
        ((sp + 0x5b0#64) ↦₆₄ w6) ∗
        ((sp + 0x830#64) ↦₆₄ v830) ∗ ((sp + 0x838#64) ↦₆₄ v838) ∗ ((sp + 0x840#64) ↦₆₄ v840)) ∗
      (F_5a ∗ R) := by
    dsimp only [F_5a, F_poll, sp] at hm2_dec ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2_dec
  refine SegExitBudget.of_sepWP (R0 := R) hm_5a
    (segLoad_e1_to_memcpy_wp_vm hpc2 hrun2 hsp2' hal2 hx20_2 hw0_ne) ?_
  rintro s3 P3 _ hsteps_5a hpc3 hrun3 hm3
    ⟨hvm_5a, rfl, hsp3, hal3, htr3, hx0_3, hx1_3, hx2_3, hx30_3,
      hx19_3, hx29_3, hvregs_3, hx24_3, hx27_3, hx21_3, hx23_3, hx25_3, hx28_3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps_5a.keepsFrozen
  let F_5b : SepProp :=
    (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
      ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((sp + 0x5b0#64) ↦₆₄ w6) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6)) ∗
    (LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      ((sp + 0x470#64) ↦₆₄ box) ∗
      ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      loadVtablesAt kit ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (sp + 0x46a#64) 6 ∗
      ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
      ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8)
  have hm_5b : s3.mem ⊨
      sessionMemcpyRegionBudgetSpec.pre (sp + 0x6f8#64, sp + 0x5b8#64, tail) s3 ∗ (F_5b ∗ R) := by
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, framelessMemcpySpec, F_5b, F_5a] at hm3 ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_3, hx1_3, by rw [hx2_3, htail_len]; rfl⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm3
  refine call_nopanic_placed (R0 := R) (memcpy_budget_ok env)
    (sp + 0x6f8#64, sp + 0x5b8#64, tail) hpc3 hrun3 hal3 hx30_3 hm_5b ?_
  intro s4 hsteps_5b hpc4 hrun4 hsp4 hal4 hcs4 hm4
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, framelessMemcpySpec] at hm4
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨hvm_5b, hm4⟩ := hm4
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨htr4, hm4⟩ := hm4
  have hcrl4 : StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem := hcrl3.of_keepsFrozen hsteps_5b.keepsFrozen
  have hsp4' : s4.sp = sp := by rw [hsp4, hsp3]
  have hm4_368 : s4.mem ⊨
      (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
        ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
        ((sp + 0x5b0#64) ↦₆₄ w6) ∗ ((sp + 0x5b8#64) ↦ₛ tail)) ∗
      (((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
        ((sp + 0x470#64) ↦₆₄ box) ∗
        ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - kit.loadPollStack) ∗
        loadVtablesAt kit ∗
        A.live box kit.loadBoxSize 8 ∗
        shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
        memRegion (sp + 0x46a#64) 6 ∗
        ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
        ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8 ∗ R) := by
    dsimp only [F_5b] at hm4
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm4
  have hm4_folded := Satisfies.mono
    (sepConj_mono_left (out368_fold sp w0 w1 w2 w3 w4 w5 w6 tail htail_len)) hm4_368
  let F_5c : SepProp :=
    ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
      ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
      ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (sp + 0x46a#64) 6 ∗
      ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
      ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8
  have hm_5c : s4.mem ⊨
      (((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
        ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff))) ∗ (F_5c ∗ R) := by
    unfold loadVtablesAt at hm4_folded
    dsimp only [F_5c]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm4_folded
  refine SegExitBudget.of_sepWP (R0 := R) hm_5c
    (segLoad_e1_to_drop_wp_vm kit hpc4 hrun4 hsp4' hal4) ?_
  rintro s5 P5 _ hsteps_5c hpc5 hrun5 hm5
    ⟨hvm_5c, rfl, hsp5, hal5, htr5, _hx0_5, hx20_5, hx22_5, hx30_5,
      hx19_5, hx29_5, hvregs_5, hx24_5, hx27_5, hx21_5, hx23_5, hx25_5, hx28_5⟩
  have hcrl5 : StoreKit.LibsignalCodeRoLoaded lsmpl s5.mem := hcrl4.of_keepsFrozen hsteps_5c.keepsFrozen
  have hm5_46a : s5.mem ⊨
      (memRegion (sp + 0x46a#64) 6 ∗
        ((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
        ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
        ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8) ∗
      ((((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
        ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
        ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - kit.loadPollStack) ∗
        A.live box kit.loadBoxSize 8 ∗
        shimFramePlaced kit ikit ist0 ctl x s0 v50) ∗ R) := by
    dsimp only [F_5c] at hm5
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm5
  have hm5_folded := Satisfies.mono
    (sepConj_mono_left (fold_46a_498 sp box (0#64 + kit.loadFutVtOff) waker0 waker1 0#64)) hm5_46a
  let F_5d : SepProp :=
    memRegion (sp + 0x46a#64) 0x116 ∗
      ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
      ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
      ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
      ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50
  have hm_5d : s5.mem ⊨ futDropBudgetSpec.pre () s5 ∗ (F_5d ∗ R) := by
    dsimp only [futDropBudgetSpec, F_5d]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm5_folded
  refine call_rocl_nopanic_placed (R0 := R)
    (env.kitOk.loadFutDrop (callerProg := lsProg_464 Hk) (callerBlk := 464) (by decide))
    () hpc5 hrun5 hal5 hx30_5 hcrl5 hm_5d ?_
  intro s6 hsteps_5d hpc6 hrun6 hsp6 hal6 hcs6 hm6
  dsimp only [futDropBudgetSpec] at hm6
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm6
  obtain ⟨⟨htr6, hvm_5d⟩, hm6⟩ := hm6
  have hcrl6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem := hcrl5.of_keepsFrozen hsteps_5d.keepsFrozen
  have hsp6' : s6.sp = sp := by rw [hsp6, hsp5]
  have hx20_6 : s6.readReg64 .x20 = box := by rw [cs_x20 hcs6, hx20_5]
  have hx22_6 : s6.readReg64 .x22 = 0#64 + kit.loadFutVtOff := by rw [cs_x22 hcs6, hx22_5]
  have hm6_box : s6.mem ⊨
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗
      ((((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64)) ∗
      ((memRegion (sp + 0x46a#64) 0x116 ∗
        ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
        ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
        ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        kit.storeAt x.ssA st0 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - kit.loadPollStack) ∗
        A.live box kit.loadBoxSize 8 ∗
        shimFramePlaced kit ikit ist0 ctl x s0 v50) ∗ R)) := by
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm6
  have hm6_mem := Satisfies.mono
    (sepConj_mono_left (kit.loadBoxAt_memRegion box x.ssA x.remA 1#8)) hm6_box
  let F_5e : SepProp :=
    memRegion box kit.loadBoxSize ∗ A.live box kit.loadBoxSize 8 ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
      ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
      ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50
  have hm_5e : s6.mem ⊨
      (((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64)) ∗ (F_5e ∗ R) := by
    dsimp only [F_5e]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm6_mem
  refine SegExitBudget.of_sepWP (R0 := R) hm_5e
    (segLoad_e1_to_dealloc_wp_vm kit hpc6 hrun6 hsp6' hal6 hx20_6 hx22_6) ?_
  rintro s7 P7 _ hsteps_5e hpc7 hrun7 hm7
    ⟨hvm_5e, rfl, hsp7, hal7, htr7, hx0_7, hx1_7, hx2_7, hx30_7,
      hx19_7, hx29_7, hvregs_7, hx24_7, hx27_7, hx21_7, hx23_7, hx25_7, hx28_7⟩
  have hcrl7 : StoreKit.LibsignalCodeRoLoaded lsmpl s7.mem := hcrl6.of_keepsFrozen hsteps_5e.keepsFrozen
  have hvm_2_7 : VmPreserved sf2 s7 :=
    hvm_5a.trans (hvm_5b.trans (hvm_5c.trans (hvm_5d.trans hvm_5e)))
  let F_5f : SepProp :=
    loadVtablesAt kit ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - allocHookStack) ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50
  have hm_5f : s7.mem ⊨
      (rustCliDeallocBudgetSpec M A lim).pre (box, kit.loadBoxSize, 8, st2) s7 ∗ (F_5f ∗ R) := by
    dsimp only [rustCliDeallocBudgetSpec, F_5f, F_5e, loadVtablesAt] at hm7 ⊢
    rw [← A.pool_transport lim st2 sf2 s7 hvm_2_7] at hm7
    have hstk := stack_encSub_poll_to_dealloc_eq kit ikit hsub (hsp7 : s7.sp = sp)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_7, by rw [hx1_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kit.loadBoxSize_lt],
      by rw [hx2_7]; rfl,
      by rw [hx30_7]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 464 0x158#64 (by decide) (by decide)⟩, ?_⟩
    refine Satisfies.mono ?_ hm7
    have hpull_stk :
        (((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
          ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64)) ∗
        ((memRegion box kit.loadBoxSize ∗ A.live box kit.loadBoxSize 8 ∗
          memRegion (sp + 0x46a#64) 0x116 ∗
          ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
          ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
          ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
          memRegion (sp + 0x580#64) 368 ∗
          ((sp + 0x6f8#64) ↦ₛ tail) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
          LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
          kit.storeAt x.ssA st0 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          A.pool lim st2 s7 ∗ stackAt sp kit.loadPollStack ∗
          memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
            (encSubStackV kit ikit - kit.loadPollStack) ∗
          shimFramePlaced kit ikit ist0 ctl x s0 v50) ∗ R) =
        (memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
            (encSubStackV kit ikit - kit.loadPollStack) ∗
          stackAt sp kit.loadPollStack) ∗
        ((memRegion box kit.loadBoxSize ∗ A.live box kit.loadBoxSize 8 ∗ A.pool lim st2 s7) ∗
          ((((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
            ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
            ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
            ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff))) ∗
            memRegion (sp + 0x46a#64) 0x116 ∗
            memRegion (sp + 0x580#64) 368 ∗
            ((sp + 0x6f8#64) ↦ₛ tail) ∗
            ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
            LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
            kit.storeAt x.ssA st0 ∗
            protocolAddressAt A.repAlloc x.rem x.remA ∗
            shimFramePlaced kit ikit ist0 ctl x s0 v50) ∗ R) := by
      sep_ac_rfl
    rw [hpull_stk, hstk]
    exact Entails.of_eq (by sep_ac_rfl)
  refine call_nopanic_placed (R0 := R) (dealloc_budget_ok env.toEncEnvBudget)
    (box, kit.loadBoxSize, 8, st2) hpc7 hrun7 hal7 hx30_7 hm_5f ?_
  intro s8 hsteps_5f hpc8 hrun8 hsp8 hal8 hcs8 hm8
  dsimp only [rustCliDeallocBudgetSpec] at hm8
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm8
  obtain ⟨⟨hacp8, _⟩, hm8⟩ := hm8
  have htr8 : s8.trace = s7.trace := hacp8.2.1
  have hbud3 := hbud2.advance rfl
  set st3 := M.stepEvents (rustDeallocEvents kit.loadBoxSize 8) st2
  have hcrl8 : StoreKit.LibsignalCodeRoLoaded lsmpl s8.mem := hcrl7.of_keepsFrozen hsteps_5f.keepsFrozen
  have hsp8' : s8.sp = sp := by rw [hsp8, hsp7]
  have hx24_8 : s8.readReg64 .x24 = w0 := by
    rw [cs_x24 hcs8, hx24_7, cs_x24 hcs6, hx24_5, cs_x24 hcs4, hx24_3]
  have hm_5g : s8.mem ⊨ emp ∗ ((A.pool lim st3 s8 ∗ stackAt s7.sp allocHookStack ∗ F_5f) ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm8
  refine SegExitBudget.of_sepWP (R0 := R) hm_5g
    (segLoad_e1_tail_wp_vm hpc8 hrun8 hsp8' hal8 hx24_8) ?_
  rintro sf Pf _ hsteps_5g hpcf hrunf hmf
    ⟨hvm_5g, rfl, hspf, half, htrf, hx19f, hx29f, hvregsf,
      hx24f, hx27f, hx21f, hx23f, hx25f, hx26f, hx28f, hpsf⟩
  have hcrlf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl8.of_keepsFrozen hsteps_5g.keepsFrozen
  have hm_out : sf.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st3 sf ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R := by
    rw [← A.pool_transport lim st3 s8 sf hvm_5g] at hmf
    have hstk_back := stack_encSub_dealloc_back_eq kit ikit hsub (hsp7 : s7.sp = sp)
    have hsp_split := encSubStack_split_extra_placed kit st0 ikit ist0 x s0 hsp_le
    dsimp only [F_5f, shimFramePlaced, dispatchFramePlaced, sp] at hmf hstk_back ⊢
    rw [emp_sepConj] at hmf
    refine Satisfies.mono ?_ hmf
    refine sepConj_mono_left ?_
    have hperm1 :
        (A.pool lim st3 sf ∗ stackAt s7.sp allocHookStack ∗
            (loadVtablesAt kit ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
              kit.storeAt x.ssA st0 ∗
              protocolAddressAt A.repAlloc x.rem x.remA ∗
              memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
                (encSubStackV kit ikit - allocHookStack) ∗
              (nowAt s0.sp x.now ∗
                encSavedRegs s0.sp s0 ∗
                memRegion (s0.sp - 0xbe0#64) 0x50 ∗
                ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
                encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
                ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
                memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
                ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
                memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
                memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
                (x.ptA ↦ₛ x.ptext) ∗
                protocolAddressAt A.repAlloc x.loc x.locA ∗
                memRegion x.ret 248 ∗
                cliTapeAfter ctl x.cur x.rest 0 ∗
                FromRecordCallees.lsLogOff ∗
                ikit.identityAt x.idA ist0))) =
        (memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
            (encSubStackV kit ikit - allocHookStack) ∗
          stackAt s7.sp allocHookStack) ∗
        (kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          A.pool lim st3 sf ∗ loadVtablesAt kit ∗
          nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          memRegion x.ret 248 ∗
          cliTapeAfter ctl x.cur x.rest 0 ∗
          FromRecordCallees.lsLogOff) := by
      sep_ac_rfl
    rw [hperm1, hstk_back]
    have hperm2 :
        stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) ∗
          (kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0) =
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
          stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) := by sep_ac_rfl
    rw [← sepConj_assoc, hperm2]
    refine Entails.trans (sepConj_mono_left hsp_split) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine hcont sf st3 sp ans w0 w1 w2 w3 w4 w5 w6 v50 tail hbud3 rfl
    hpcf ⟨hrunf, hspf, hal0, half, ?_, ?_, hcrlf, ?_⟩
    ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
    hw0_ne htail_len hl ?_ hx24f ?_ ?_ ?_ ?_ hx26f ?_ hpsf hm_out
  · rw [hx29f, cs_x29 hcs8, hx29_7, cs_x29 hcs6, hx29_5, cs_x29 hcs4, hx29_3, cs_x29 hcs2, hx29m2, cs_x29 hcs1, hx29m]
  · rw [hx19f, cs_x19 hcs8, hx19_7, cs_x19 hcs6, hx19_5, cs_x19 hcs4, hx19_3, cs_x19 hcs2, hx19m2, cs_x19 hcs1, hx19m]
  · rw [hvregsf, cs_vregs hcs8, hvregs_7, cs_vregs hcs6, hvregs_5, cs_vregs hcs4, hvregs_3, cs_vregs hcs2, hvregsm2, cs_vregs hcs1, hvregsm]
  · rw [htrf, htr8, htr7, htr6, htr5, htr4.2, htr3, htr2, htrm2, htr1, htrm]
  · rw [hx27f, cs_x27 hcs8, hx27_7, cs_x27 hcs6, hx27_5, cs_x27 hcs4, hx27_3]
  · rw [hx21f, cs_x21 hcs8, hx21_7, cs_x21 hcs6, hx21_5, cs_x21 hcs4, hx21_3]
  · rw [hx23f, cs_x23 hcs8, hx23_7, cs_x23 hcs6, hx23_5, cs_x23 hcs4, hx23_3]
  · rw [hx25f, cs_x25 hcs8, hx25_7, cs_x25 hcs6, hx25_5, cs_x25 hcs4, hx25_3]
  · rw [hx28f, cs_x28 hcs8, hx28_7, cs_x28 hcs6, hx28_5, cs_x28 hcs4, hx28_3]

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlacedBudget
