/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.EvictOldestKey
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded `EvictOldestKey` Sub-Segment (Block 24)

Proves `EvictOldestKeyPlacedSpec` under `RustCliAllocBudget M` and `SeamBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.EvictOldestKeyBudget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (
  ChainKey MessageKeyGenerator RatchetState ReceiverChain maxMessageKeys
)
open CryptoVerification (
  LibsignalPlacement blkLib_24 blkLib_eq_24 blkPC_24 blkPl_24 lsLogFilterAddr lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost MessageKeyGhost RatchetGhost
)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkLoopHeap_placed_eq_at cmkRustDeallocSym cmk_hook_ok_of_mem
)
open CryptoVerification.LibsignalSession.StoreLoop (
  cap_add_one_ne_zero evictOldestKeyFootprint evictOldestKeyFrameAt
  evictOldestKeyHeapAt_entails_evictOldestKeyFootprint evictOldestKeyPostFootprint
  evictOldestKeyPost_entails_cmkLoopHeapAt msgKeyPopSlots newMsgKeyGhost pinDealloc
  seed_cap_ne_zero updatedRatchetState
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks
)
open LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.DefsBudget (
  ConcatEnv EvictOldestKeyPlacedSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

attribute [local irreducible] Program.fetch Program.externAt?

private theorem blk24_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 (blkLib_24).text = true := rfl

private theorem msgKeyPopSlots_208000_eq (gk : MessageKeyGhost × MessageKeyGenerator)
    (mkPtr1 : BitVec 64) :
    msgKeyPopSlots gk (mkPtr1 + 208000#64) =
      ((mkPtr1 + 208000#64) ↦₆₄ gk.1.cipher.cap) ∗
      ((mkPtr1 + 208008#64) ↦₆₄ gk.1.cipher.ptr) ∗
      ((mkPtr1 + 208016#64) ↦₆₄ 0#64) ∗
      ((mkPtr1 + 208024#64) ↦₆₄ gk.1.mac.cap) ∗
      ((mkPtr1 + 208032#64) ↦₆₄ gk.1.mac.ptr) ∗
      ((mkPtr1 + 208040#64) ↦₆₄ 0#64) ∗
      ((mkPtr1 + 208048#64) ↦₆₄ gk.1.iv.cap) ∗
      ((mkPtr1 + 208056#64) ↦₆₄ gk.1.iv.ptr) ∗
      ((mkPtr1 + 208064#64) ↦₆₄ 0#64) ∗
      ((mkPtr1 + 208072#64) ↦₆₄ gk.1.seed.cap) ∗
      ((mkPtr1 + 208080#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((mkPtr1 + 208088#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      ((mkPtr1 + 208096#64) ↦₃₂ gk.2.counter) ∗
      memRegion (mkPtr1 + 208100#64) 4 := by
  unfold msgKeyPopSlots
  have h8 : mkPtr1 + 208000#64 + 8#64 = mkPtr1 + 208008#64 := by bv_arith
  have h16 : mkPtr1 + 208000#64 + 16#64 = mkPtr1 + 208016#64 := by bv_arith
  have h24 : mkPtr1 + 208000#64 + 24#64 = mkPtr1 + 208024#64 := by bv_arith
  have h32 : mkPtr1 + 208000#64 + 32#64 = mkPtr1 + 208032#64 := by bv_arith
  have h40 : mkPtr1 + 208000#64 + 40#64 = mkPtr1 + 208040#64 := by bv_arith
  have h48 : mkPtr1 + 208000#64 + 48#64 = mkPtr1 + 208048#64 := by bv_arith
  have h56 : mkPtr1 + 208000#64 + 56#64 = mkPtr1 + 208056#64 := by bv_arith
  have h64 : mkPtr1 + 208000#64 + 64#64 = mkPtr1 + 208064#64 := by bv_arith
  have h72 : mkPtr1 + 208000#64 + 72#64 = mkPtr1 + 208072#64 := by bv_arith
  have h80 : mkPtr1 + 208000#64 + 80#64 = mkPtr1 + 208080#64 := by bv_arith
  have h88 : mkPtr1 + 208000#64 + 88#64 = mkPtr1 + 208088#64 := by bv_arith
  have h96 : mkPtr1 + 208000#64 + 96#64 = mkPtr1 + 208096#64 := by bv_arith
  have h100 : mkPtr1 + 208000#64 + 100#64 = mkPtr1 + 208100#64 := by bv_arith
  rw [h8, h16, h24, h32, h40, h48, h56, h64, h72, h80, h88, h96, h100]

local macro "dealloc_post_norm" : tactic => `(tactic| (
  obtain ⟨_, _, _, _, _, _, _⟩ := ‹AllocCallPreserved _ _›
  (conv => arg 4; arg 2; arg 1; arg 1; simp only [wp_norm, arm64_norm, *])
))

local macro "dealloc_post_norm_append" : tactic => `(tactic| (
  obtain ⟨_, _, _, _, _, _, _⟩ := ‹AllocCallPreserved _ _›
  (conv => arg 4; arg 2; arg 1; arg 1; simp only [wp_norm, arm64_norm, *])
  rw [← AllocCostModel.stepEvents_append]
  (conv => arg 4; simp only [← List.append_assoc])
))

local macro "evict_step_to_dealloc" H:ident hcip_add1:ident hseed_cap_ne:ident
    hcip0:ident hmac0:ident hiv0:ident : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := (blkPC_24).rebase (blkPl_24).base (hooksException $H))
    blkLib_eq_24 blk24_noSvc0 (mid := lsρ cmkRustDeallocSym)
  intro _m_strip
  wp_steps
  try (wp_if _hbr <;> try (exfalso; first
    | exact $hcip_add1 _hbr | exact $hseed_cap_ne _hbr
    | exact $hcip0 _hbr | exact _hbr $hcip0
    | exact $hmac0 _hbr | exact _hbr $hmac0
    | exact $hiv0 _hbr | exact _hbr $hiv0))
  wp_steps
  try (wp_if _hbr <;> try (exfalso; first
    | exact $hcip_add1 _hbr | exact $hseed_cap_ne _hbr
    | exact $hcip0 _hbr | exact _hbr $hcip0
    | exact $hmac0 _hbr | exact _hbr $hmac0
    | exact $hiv0 _hbr | exact _hbr $hiv0))
  wp_steps
  try (wp_if _hbr <;> try (exfalso; first
    | exact $hcip_add1 _hbr | exact $hseed_cap_ne _hbr
    | exact $hcip0 _hbr | exact _hbr $hcip0
    | exact $hmac0 _hbr | exact _hbr $hmac0
    | exact $hiv0 _hbr | exact _hbr $hiv0))
  wp_steps
  try (wp_if _hbr <;> try (exfalso; first
    | exact $hcip_add1 _hbr | exact $hseed_cap_ne _hbr
    | exact $hcip0 _hbr | exact _hbr $hcip0
    | exact $hmac0 _hbr | exact _hbr $hmac0
    | exact $hiv0 _hbr | exact _hbr $hiv0))
  wp_steps
  try (wp_if _hbr <;> try (exfalso; first
    | exact $hcip_add1 _hbr | exact $hseed_cap_ne _hbr
    | exact $hcip0 _hbr | exact _hbr $hcip0
    | exact $hmac0 _hbr | exact _hbr $hmac0
    | exact $hiv0 _hbr | exact _hbr $hiv0))
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm, *])) (hnext := ?_)
))

private def evictOldestKeyPostPred [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ConsumeMessageKeyGhost) (st : M.σ) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s sf : State)
    (P_f : SepProp) : Prop :=
  ∃ evs : List AllocEvent,
    FreeOnlyEvs evs ∧
    (sf.mem ⊨ P_f ∗ R →
      sf.mem ⊨ evictOldestKeyPostFootprint (A.atState lim (M.stepEvents evs st) sf)
        chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗ R) ∧
    sf.sp = s0.sp - 480#64 ∧
    sf.spAligned = true ∧
    (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
    sf.readReg64 .x19 = 1#64 ∧
    sf.readReg64 .x21 = x.ckA ∧
    sf.readReg64 .x22 = x.theirA ∧
    sf.readReg64 .x23 = x.self ∧
    sf.readReg64 .x27 = s0.sp - 224#64 ∧
    sf.readReg64 .x29 = s0.sp - 96#64

private theorem evictOldestKey_00_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (x : ConsumeMessageKeyGhost) (st : M.σ) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1020#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp0_align : s0.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA) (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self) (hx25 : s.readReg64 .x25 = chainPtr)
    (hx26 : s.readReg64 .x26 = 2000#64)
    (hseed_ne : gk.2.seed ≠ []) (hcip_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (hcip0 : gk.1.cipher.cap = 0#64) (hmac0 : gk.1.mac.cap = 0#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1140#64) s
      (evictOldestKeyFootprint (A.atState lim st s) chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64))
      (evictOldestKeyPostPred A lim x st chainPtr mkCap1 mkPtr1 gk R s0 s) := by
  unfold evictOldestKeyPostPred evictOldestKeyFootprint evictOldestKeyPostFootprint pinDealloc
  simp only [msgKeyPopSlots_208000_eq, RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  have hdealloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) := cmk_hook_ok_of_mem hA.2.1
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have ⟨hcip_add1, _⟩ := cap_add_one_ne_zero hcip_lt
  have hseed_cap_ne : gk.1.seed.cap ≠ 0#64 := seed_cap_ne_zero hseed_ne hseed_le
  simp only [hcip0, hmac0, hseed_cap_ne, ↓reduceIte, emp_sepConj, sepConj_assoc]
  by_cases hiv0 : gk.1.iv.cap = 0#64
  · simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1, st)
    dealloc_post_norm
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨rustDeallocEvents gk.1.seed.cap.toNat 1,
        FreeOnlyEvs.singleton 1 gk.1.seed.cap.toNat,
        fun hm => Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  · simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.iv.ptr, gk.1.iv.cap.toNat, 1, st)
    dealloc_post_norm
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.iv.cap.toNat 1) st)
    dealloc_post_norm_append
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨rustDeallocEvents gk.1.iv.cap.toNat 1 ++ rustDeallocEvents gk.1.seed.cap.toNat 1,
        FreeOnlyEvs.append
          (FreeOnlyEvs.singleton 1 gk.1.iv.cap.toNat)
          (FreeOnlyEvs.singleton 1 gk.1.seed.cap.toNat),
        fun hm => Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩

private theorem evictOldestKey_01_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (x : ConsumeMessageKeyGhost) (st : M.σ) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1020#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp0_align : s0.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA) (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self) (hx25 : s.readReg64 .x25 = chainPtr)
    (hx26 : s.readReg64 .x26 = 2000#64)
    (hseed_ne : gk.2.seed ≠ []) (hcip_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (hcip0 : gk.1.cipher.cap = 0#64) (hmac0 : ¬ gk.1.mac.cap = 0#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1140#64) s
      (evictOldestKeyFootprint (A.atState lim st s) chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64))
      (evictOldestKeyPostPred A lim x st chainPtr mkCap1 mkPtr1 gk R s0 s) := by
  unfold evictOldestKeyPostPred evictOldestKeyFootprint evictOldestKeyPostFootprint pinDealloc
  simp only [msgKeyPopSlots_208000_eq, RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  have hdealloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) := cmk_hook_ok_of_mem hA.2.1
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have ⟨hcip_add1, _⟩ := cap_add_one_ne_zero hcip_lt
  have hseed_cap_ne : gk.1.seed.cap ≠ 0#64 := seed_cap_ne_zero hseed_ne hseed_le
  simp only [hcip0, hmac0, hseed_cap_ne, ↓reduceIte, emp_sepConj, sepConj_assoc]
  by_cases hiv0 : gk.1.iv.cap = 0#64
  · simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.mac.ptr, gk.1.mac.cap.toNat, 1, st)
    dealloc_post_norm
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.mac.cap.toNat 1) st)
    dealloc_post_norm_append
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨rustDeallocEvents gk.1.mac.cap.toNat 1 ++ rustDeallocEvents gk.1.seed.cap.toNat 1,
        FreeOnlyEvs.append
          (FreeOnlyEvs.singleton 1 gk.1.mac.cap.toNat)
          (FreeOnlyEvs.singleton 1 gk.1.seed.cap.toNat),
        fun hm => Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  · simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.mac.ptr, gk.1.mac.cap.toNat, 1, st)
    dealloc_post_norm
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.iv.ptr, gk.1.iv.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.mac.cap.toNat 1) st)
    dealloc_post_norm_append
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.mac.cap.toNat 1 ++
        rustDeallocEvents gk.1.iv.cap.toNat 1) st)
    dealloc_post_norm_append
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨(rustDeallocEvents gk.1.mac.cap.toNat 1 ++ rustDeallocEvents gk.1.iv.cap.toNat 1) ++
          rustDeallocEvents gk.1.seed.cap.toNat 1,
        FreeOnlyEvs.append
          (FreeOnlyEvs.append
            (FreeOnlyEvs.singleton 1 gk.1.mac.cap.toNat)
            (FreeOnlyEvs.singleton 1 gk.1.iv.cap.toNat))
          (FreeOnlyEvs.singleton 1 gk.1.seed.cap.toNat),
        fun hm => Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩

private theorem evictOldestKey_10_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (x : ConsumeMessageKeyGhost) (st : M.σ) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1020#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp0_align : s0.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA) (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self) (hx25 : s.readReg64 .x25 = chainPtr)
    (hx26 : s.readReg64 .x26 = 2000#64)
    (hseed_ne : gk.2.seed ≠ []) (hcip_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (hcip0 : ¬ gk.1.cipher.cap = 0#64) (hmac0 : gk.1.mac.cap = 0#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1140#64) s
      (evictOldestKeyFootprint (A.atState lim st s) chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64))
      (evictOldestKeyPostPred A lim x st chainPtr mkCap1 mkPtr1 gk R s0 s) := by
  unfold evictOldestKeyPostPred evictOldestKeyFootprint evictOldestKeyPostFootprint pinDealloc
  simp only [msgKeyPopSlots_208000_eq, RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  have hdealloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) := cmk_hook_ok_of_mem hA.2.1
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have ⟨hcip_add1, _⟩ := cap_add_one_ne_zero hcip_lt
  have hseed_cap_ne : gk.1.seed.cap ≠ 0#64 := seed_cap_ne_zero hseed_ne hseed_le
  simp only [hcip0, hmac0, hseed_cap_ne, ↓reduceIte, emp_sepConj, sepConj_assoc]
  by_cases hiv0 : gk.1.iv.cap = 0#64
  · simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.cipher.ptr, gk.1.cipher.cap.toNat, 1, st)
    dealloc_post_norm
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.cipher.cap.toNat 1) st)
    dealloc_post_norm_append
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨rustDeallocEvents gk.1.cipher.cap.toNat 1 ++ rustDeallocEvents gk.1.seed.cap.toNat 1,
        FreeOnlyEvs.append
          (FreeOnlyEvs.singleton 1 gk.1.cipher.cap.toNat)
          (FreeOnlyEvs.singleton 1 gk.1.seed.cap.toNat),
        fun hm => Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  · simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.cipher.ptr, gk.1.cipher.cap.toNat, 1, st)
    dealloc_post_norm
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.iv.ptr, gk.1.iv.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.cipher.cap.toNat 1) st)
    dealloc_post_norm_append
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.cipher.cap.toNat 1 ++
        rustDeallocEvents gk.1.iv.cap.toNat 1) st)
    dealloc_post_norm_append
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨(rustDeallocEvents gk.1.cipher.cap.toNat 1 ++ rustDeallocEvents gk.1.iv.cap.toNat 1) ++
          rustDeallocEvents gk.1.seed.cap.toNat 1,
        FreeOnlyEvs.append
          (FreeOnlyEvs.append
            (FreeOnlyEvs.singleton 1 gk.1.cipher.cap.toNat)
            (FreeOnlyEvs.singleton 1 gk.1.iv.cap.toNat))
          (FreeOnlyEvs.singleton 1 gk.1.seed.cap.toNat),
        fun hm => Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩

private theorem evictOldestKey_11_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (x : ConsumeMessageKeyGhost) (st : M.σ) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1020#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp0_align : s0.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA) (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self) (hx25 : s.readReg64 .x25 = chainPtr)
    (hx26 : s.readReg64 .x26 = 2000#64)
    (hseed_ne : gk.2.seed ≠ []) (hcip_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (hcip0 : ¬ gk.1.cipher.cap = 0#64) (hmac0 : ¬ gk.1.mac.cap = 0#64) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1140#64) s
      (evictOldestKeyFootprint (A.atState lim st s) chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64))
      (evictOldestKeyPostPred A lim x st chainPtr mkCap1 mkPtr1 gk R s0 s) := by
  unfold evictOldestKeyPostPred evictOldestKeyFootprint evictOldestKeyPostFootprint pinDealloc
  simp only [msgKeyPopSlots_208000_eq, RustCliAllocBudget.atState_pool, RustCliAllocBudget.atState_live]
  have hdealloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim) := cmk_hook_ok_of_mem hA.2.1
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have ⟨hcip_add1, _⟩ := cap_add_one_ne_zero hcip_lt
  have hseed_cap_ne : gk.1.seed.cap ≠ 0#64 := seed_cap_ne_zero hseed_ne hseed_le
  simp only [hcip0, hmac0, hseed_cap_ne, ↓reduceIte, emp_sepConj, sepConj_assoc]
  by_cases hiv0 : gk.1.iv.cap = 0#64
  · simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.cipher.ptr, gk.1.cipher.cap.toNat, 1, st)
    dealloc_post_norm
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.mac.ptr, gk.1.mac.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.cipher.cap.toNat 1) st)
    dealloc_post_norm_append
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.cipher.cap.toNat 1 ++
        rustDeallocEvents gk.1.mac.cap.toNat 1) st)
    dealloc_post_norm_append
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨(rustDeallocEvents gk.1.cipher.cap.toNat 1 ++ rustDeallocEvents gk.1.mac.cap.toNat 1) ++
          rustDeallocEvents gk.1.seed.cap.toNat 1,
        FreeOnlyEvs.append
          (FreeOnlyEvs.append
            (FreeOnlyEvs.singleton 1 gk.1.cipher.cap.toNat)
            (FreeOnlyEvs.singleton 1 gk.1.mac.cap.toNat))
          (FreeOnlyEvs.singleton 1 gk.1.seed.cap.toNat),
        fun hm => Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  · simp only [hiv0, ↓reduceIte, emp_sepConj, sepConj_assoc]
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.cipher.ptr, gk.1.cipher.cap.toNat, 1, st)
    dealloc_post_norm
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.mac.ptr, gk.1.mac.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.cipher.cap.toNat 1) st)
    dealloc_post_norm_append
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.iv.ptr, gk.1.iv.cap.toNat, 1,
      M.stepEvents (rustDeallocEvents gk.1.cipher.cap.toNat 1 ++
        rustDeallocEvents gk.1.mac.cap.toNat 1) st)
    dealloc_post_norm_append
    evict_step_to_dealloc H hcip_add1 hseed_cap_ne hcip0 hmac0 hiv0
    wp_call hdealloc (gk.1.seed.ptr, gk.1.seed.cap.toNat, 1,
      M.stepEvents ((rustDeallocEvents gk.1.cipher.cap.toNat 1 ++
        rustDeallocEvents gk.1.mac.cap.toNat 1) ++
        rustDeallocEvents gk.1.iv.cap.toNat 1) st)
    dealloc_post_norm_append
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨((rustDeallocEvents gk.1.cipher.cap.toNat 1 ++ rustDeallocEvents gk.1.mac.cap.toNat 1) ++
          rustDeallocEvents gk.1.iv.cap.toNat 1) ++
          rustDeallocEvents gk.1.seed.cap.toNat 1,
        FreeOnlyEvs.append
          (FreeOnlyEvs.append
            (FreeOnlyEvs.append
              (FreeOnlyEvs.singleton 1 gk.1.cipher.cap.toNat)
              (FreeOnlyEvs.singleton 1 gk.1.mac.cap.toNat))
            (FreeOnlyEvs.singleton 1 gk.1.iv.cap.toNat))
          (FreeOnlyEvs.singleton 1 gk.1.seed.cap.toNat),
        fun hm => Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [State.spAligned, wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩

theorem evictOldestKey_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hA : CmkAllocHooks A lim H)
    (x : ConsumeMessageKeyGhost) (st : M.σ) (chainPtr mkCap1 mkPtr1 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1020#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (_hsp_align : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx25 : s.readReg64 .x25 = chainPtr)
    (hx26 : s.readReg64 .x26 = 2000#64)
    (hseed_ne : gk.2.seed ≠ [])
    (hcip_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (_hmac_lt : gk.1.mac.cap.toNat < 2 ^ 63)
    (_hiv_lt : gk.1.iv.cap.toNat < 2 ^ 63)
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (_hseed_lt : gk.1.seed.cap.toNat < 2 ^ 63) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1140#64) s
      (evictOldestKeyFootprint (A.atState lim st s) chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64))
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ evictOldestKeyPostFootprint (A.atState lim (M.stepEvents evs st) sf)
              chainPtr mkCap1 mkPtr1 gk (s0.sp - 480#64) ∗ R) ∧
          sf.sp = s0.sp - 480#64 ∧
          sf.spAligned = true ∧
          (sf.trace = s.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
          sf.readReg64 .x19 = 1#64 ∧
          sf.readReg64 .x21 = x.ckA ∧
          sf.readReg64 .x22 = x.theirA ∧
          sf.readReg64 .x23 = x.self ∧
          sf.readReg64 .x27 = s0.sp - 224#64 ∧
          sf.readReg64 .x29 = s0.sp - 96#64) := by
  by_cases hcip0 : gk.1.cipher.cap = 0#64
  · by_cases hmac0 : gk.1.mac.cap = 0#64
    · exact evictOldestKey_00_wp hA x st chainPtr mkCap1 mkPtr1 gk R s0 s
        hpc hrun hsp hsp0_align hx29 hx19 hx21 hx22 hx23 hx25 hx26 hseed_ne hcip_lt hseed_le hcip0 hmac0
    · exact evictOldestKey_01_wp hA x st chainPtr mkCap1 mkPtr1 gk R s0 s
        hpc hrun hsp hsp0_align hx29 hx19 hx21 hx22 hx23 hx25 hx26 hseed_ne hcip_lt hseed_le hcip0 hmac0
  · by_cases hmac0 : gk.1.mac.cap = 0#64
    · exact evictOldestKey_10_wp hA x st chainPtr mkCap1 mkPtr1 gk R s0 s
        hpc hrun hsp hsp0_align hx29 hx19 hx21 hx22 hx23 hx25 hx26 hseed_ne hcip_lt hseed_le hcip0 hmac0
    · exact evictOldestKey_11_wp hA x st chainPtr mkCap1 mkPtr1 gk R s0 s
        hpc hrun hsp hsp0_align hx29 hx19 hx21 hx22 hx23 hx25 hx26 hseed_ne hcip_lt hseed_le hcip0 hmac0

theorem evictOldestKey_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} :
    EvictOldestKeyPlacedSpec F A lim H := by
  intro hA x st_init stB remPost Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr R s0 sB
    hchc_get hSB_full hL
  rcases hSB_full with ⟨hsb, hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, hvregs⟩,
    ⟨hx19, hx21, hx22, hx23, hx25, hx26, _hx28⟩,
    ⟨hci_gc, hcg_eq⟩, hsrk, hmk_len, hgk_len, hmk_cap_le, hmk_cap_lt, hmk_ptr_ne, hmem⟩
  have hci_stc : ci < stc.receiverChains.length := (List.getElem?_eq_some_iff.mp hchc_get).1
  set chainPtr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set gks1 : List (MessageKeyGhost × MessageKeyGenerator) :=
    (newMsgKeyGhost seedPtr, ckc.messageKeys F) :: cg.keys.zip chc.messageKeys
  have hgks1_len : gks1.length = 2000 + 1 := by
    simp [gks1, List.length_zip, hgk_len, hmk_len]
  set gk := gks1[2000]'(by omega)
  have hsplit := Satisfies.mono
    (sepConj_mono_left (evictOldestKeyHeapAt_entails_evictOldestKeyFootprint F
      (A.atState lim stB sB) lsLogFilterAddr x Gc stc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr s0 hmk_len hgk_len)) hmem
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hsplit
  rcases hsplit with ⟨⟨hseed_ne, hcip_lt, _, hmac_lt, _, hiv_lt, _, hseed_le, hseed_lt, _⟩, hmem_pre⟩
  have hpc' : sB.pc = (blkPl_24).base + 1020#64 := hpc
  have hwp := evictOldestKey_placed_wp hA x stB chainPtr mkCap1 mkPtr1 gk
    (evictOldestKeyFrameAt F (A.atState lim stB sB) lsLogFilterAddr x Gc stc ckc ci chc cg
      mkCap1 mkPtr1 seedPtr s0 ∗ R)
    s0 sB hpc' hrun hsp hsp0_align hsp_align hx29 hx19 hx21 hx22 hx23 hx25 hx26
    hseed_ne hcip_lt hmac_lt hiv_lt hseed_le hseed_lt
  rcases hwp.elim hmem_pre hL with ⟨sC, hsteps, ⟨hpc_sC, hrun_sC, P_f, hmf,
    evs, hfree, himp, hsp_sC, hsp_align_sC, ⟨htrace_sC, hvregs_sC⟩,
    hx19_sC, hx21_sC, hx22_sC, hx23_sC, hx27_sC, hx29_sC⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  set stC := M.stepEvents evs stB
  have hframe_eq :
      evictOldestKeyFrameAt F (A.atState lim stB sB) lsLogFilterAddr x Gc stc ckc ci chc cg
        mkCap1 mkPtr1 seedPtr s0 =
      evictOldestKeyFrameAt F (A.atState lim stC sC) lsLogFilterAddr x Gc stc ckc ci chc cg
        mkCap1 mkPtr1 seedPtr s0 := rfl
  have hpost_fp := himp hmf
  rw [hframe_eq, ← sepConj_assoc] at hpost_fp
  set cg' : ChainGhost :=
    { cg with mkCap := mkCap1, mkPtr := mkPtr1,
              keys := (newMsgKeyGhost seedPtr :: cg.keys).take maxMessageKeys }
  have hmem_sC := Satisfies.mono
    (sepConj_mono_left (evictOldestKeyPost_entails_cmkLoopHeapAt F (A.atState lim stC sC) lsLogFilterAddr
      x Gc stc ckc ci chc cg mkCap1 mkPtr1 seedPtr s0 gk
      hci_stc hsrk hmk_len hgk_len hmk_cap_le hmk_cap_lt hmk_ptr_ne))
    hpost_fp
  rw [← cmkLoopHeap_placed_eq_at] at hmem_sC
  have hagree : Gc.AgreeExcept (Gc.setChain ci cg') (some ci) :=
    RatchetGhost.AgreeExcept.setChain Gc hci_gc cg' (by simp [cg', hcg_eq]) (by simp [cg', hcg_eq])
  have hcap_get : ((Gc.setChain ci cg').chains[ci]?.map (·.mkCap)).getD 0#64 = mkCap1 := by
    rw [show (Gc.setChain ci cg').chains = Gc.chains.set ci cg' from rfl,
      List.getElem?_set_self hci_gc]
    rfl
  have hsbC := hsb.step (fun e1 e2 h1 h2 => ⟨e1, e2, rfl, h1, h2⟩) hfree
  refine ⟨sC, hsteps, stC, Gc.setChain ci cg', hagree, hcap_get, hsbC,
    hpc_sC,
    ⟨hrun_sC, hsp_sC, hsp0_align, hsp_align_sC, hx29_sC, htrace_sC.trans htrace,
      hcl.of_keepsFrozen hsteps.keepsFrozen, hvregs_sC.trans hvregs⟩,
    ⟨hx19_sC, hx21_sC, hx22_sC, hx23_sC, hx27_sC⟩,
    hmem_sC⟩

end LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.EvictOldestKeyBudget
