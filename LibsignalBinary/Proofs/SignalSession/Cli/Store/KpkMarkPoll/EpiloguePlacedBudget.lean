/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Epilogue & Error Cleanup for `KpkMarkPoll`

Proves the budget-threaded shared epilogue (`+816`), tail deallocations (`+804`, `+808`), error
cleanup (`+744`), and `Dir::get` error exits (`+196`, `+632`) on Block `578` (`lsProg_578 H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (speWord)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (KpkMarkPollGhost kpkMarkBoxAt kpkMarkOutAt strSpeAt utf8)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_578 blkPl_578 lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (bind_sepWP_state_mark epilogueOut epiloguePre kpkMarkOutAt_readErr_reassemble
   layoutOk_u8_of_ne_zero pointsTo64_eq_word1421At savedCalleeSlots setWidth_32_setWidth_64
   spAligned_sub_f0 speReadHeap sret48_kpk_split strSpeAt_reassemble vecU8Tail vecU8_free_ne
   vecU8_free_zero word1421At)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget RustLayoutOk
   rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)

private theorem bv_sub_add_lit_kpk (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit_kpk BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

private abbrev readErrV28P (fnPtr : BitVec 64) : BitVec 64 :=
  (fnPtr.extractLsb' 0 8).setWidth 64

private abbrev readErrW8P (fnPtr : BitVec 64) : BitVec 64 :=
  BitVec.zeroExtend 64
    (BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.extractLsb' 40 16 fnPtr) |||
        BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.extractLsb' 56 8 fnPtr) <<< 16)))

private abbrev readErrV23P (fnPtr : BitVec 64) : BitVec 64 :=
  (fnPtr.extractLsb' 8 32).setWidth 64 ||| (readErrW8P fnPtr <<< 32)

private theorem readErr_v28_lo_p (fnPtr : BitVec 64) :
    (readErrV28P fnPtr).setWidth 8 = fnPtr.extractLsb' 0 8 := by
  unfold readErrV28P; bv_bits

private theorem readErr_v23_lo_p (fnPtr : BitVec 64) :
    (readErrV23P fnPtr).setWidth 32 = fnPtr.extractLsb' 8 32 := by
  unfold readErrV23P readErrW8P; bv_bits

private theorem readErr_v23_mid_p (fnPtr : BitVec 64) :
    ((readErrV23P fnPtr) >>> 32).setWidth 16 = fnPtr.extractLsb' 40 16 := by
  unfold readErrV23P readErrW8P; bv_bits

private theorem readErr_v23_hi_p (fnPtr : BitVec 64) :
    ((readErrV23P fnPtr) >>> 48).setWidth 8 = fnPtr.extractLsb' 56 8 := by
  unfold readErrV23P readErrW8P; bv_bits

/-- Events emitted when dropping `used`, `seen`, and `file` in `kpk_err_cleanup_2e8_placed`. -/
abbrev kpkErrCleanupEvents (usedCap seenCap fileCap : BitVec 64) : List AllocEvent :=
  optDeallocBufEvents usedCap ++ optDeallocBufEvents seenCap ++ optDeallocBufEvents fileCap

theorem freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

theorem freeOnlyEvs_optDeallocBufEvents (cap : BitVec 64) :
    FreeOnlyEvs (optDeallocBufEvents cap) := by
  unfold optDeallocBufEvents
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap.toNat

theorem freeOnlyEvs_kpkErrCleanupEvents (usedCap seenCap fileCap : BitVec 64) :
    FreeOnlyEvs (kpkErrCleanupEvents usedCap seenCap fileCap) :=
  FreeOnlyEvs.append
    (FreeOnlyEvs.append
      (freeOnlyEvs_optDeallocBufEvents usedCap)
      (freeOnlyEvs_optDeallocBufEvents seenCap))
    (freeOnlyEvs_optDeallocBufEvents fileCap)

/-- Shared epilogue (`+816 .. +888` in Block `578`): writes `[out .. out + 48)`, sets `[fut + 24] := 1`,
restores all saved callee registers and `sp`, and returns to `s0.readReg64 .lr`. -/
theorem kpk_epilogue_330_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (v21 v27 v25 v22 v28 v23 v26 : BitVec 64)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_578).base + 816#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = v21)
    (hx27 : s.readReg64 .x27 = v27)
    (hx25 : s.readReg64 .x25 = v25)
    (hx22 : s.readReg64 .x22 = v22)
    (hx28 : s.readReg64 .x28 = v28)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26)
    (hfoc : P ⊢ epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x v21 v27 v25 v22 v28 v23 v26 ∗ A.pool lim st sf ∗ F) →
      post sf P_f) :
    SepWP (lsProg_578 H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  change SepWP ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P post
  refine SepWP.weaken_pre hfoc ?_
  unfold epiloguePre kpkMarkBoxAt savedCalleeSlots
  rw [sret48_kpk_split x.out]
  unfold word1421At
  kpk_sep_norm
  refine SepWP.exists_elim fun o0 => SepWP.exists_elim fun o1 =>
    SepWP.exists_elim fun o2 => SepWP.exists_elim fun o3 =>
    SepWP.exists_elim fun ob0 => SepWP.exists_elim fun ob14 =>
    SepWP.exists_elim fun ob56 => SepWP.exists_elim fun ob7 =>
    SepWP.exists_elim fun o5 => ?_
  wp_steps_sync_pool (s0.readReg64 .lr)
  apply bind_sepWP_state_mark; intro sf
  apply SepWP.done (by simp only [sf]; kpk_norm) (by simp only [sf]; kpk_norm)
  refine hk sf _ (by simp only [sf]; kpk_norm) (by simp only [sf]; kpk_norm)
    (by unfold CalleeSavedPreserved; simp only [sf]; kpk_norm) ?_
  dsimp only [sf]
  unfold epilogueOut word1421At savedCalleeSlots kpkMarkBoxAt
  kpk_sep_norm
  sep_focus

/-- Tail dealloc at `+808 .. +812`: frees `(x0 = ptr, x1 = cap)` (`cap ≠ 0#64`) and enters `+816`. -/
theorem kpk_free_ptr_328_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (v21 v27 v25 v22 v28 v23 v26 : BitVec 64)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hcap : cap ≠ 0#64) (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63)
    (_hptr : ptr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 808#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = v21)
    (hx27 : s.readReg64 .x27 = v27)
    (hx25 : s.readReg64 .x25 = v25)
    (hx22 : s.readReg64 .x22 = v22)
    (hx28 : s.readReg64 .x28 = v28)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26)
    (hfoc : P ⊢
      bytesAt false ptr bs ∗
      vecU8Tail A.repAlloc cap ptr bs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x v21 v27 v25 v22 v28 v23 v26 ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st) sf ∗ F) →
      post sf P_f) :
    SepWP (lsProg_578 H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  obtain ⟨hcap_pos, hpow1, hcap_hi⟩ := layoutOk_u8_of_ne_zero hcap hlt
  have hlay : RustLayoutOk cap.toNat 1 := ⟨⟨hcap_pos, hpow1, hcap_hi⟩, by decide⟩
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_578 H) hC
  dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack, lsProg_578] at hdealloc
  have hep := @kpk_epilogue_330_placed _ M A lim H
  dsimp only [lsProg_578] at hep
  clear hC
  change SepWP ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P post
  refine SepWP.weaken_pre hfoc ?_
  refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := ptr) hcap hlen hlt) (by sep_focus) ?_
  apply sepWP_seq_lscro hcrl (mid := lsρ lsRustDeallocSymCli)
  wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
  apply SepWP.done (by kpk_norm) (by wp_norm_lhs)
  intro hcrl_da
  apply sepWP_seq_lscro hcrl_da (mid := (blkPl_578).base + 816#64)
  rcases hcrl_da with ⟨hcl_da, hro_da⟩
  wp_call hdealloc (ptr, cap.toNat, 1, st)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro _hcrl_330
  refine hep x (M.stepEvents (rustDeallocEvents cap.toNat 1) st) s0 _
    v21 v27 v25 v22 v28 v23 v26 _
    (stackAt (s0.sp - 0xf0#64) extHookStack ∗ F)
    (by kpk_norm)
    (by kpk_norm)
    hsp_align
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by unfold epiloguePre; (try simp only [arm64_norm]); (try rw [hsp]); kpk_sep_focus)
    fun sf P_f htr_f hsp_f hcs_f hPf =>
      hk sf P_f (htr_f.trans (by kpk_norm)) hsp_f hcs_f
        (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)))

/-- Tail dealloc at `+804 .. +812`: loads `filePtr` from `[sp + 0x18]` (`s0.sp - 0xd8#64`) and
chains into `kpk_free_ptr_328_placed`. -/
theorem kpk_free_file_324_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (v21 v27 v25 v22 v28 v23 v26 : BitVec 64)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hcap : fileCap ≠ 0#64) (hlen : fileBs.length ≤ fileCap.toNat) (hlt : fileCap.toNat < 2 ^ 63)
    (hptr : filePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 804#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx1 : s.readReg64 .x1 = fileCap)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = v21)
    (hx27 : s.readReg64 .x27 = v27)
    (hx25 : s.readReg64 .x25 = v25)
    (hx22 : s.readReg64 .x22 = v22)
    (hx28 : s.readReg64 .x28 = v28)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = v26)
    (hfoc : P ⊢
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      bytesAt false filePtr fileBs ∗
      vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x v21 v27 v25 v22 v28 v23 v26 ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim (M.stepEvents (rustDeallocEvents fileCap.toNat 1) st) sf ∗ F) →
      post sf P_f) :
    SepWP (lsProg_578 H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hfree := @kpk_free_ptr_328_placed _ M A lim H hC
  dsimp only [lsProg_578] at hfree
  clear hC
  change SepWP ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P post
  refine SepWP.weaken_pre hfoc ?_
  apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 808#64)
  wp_steps_sync_pool ((blkPl_578).base + 808#64)
  apply SepWP.done (by kpk_norm) (by wp_norm_lhs)
  intro hcrl_328
  refine hfree x st s0 _ fileCap filePtr fileBs v21 v27 v25 v22 v28 v23 v26 _
    (((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ F)
    hcap hlen hlt hptr
    (by kpk_norm)
    (by kpk_norm)
    hsp_align
    (by kpk_norm)
    hcrl_328
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by unfold epiloguePre; kpk_sep_focus)
    fun sf P_f htr_f hsp_f hcs_f hPf =>
      hk sf P_f (htr_f.trans (by kpk_norm)) hsp_f hcs_f
        (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)))

/-- Shared error cleanup (`+744 .. +812` → `kpk_epilogue_330_placed`) for `reused` and `malformed`:
drops `used`, `seen`, and `file` (`Vec<u8>`), moves `(errPtr, errLen)` into `(x25, x27)` and `9`
into `x26`, runs the epilogue, and reassembles `strSpeAt A.repAlloc x.out tagIdx`. -/
theorem kpk_err_cleanup_2e8_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (tagIdx : Nat) (errPtr : BitVec 64) (errBs : List (BitVec 8))
    (v28 v23 : BitVec 64)
    (usedCap usedPtr : BitVec 64) (usedBs : List (BitVec 8))
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    (herr_pos : 0 < errBs.length) (herr_lt : errBs.length < 2 ^ 63) (herr_ptr : errPtr ≠ 0#64)
    (hu_len : usedBs.length ≤ usedCap.toNat) (hu_lt : usedCap.toNat < 2 ^ 63)
    (_hu_ptr : usedPtr ≠ 0#64)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (_hs_ptr : seenPtr ≠ 0#64)
    (hf_len : fileBs.length ≤ fileCap.toNat) (hf_lt : fileCap.toNat < 2 ^ 63)
    (hf_ptr : filePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 744#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = speWord tagIdx)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 errBs.length)
    (hx23 : s.readReg64 .x23 = v23)
    (hx24 : s.readReg64 .x24 = errPtr)
    (hx25 : s.readReg64 .x25 = seenPtr)
    (hx27 : s.readReg64 .x27 = seenCap)
    (hx28 : s.readReg64 .x28 = v28)
    (hfoc : P ⊢
      ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
      ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
      bytesAt false usedPtr usedBs ∗
      vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
      bytesAt false seenPtr seenBs ∗
      vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
      bytesAt false filePtr fileBs ∗
      vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
      A.repAlloc.live errPtr errBs.length 1 ∗ (errPtr ↦ₛ errBs) ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ strSpeAt A.repAlloc x.out tagIdx ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim (M.stepEvents (kpkErrCleanupEvents usedCap seenCap fileCap) st) sf ∗ F) →
      post sf P_f) :
    SepWP (lsProg_578 H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_578 H) hC
  dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack, lsProg_578] at hdealloc
  have hep := @kpk_epilogue_330_placed _ M A lim H
  have hfreeFile := @kpk_free_file_324_placed _ M A lim H hC
  dsimp only [lsProg_578] at hep hfreeFile
  clear hC
  let st_u : M.σ := M.stepEvents (optDeallocBufEvents usedCap) st
  let st_s : M.σ := M.stepEvents (optDeallocBufEvents seenCap) st_u
  have hst_f_eq :
      M.stepEvents (optDeallocBufEvents fileCap) st_s =
        M.stepEvents (kpkErrCleanupEvents usedCap seenCap fileCap) st := by
    simp only [st_s, st_u, kpkErrCleanupEvents, M.stepEvents_append]
  change SepWP ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P post
  refine SepWP.weaken_pre hfoc ?_
  have hstep_used : ∀ (su : State) (Q_u : SepProp),
      su.pc = (blkPl_578).base + 764#64 →
      su.status = .Running →
      su.sp = s0.sp - 0xf0#64 →
      LibsignalCodeRoLoaded lsmpl su.mem →
      su.trace = s.trace →
      calleeSavedVRegs su = calleeSavedVRegs s0 →
      su.readReg64 .x19 = x.fut →
      su.readReg64 .x20 = x.out →
      su.readReg64 .x21 = speWord tagIdx →
      su.readReg64 .x22 = BitVec.ofNat 64 errBs.length →
      su.readReg64 .x23 = v23 →
      su.readReg64 .x24 = errPtr →
      su.readReg64 .x25 = seenPtr →
      su.readReg64 .x27 = seenCap →
      su.readReg64 .x28 = v28 →
      (Q_u ⊢
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        bytesAt false filePtr fileBs ∗
        vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
        A.repAlloc.live errPtr errBs.length 1 ∗ (errPtr ↦ₛ errBs) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        epiloguePre s0 x ∗ A.pool lim st_u su ∗ F) →
      SepWP ((blkPC_578).rebase (blkPl_578).base H)
        (s0.readReg64 .lr) su Q_u post := by
    intro su Q_u hpc_u hrun_u hsp_u hcrl_u htr_u hv_u h19 h20 h21 h22 h23 h24 h25 h27 h28 hQu
    have hsp_al_u : su.spAligned = true := spAligned_sub_f0 hsp_align hsp_u
    refine SepWP.weaken_pre hQu ?_
    have hstep_seen : ∀ (ss : State) (Q_s : SepProp),
        ss.pc = (blkPl_578).base + 784#64 →
        ss.status = .Running →
        ss.sp = s0.sp - 0xf0#64 →
        LibsignalCodeRoLoaded lsmpl ss.mem →
        ss.trace = su.trace →
        calleeSavedVRegs ss = calleeSavedVRegs s0 →
        ss.readReg64 .x19 = x.fut →
        ss.readReg64 .x20 = x.out →
        ss.readReg64 .x21 = speWord tagIdx →
        ss.readReg64 .x22 = BitVec.ofNat 64 errBs.length →
        ss.readReg64 .x23 = v23 →
        ss.readReg64 .x24 = errPtr →
        ss.readReg64 .x28 = v28 →
        (Q_s ⊢
          ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
          ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
          ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          bytesAt false filePtr fileBs ∗
          vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
          A.repAlloc.live errPtr errBs.length 1 ∗ (errPtr ↦ₛ errBs) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          epiloguePre s0 x ∗ A.pool lim st_s ss ∗ F) →
        SepWP ((blkPC_578).rebase (blkPl_578).base H)
          (s0.readReg64 .lr) ss Q_s post := by
      intro ss Q_s hpc_s hrun_s hsp_s hcrl_s htr_s hv_s s19 s20 s21 s22 s23 s24 s28 hQs
      have hsp_al_s : ss.spAligned = true := spAligned_sub_f0 hsp_align hsp_s
      refine SepWP.weaken_pre hQs ?_
      by_cases hfcap : fileCap = 0#64
      · subst hfcap
        have hst_f0 : st_s = M.stepEvents (kpkErrCleanupEvents usedCap seenCap 0#64) st := by
          rw [← hst_f_eq]
          simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
        refine SepWP.fold (vecU8_free_zero A.repAlloc filePtr hf_len) (by sep_focus) ?_
        apply sepWP_seq_lscro hcrl_s (mid := (blkPl_578).base + 816#64)
        wp_steps_sync_pool ((blkPl_578).base + 816#64)
        apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
        intro _hcrl_330
        refine hep x st_s s0 _ (speWord tagIdx) (BitVec.ofNat 64 errBs.length) errPtr
          (BitVec.ofNat 64 errBs.length) v28 v23 9#64 _
          (((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗ ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
            ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ 0#64) ∗
            A.repAlloc.live errPtr errBs.length 1 ∗ (errPtr ↦ₛ errBs) ∗
            stackAt (s0.sp - 0xf0#64) extHookStack ∗ F)
          (by kpk_norm)
          (by kpk_norm)
          hsp_align
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by unfold epiloguePre; kpk_sep_focus)
          fun sf P_f htr_f hsp_f hcs_f hPf =>
            hk sf P_f (htr_f.trans ((by kpk_norm : _ = ss.trace).trans
              (htr_s.trans htr_u))) hsp_f hcs_f <| by
              refine Entails.trans hPf ?_
              rw [hst_f0]
              unfold epilogueOut
              refine Entails.trans ?_
                (sepConj_mono_left
                  (strSpeAt_reassemble A.repAlloc x.out errPtr 9#64 tagIdx errBs
                    (v28.setWidth 8) (v23.setWidth 32)
                    ((v23 >>> 32).setWidth 16) ((v23 >>> 48).setWidth 8)
                    herr_pos herr_lt herr_ptr))
              sep_focus
      · have hfcap_beq : (fileCap == 0#64) = false := beq_eq_false_iff_ne.mpr hfcap
        have hst_f1 :
            M.stepEvents (rustDeallocEvents fileCap.toNat 1) st_s =
              M.stepEvents (kpkErrCleanupEvents usedCap seenCap fileCap) st := by
          rw [← hst_f_eq]
          simp only [optDeallocBufEvents, hfcap, ↓reduceIte]
        apply sepWP_seq_lscro hcrl_s (mid := (blkPl_578).base + 804#64)
        wp_steps_sync_pool ((blkPl_578).base + 804#64)
        apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
        intro hcrl_324
        refine hfreeFile x st_s s0 _ fileCap filePtr fileBs
          (speWord tagIdx) (BitVec.ofNat 64 errBs.length) errPtr
          (BitVec.ofNat 64 errBs.length) v28 v23 9#64 _
          (((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗ ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
            ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
            A.repAlloc.live errPtr errBs.length 1 ∗ (errPtr ↦ₛ errBs) ∗ F)
          hfcap hf_len hf_lt hf_ptr
          (by kpk_norm)
          (by kpk_norm)
          hsp_align
          (by kpk_norm)
          hcrl_324
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by kpk_norm)
          (by unfold epiloguePre; kpk_sep_focus)
          fun sf P_f htr_f hsp_f hcs_f hPf =>
            hk sf P_f (htr_f.trans ((by kpk_norm : _ = ss.trace).trans
              (htr_s.trans htr_u))) hsp_f hcs_f <| by
              refine Entails.trans hPf ?_
              rw [hst_f1]
              unfold epilogueOut
              refine Entails.trans ?_
                (sepConj_mono_left
                  (strSpeAt_reassemble A.repAlloc x.out errPtr 9#64 tagIdx errBs
                    (v28.setWidth 8) (v23.setWidth 32)
                    ((v23 >>> 32).setWidth 16) ((v23 >>> 48).setWidth 8)
                    herr_pos herr_lt herr_ptr))
              sep_focus
    by_cases hscap : seenCap = 0#64
    · subst hscap
      have hst_s0 : st_u = st_s := by
        simp only [st_s, optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
      refine SepWP.fold (vecU8_free_zero A.repAlloc seenPtr hs_len) (by sep_focus) ?_
      apply sepWP_seq_lscro hcrl_u (mid := (blkPl_578).base + 784#64)
      wp_steps_sync_pool ((blkPl_578).base + 784#64)
      apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_s
      exact hstep_seen _ _ (by kpk_norm) (by kpk_norm)
        (by kpk_norm) hcrl_s (by kpk_norm)
        (by kpk_norm) (by kpk_norm)
        (by kpk_norm) (by kpk_norm)
        (by kpk_norm) (by kpk_norm)
        (by kpk_norm) (by kpk_norm)
        (by rw [← hst_s0]; kpk_sep_focus)
    · obtain ⟨hs_pos, hs_pow1, hs_hi⟩ := layoutOk_u8_of_ne_zero hscap hs_lt
      have hs_lay : RustLayoutOk seenCap.toNat 1 := ⟨⟨hs_pos, hs_pow1, hs_hi⟩, by decide⟩
      have hscap_beq : (seenCap == 0#64) = false := beq_eq_false_iff_ne.mpr hscap
      have hst_s1 : M.stepEvents (rustDeallocEvents seenCap.toNat 1) st_u = st_s := by
        simp only [st_s, optDeallocBufEvents, hscap, ↓reduceIte]
      refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := seenPtr) hscap hs_len hs_lt) (by sep_focus) ?_
      apply sepWP_seq_lscro hcrl_u (mid := lsρ lsRustDeallocSymCli)
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_da
      apply sepWP_seq_lscro hcrl_da (mid := (blkPl_578).base + 784#64)
      rcases hcrl_da with ⟨hcl_da, hro_da⟩
      wp_call hdealloc (seenPtr, seenCap.toNat, 1, st_u)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl_s
      exact hstep_seen _ _ (by kpk_norm) (by kpk_norm)
        (by kpk_norm) hcrl_s (by kpk_norm)
        (by kpk_norm) (by kpk_norm)
        (by kpk_norm) (by kpk_norm)
        (by kpk_norm) (by kpk_norm)
        (by kpk_norm) (by kpk_norm)
        (by rw [hst_s1]; (try simp only [arm64_norm]); (try rw [hsp_u]); kpk_sep_focus)
  by_cases hucap : usedCap = 0#64
  · subst hucap
    have hst_u0 : st = st_u := by
      simp only [st_u, optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil]
    refine SepWP.fold (vecU8_free_zero A.repAlloc usedPtr hu_len) (by sep_focus) ?_
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 764#64)
    wp_steps_sync_pool ((blkPl_578).base + 764#64)
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_u
    exact hstep_used _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hcrl_u (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by rw [← hst_u0]; kpk_sep_focus)
  · obtain ⟨hu_pos, hu_pow1, hu_hi⟩ := layoutOk_u8_of_ne_zero hucap hu_lt
    have hu_lay : RustLayoutOk usedCap.toNat 1 := ⟨⟨hu_pos, hu_pow1, hu_hi⟩, by decide⟩
    have hucap_beq : (usedCap == 0#64) = false := beq_eq_false_iff_ne.mpr hucap
    have hst_u1 : M.stepEvents (rustDeallocEvents usedCap.toNat 1) st = st_u := by
      simp only [st_u, optDeallocBufEvents, hucap, ↓reduceIte]
    refine SepWP.fold (vecU8_free_ne A.repAlloc (ptr := usedPtr) hucap hu_len hu_lt) (by sep_focus) ?_
    apply sepWP_seq_lscro hcrl (mid := lsρ lsRustDeallocSymCli)
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_da
    apply sepWP_seq_lscro hcrl_da (mid := (blkPl_578).base + 764#64)
    rcases hcrl_da with ⟨hcl_da, hro_da⟩
    wp_call hdealloc (usedPtr, usedCap.toNat, 1, st)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_u
    exact hstep_used _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hcrl_u (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by rw [hst_u1]; (try simp only [arm64_norm]); (try rw [hsp]); kpk_sep_focus)

/-! ## Both `Dir::get` Error Exits (`+196` `one_time` and `+632` `last_resort`) -/

/-- `one_time.get` error exit (`+196 .. +236` → `+808` / `+816`): loads `fnPtr` / `fnLen` from
`[sp + 0x60 .. sp + 0x70)`, drops `name`, runs `kpk_epilogue_330_placed`, and reassembles
`kpkMarkOutAt A.repAlloc x.out .readErr`. -/
theorem kpk_read_err_c4_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (errBs : List (BitVec 8)) (errCap errPtr fnPtr : BitVec 64)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 196#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = speWord 1)
    (hx27 : s.readReg64 .x27 = errCap)
    (hx25 : s.readReg64 .x25 = errPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 errBs.length)
    (hx24 : s.readReg64 .x24 = namePtr)
    (hfoc : P ⊢
      ((s0.sp - 0x90#64) ↦₆₄ fnPtr) ∗
      ((s0.sp - 0x88#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
      bytesAt false namePtr nameBs ∗
      vecU8Tail A.repAlloc nameCap namePtr nameBs ∗
      speReadHeap A.repAlloc errBs errCap errPtr fnPtr ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A.repAlloc x.out .readErr ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        word1421At (s0.sp - 0x90#64) (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
          (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8) ∗
        ((s0.sp - 0x88#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim (M.stepEvents (optDeallocBufEvents nameCap) st) sf ∗ F) →
      post sf P_f) :
    SepWP (lsProg_578 H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hep := @kpk_epilogue_330_placed _ M A lim H
  have hfree := @kpk_free_ptr_328_placed _ M A lim H hC
  dsimp only [lsProg_578] at hep hfree
  clear hC
  change SepWP ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P post
  refine SepWP.weaken_pre hfoc ?_
  rw [pointsTo64_eq_word1421At (s0.sp - 0x90#64) fnPtr]
  unfold word1421At
  kpk_sep_norm
  by_cases hncap : nameCap = 0#64
  · subst hncap
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil] at hk
    refine SepWP.fold (vecU8_free_zero A.repAlloc namePtr hnlen) (by sep_focus) ?_
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 816#64)
    wp_steps_sync_pool ((blkPl_578).base + 816#64)
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro _hcrl_330
    refine hep x st s0 _ (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length)
      (readErrV28P fnPtr) (readErrV23P fnPtr) (BitVec.ofNat 64 (utf8 "read").length) _
      (word1421At (s0.sp - 0x90#64) (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
        (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8) ∗
        ((s0.sp - 0x88#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        ((s0.sp - 0x80#64) ↦₆₄ 0#64) ∗
        speReadHeap A.repAlloc errBs errCap errPtr fnPtr ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗ F)
      (by kpk_norm)
      (by kpk_norm)
      hsp_align
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by unfold epiloguePre word1421At; kpk_sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by kpk_norm)) hsp_f hcs_f <| by
          refine Entails.trans hPf ?_
          unfold epilogueOut
          refine Entails.trans ?_
            (sepConj_mono_left
              (kpkMarkOutAt_readErr_reassemble A.repAlloc x.out errBs errCap errPtr fnPtr
                (readErrV28P fnPtr) (readErrV23P fnPtr)
                (readErr_v28_lo_p fnPtr) (readErr_v23_lo_p fnPtr)
                (readErr_v23_mid_p fnPtr) (readErr_v23_hi_p fnPtr)))
          sep_focus
  · have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    simp only [optDeallocBufEvents, hncap, ↓reduceIte] at hk
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 808#64)
    wp_steps_sync_pool ((blkPl_578).base + 808#64)
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_328
    refine hfree x st s0 _ nameCap namePtr nameBs
      (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length)
      (readErrV28P fnPtr) (readErrV23P fnPtr) (BitVec.ofNat 64 (utf8 "read").length) _
      (word1421At (s0.sp - 0x90#64) (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
        (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8) ∗
        ((s0.sp - 0x88#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
        speReadHeap A.repAlloc errBs errCap errPtr fnPtr ∗ F)
      hncap hnlen hnlt hnptr
      (by kpk_norm)
      (by kpk_norm)
      hsp_align
      (by kpk_norm)
      hcrl_328
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by unfold epiloguePre word1421At; kpk_sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by kpk_norm)) hsp_f hcs_f <| by
          refine Entails.trans hPf ?_
          unfold epilogueOut
          refine Entails.trans ?_
            (sepConj_mono_left
              (kpkMarkOutAt_readErr_reassemble A.repAlloc x.out errBs errCap errPtr fnPtr
                (readErrV28P fnPtr) (readErrV23P fnPtr)
                (readErr_v28_lo_p fnPtr) (readErr_v23_lo_p fnPtr)
                (readErr_v23_mid_p fnPtr) (readErr_v23_hi_p fnPtr)))
          sep_focus

/-- `last_resort.get` error exit (`+632 .. +668` → `+804` / `+816`): loads `fnPtr` / `fnLen` from
`[sp + 0x60 .. sp + 0x70)`, drops `file` via `[sp + 0x20]` / `[sp + 0x18]`, runs `kpk_epilogue_330_placed`,
and reassembles `kpkMarkOutAt A.repAlloc x.out .readErr`. -/
theorem kpk_read_err_278_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s : State)
    (fileCap filePtr : BitVec 64) (fileBs : List (BitVec 8))
    (errBs : List (BitVec 8)) (errCap errPtr fnPtr : BitVec 64)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hflen : fileBs.length ≤ fileCap.toNat) (hflt : fileCap.toNat < 2 ^ 63)
    (hfptr : filePtr ≠ 0#64)
    (hpc : s.pc = (blkPl_578).base + 632#64)
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = speWord 1)
    (hx27 : s.readReg64 .x27 = errCap)
    (hx25 : s.readReg64 .x25 = errPtr)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 errBs.length)
    (hfoc : P ⊢
      ((s0.sp - 0x90#64) ↦₆₄ fnPtr) ∗
      ((s0.sp - 0x88#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
      ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
      bytesAt false filePtr fileBs ∗
      vecU8Tail A.repAlloc fileCap filePtr fileBs ∗
      speReadHeap A.repAlloc errBs errCap errPtr fnPtr ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      epiloguePre s0 x ∗ A.pool lim st s ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A.repAlloc x.out .readErr ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        word1421At (s0.sp - 0x90#64) (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
          (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8) ∗
        ((s0.sp - 0x88#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool lim (M.stepEvents (optDeallocBufEvents fileCap) st) sf ∗ F) →
      post sf P_f) :
    SepWP (lsProg_578 H) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hep := @kpk_epilogue_330_placed _ M A lim H
  have hfreeFile := @kpk_free_file_324_placed _ M A lim H hC
  dsimp only [lsProg_578] at hep hfreeFile
  clear hC
  change SepWP ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P post
  refine SepWP.weaken_pre hfoc ?_
  rw [pointsTo64_eq_word1421At (s0.sp - 0x90#64) fnPtr]
  unfold word1421At
  kpk_sep_norm
  by_cases hfcap : fileCap = 0#64
  · subst hfcap
    simp only [optDeallocBufEvents, ↓reduceIte, M.stepEvents_nil] at hk
    refine SepWP.fold (vecU8_free_zero A.repAlloc filePtr hflen) (by sep_focus) ?_
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 816#64)
    wp_steps_sync_pool ((blkPl_578).base + 816#64)
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro _hcrl_330
    refine hep x st s0 _ (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length)
      (readErrV28P fnPtr) (readErrV23P fnPtr) (BitVec.ofNat 64 (utf8 "read").length) _
      (word1421At (s0.sp - 0x90#64) (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
        (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8) ∗
        ((s0.sp - 0x88#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ 0#64) ∗
        speReadHeap A.repAlloc errBs errCap errPtr fnPtr ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗ F)
      (by kpk_norm)
      (by kpk_norm)
      hsp_align
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by unfold epiloguePre word1421At; kpk_sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by kpk_norm)) hsp_f hcs_f <| by
          refine Entails.trans hPf ?_
          unfold epilogueOut
          refine Entails.trans ?_
            (sepConj_mono_left
              (kpkMarkOutAt_readErr_reassemble A.repAlloc x.out errBs errCap errPtr fnPtr
                (readErrV28P fnPtr) (readErrV23P fnPtr)
                (readErr_v28_lo_p fnPtr) (readErr_v23_lo_p fnPtr)
                (readErr_v23_mid_p fnPtr) (readErr_v23_hi_p fnPtr)))
          sep_focus
  · have hfcap_beq : (fileCap == 0#64) = false := beq_eq_false_iff_ne.mpr hfcap
    simp only [optDeallocBufEvents, hfcap, ↓reduceIte] at hk
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 804#64)
    wp_steps_sync_pool ((blkPl_578).base + 804#64)
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_324
    refine hfreeFile x st s0 _ fileCap filePtr fileBs
      (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length)
      (readErrV28P fnPtr) (readErrV23P fnPtr) (BitVec.ofNat 64 (utf8 "read").length) _
      (word1421At (s0.sp - 0x90#64) (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
        (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8) ∗
        ((s0.sp - 0x88#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        speReadHeap A.repAlloc errBs errCap errPtr fnPtr ∗ F)
      hfcap hflen hflt hfptr
      (by kpk_norm)
      (by kpk_norm)
      hsp_align
      (by kpk_norm)
      hcrl_324
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by unfold epiloguePre word1421At; kpk_sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by kpk_norm)) hsp_f hcs_f <| by
          refine Entails.trans hPf ?_
          unfold epilogueOut
          refine Entails.trans ?_
            (sepConj_mono_left
              (kpkMarkOutAt_readErr_reassemble A.repAlloc x.out errBs errCap errPtr fnPtr
                (readErrV28P fnPtr) (readErrV23P fnPtr)
                (readErr_v28_lo_p fnPtr) (readErr_v23_lo_p fnPtr)
                (readErr_v23_mid_p fnPtr) (readErr_v23_hi_p fnPtr)))
          sep_focus

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget
