/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.Core
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `TooFarPath` Segment Proof (Block 24)

Proves `TooFarPathPlacedSpec` under `RustCliAllocBudget M` and `SeamBudget`, ruling out OOM at
`__rust_alloc(36, 1)`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.CoreBudget

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoVerification (
  LibsignalPlacement lsmpl lsρ lsLogFilterAddr
  blkPC_24 blkPl_24 blkLib_eq_24
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (
  RatchetGhost ratchetAt tooFarInFutureStr msgTypeByte
)
open CryptoVerification.SessionModel (consumeMessageKey_tooFar)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost
  cmkRustAllocSym cmkRustNoAllocShimSym
  cmkDummyImg logFilterAddr_cmkDummyImg
  cmkPreLoopHeap cmkPreLoopHeap_placed_eq cmkSavedRegs
  cmk_hook_ok_of_mem
)
open CryptoVerification.LibsignalSession.TooFarPath (
  cmkTooFarStrSym
  reaches_outcome_of_sepWPp_post cs_maxForwardJumps_eq_false
  ratchetRest ratchetAt_split_mfj
  pointsToBytesRO_tooFarInFutureStr memRegion_88_ret_split
  stackAt_7712_split memRegion_384_tooFarPath_split memRegion_36_split
  tooFarPathPost tooFarPathPostRaw tooFarPathPostRaw_entails_tooFarPathPost
  SepWP.conseq_tooFarPathPost
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEvents RustLayoutOk
  rustAllocEvents rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  cmkShimSpec CmkEnv cmkPlacedSpec TooFarPathPlacedSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? cmkDummyImg
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `A.atState` Independence and Postcondition Entailment -/

private theorem ratchetAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetAt (A.atState lim st s) = ratchetAt A.repAlloc :=
  rfl

private theorem ratchetRest_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetRest (A.atState lim st s) = ratchetRest A.repAlloc :=
  rfl

theorem tooFarPathPost_entails_cmkPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {x : ConsumeMessageKeyGhost} {st_init : M.σ} {evs : List AllocEvent}
    (henv : CmkEnv x evs)
    (hm1 : (x.model F).1 = .error (.invalidMessage x.msgType .tooFarInFuture))
    (hm2 : (x.model F).2 = x.st)
    (htouch : x.touched F = none)
    (s0 sf : State) :
    tooFarPathPost (A.atState lim (M.stepEvents evs st_init) sf) cmkDummyImg x s0 sf ⊢
      (cmkPlacedSpec F A lim).post (x, st_init) s0 sf := by
  have h :=
    CryptoVerification.LibsignalSession.TooFarPath.tooFarPathPost_entails_cmkPlacedSpec
      (F := F) (A := A.atState lim (M.stepEvents evs st_init) sf)
      hm1 hm2 htouch s0 sf
  unfold cmkPlacedSpec
  dsimp only
  refine Entails.trans ?_ (Entails.sepExists_intro evs)
  exact Entails.pure_right henv h

/-! ## Top-Level `TooFarPathPlacedSpec` Proof -/

theorem tooFarPath_placed_ok' [LibsignalPlacement] {M : AllocCostModel}
    (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) :
    TooFarPathPlacedSpec F A lim H := by
  intro hA x st_init st R s0 s hle hjump ⟨hsb, hstate⟩
  have hfit36 : FitsEvents M lim st (rustAllocEvents 36 1) :=
    hsb.1 (rustAllocEvents 36 1) rfl
  obtain ⟨evs_tot, hst_tot, henv_tot⟩ :=
    hsb.finish (evs_exit := rustAllocEvents 36 1) rfl
  rcases hA with ⟨halloc_sat, _, hshim_sat, _, _, _⟩
  rcases hstate with
    ⟨hpc, ⟨hrun, hsp, hsp0_align, hsp_align, hx29, htrace, hcl, hvregs⟩,
     ⟨hx2, hx4, hx9, hx20, hx22, hx23, hx26, hx27, hx28⟩, hmem⟩
  have hmodel : x.model F = (.error (.invalidMessage x.msgType .tooFarInFuture), x.st) :=
    consumeMessageKey_tooFar F x.st x.their x.ck x.counter x.msgType hle hjump
  have hm1 : (x.model F).1 = .error (.invalidMessage x.msgType .tooFarInFuture) := by rw [hmodel]
  have hm2 : (x.model F).2 = x.st := by rw [hmodel]
  have htouch : x.touched F = none := by unfold ConsumeMessageKeyGhost.touched; rw [hm1]
  have hshim : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H)
      (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hshim_sat
  have halloc_nooom : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H)
      (lsρ cmkRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
    subroutine_ok_allocNoOom_of_budget (cmk_hook_ok_of_mem halloc_sat)
  have hpc' : s.pc = (blkPl_24).base + 368#64 := hpc
  clear hpc
  have hpc := hpc'
  clear hpc'
  rw [cmkPreLoopHeap_placed_eq] at hmem
  have hmem_ro : s.mem ⊨
      ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗
        cmkPreLoopHeap (A.atState lim st s) cmkDummyImg x s0) ∗ R := by
    have heq :
        cmkPreLoopHeap (A.atState lim st s) cmkDummyImg x s0 ∗
          ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) =
        ((lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗
          cmkPreLoopHeap (A.atState lim st s) cmkDummyImg x s0) ∗ R := by sep_ac_rfl
    rwa [← heq]
  clear hmem
  refine reaches_outcome_of_sepWPp_post
    (Drop := (lsρ cmkTooFarStrSym ↦₆₄ᵣ 0x206567617373656d#64) ∗
      ((lsρ cmkTooFarStrSym + 8#64) ↦₆₄ᵣ 0x6f6f74206d6f7266#64) ∗
      ((lsρ cmkTooFarStrSym + 16#64) ↦₆₄ᵣ 0x746e692072616620#64) ∗
      ((lsρ cmkTooFarStrSym + 24#64) ↦₆₄ᵣ 0x756620656874206f#64) ∗
      ((lsρ cmkTooFarStrSym + 32#64) ↦₃₂ᵣ 0x65727574#32))
    (Post := fun sf => tooFarPathPost (A.atState lim (M.stepEvents evs_tot st_init) sf) cmkDummyImg x s0 sf)
    hmem_ro (tooFarPathPost_entails_cmkPlacedSpec henv_tot hm1 hm2 htouch s0) ?_
  clear halloc_sat hshim_sat hmodel hm1 hm2 htouch hcl hmem_ro hsb henv_tot
  apply SepWPp.of_sepWP_ret
  unfold cmkPreLoopHeap cmkSavedRegs
  rw [ratchetAt_atState, RustCliAllocBudget.atState_pool,
      logFilterAddr_cmkDummyImg,
      pointsToBytesRO_tooFarInFutureStr (lsρ cmkTooFarStrSym),
      ratchetAt_split_mfj A.repAlloc x.self x.G x.st,
      memRegion_88_ret_split x.ret,
      stackAt_7712_split s0.sp,
      memRegion_384_tooFarPath_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun r40 => SepWP.exists_elim fun r32 =>
    SepWP.exists_elim fun r24 => SepWP.exists_elim fun r16 =>
    SepWP.exists_elim fun r8 => SepWP.exists_elim fun r0 =>
    SepWP.exists_elim fun v9 => ?_
  have hcs := cs_maxForwardJumps_eq_false hjump
  have hx4_gpr : BitVec.zeroExtend 8 (s.readReg64 (Reg.gpr 4#5)) = msgTypeByte x.msgType := hx4
  have hpow1 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay36 : RustLayoutOk 36 1 := ⟨⟨by decide, hpow1, by decide⟩, by decide⟩
  have hfe36_raw : FitsEvents M lim st [.alloc 36] := by
    simpa [rustAllocEvents] using hfit36
  rcases hfe36_raw with ⟨⟨_hwma36, _henf36, _hram36, _hva36⟩, -⟩
  dsimp only [cmkShimSpec] at hshim
  wp_steps_sync_pool (lsρ cmkRustNoAllocShimSym)
  wp_call hshim ()
  refine SepWP.transport_budgetPool ‹LibsignalBinary.Heap.VmPreserved _ sf› (hnext := ?_)
  have htr_sf0 : sf.trace = s0.trace := (‹sf.trace = s.trace›).trans htrace
  wp_steps_sync_pool (lsρ cmkRustAllocSym)
  wp_call halloc_nooom (36, 1, st)
  have htrace1 : sf_1.trace = s0.trace :=
    (‹LibsignalBinary.Heap.AllocCallPreserved _ sf_1›).2.1.trans htr_sf0
  have hoom' : sf_1.readReg64 .x0 ≠ 0 := ‹sf_1.readReg64 .x0 ≠ 0#64›
  have hcbz_oom : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom'
  rw [(‹sf.sp = s.sp›).trans hsp]
  rw [memRegion_36_split (sf_1.readReg64 .x0)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun p4 => SepWP.exists_elim fun p3 =>
    SepWP.exists_elim fun p2 => SepWP.exists_elim fun p1 =>
    SepWP.exists_elim fun p0 => ?_
  apply SepWP.conseq_tooFarPathPost (fun sf_ret =>
    tooFarPathPostRaw_entails_tooFarPathPost
      (A.atState lim (M.stepEvents evs_tot st_init) sf_ret)
      cmkDummyImg x s0 (sf_1.readReg64 .x0) hoom' sf_ret)
  simp only [tooFarPathPostRaw, cmkSavedRegs, logFilterAddr_cmkDummyImg,
    ratchetRest_atState, RustCliAllocBudget.atState_live, RustCliAllocBudget.atState_pool]
  rw [hst_tot]
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  wp_done

end LibsignalBinary.Proofs.ConsumeMessageKey.TooFarPathProofs.CoreBudget
