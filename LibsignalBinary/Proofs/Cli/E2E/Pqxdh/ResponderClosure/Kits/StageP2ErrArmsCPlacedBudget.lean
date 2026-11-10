/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrCPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlaced
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Relocatable Stage P2 Rejection and Store-Error Unwind Arms 5–6

Defines `FreeOnlyEvs` event lists and proves `RustCliAllocBudget M` / `VmPreserved` placed unwinds
to `s0.readReg64 .x30` on Block `518` for Arms 5 (`+0x125c`) and 6 (`+0x09f4`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees hiding
  dropSessionStructureLocal2Spec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  PreKeyStoreKitPlacedOk IdentitySelfStoreKitPlacedOkI
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  StageP2ClosureHooksPlaced
  stageP2_err_funnel_hooks_placed_ok
  p2_err5_1568_hooks_placed_wp
  p2_err6a_ext_placed_wp
  p2_err6b_a_hooks_placed_wp
  p2_err6b_b_1568_hooks_placed_wp
  p2_arm5_err_hooks_placed_ok
  p2_arm6_err_hooks_placed_ok
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
  rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (
  futDropBudgetSpec
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  StageP2ClosureHooksPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrCPlacedBudget (
  p2_err5_1568_hooks_placed_wp
  p2_err6a_ext_placed_wp
  p2_err6b_a_hooks_placed_wp
  p2_err6b_b_1568_hooks_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget (
  p2_bind_sepWP_qp_frame_state_placed
  p2_bind_sepWPp_steps_frame_state
  p2ErrFunnelEvents
  p2ErrFunnelEvents_freeOnly
  stageP2_err_funnel_hooks_placed_ok
)

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## 1. Concrete `FreeOnlyEvs` Event Lists for Rejection & Store-Error Arms 5–6 -/

/-- Exact deallocation event list for Arm 5 (`initialize_bob_session` `Err` unwind:
`pkBuf` `1568` B, `skBuf` `3168` B, plus error funnel). -/
def p2Arm5ErrEvents (prevCap : BitVec 64) : List AllocEvent :=
  (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) ++ p2ErrFunnelEvents prevCap

/-- Exact deallocation event list for Arm 6 (`get_local_registration_id` `.error` unwind:
`regIdFutPtr`, `evs_ss` from `drop_session_structure3`, `pkBuf` `1568` B, `skBuf` `3168` B, plus
error funnel). -/
def p2Arm6ErrEvents (regIdBoxSize : Nat) (evs_ss : List AllocEvent) (prevCap : BitVec 64) :
    List AllocEvent :=
  ((rustDeallocEvents regIdBoxSize 8 ++ evs_ss) ++
    (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1)) ++
    p2ErrFunnelEvents prevCap

theorem p2Arm5ErrEvents_freeOnly (prevCap : BitVec 64) :
    FreeOnlyEvs (p2Arm5ErrEvents prevCap) :=
  ((FreeOnlyEvs.singleton 1 1568).append (FreeOnlyEvs.singleton 1 3168)).append
    (p2ErrFunnelEvents_freeOnly prevCap)

theorem p2Arm6ErrEvents_freeOnly (regIdBoxSize : Nat) {evs_ss : List AllocEvent}
    (hevs_ss : FreeOnlyEvs evs_ss) (prevCap : BitVec 64) :
    FreeOnlyEvs (p2Arm6ErrEvents regIdBoxSize evs_ss prevCap) :=
  (((FreeOnlyEvs.singleton 8 regIdBoxSize).append hevs_ss).append
    ((FreeOnlyEvs.singleton 1 1568).append (FreeOnlyEvs.singleton 1 3168))).append
    (p2ErrFunnelEvents_freeOnly prevCap)

/-! ## 2. Rejection Unwind Arm 5 (`+0x125c -> s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-Threaded Arm 5 (`+0x125c -> s0.readReg64 .x30`) on `stageP1ProgPlaced ext`:
`initialize_bob_session` `Err` unwind through `p2_err5_1568_hooks_placed_wp`
(freeing Kyber keypair at `coroPtr + 0x718..0x730`) and `stageP2_err_funnel_hooks_placed_ok`. -/
theorem p2_arm5_err_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr pkBuf skBuf
    w0 w1 w2 w3 w4 w5 u_88 u_a8 u_b8 u_d0 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hw0_ne_pending : w0 ≠ 0xfffffffffffffffd#64) (hw0_ne_ok : w0 ≠ 0xfffffffffffffffe#64)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
       speWordsAt (sp + 0x3e8#64) w0 w1 w2 w3 w4 w5 ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim st s ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        let st' := M.stepEvents (p2Arm5ErrEvents prevCap) st
        sf.trace = s.trace ∧
        (P_f ⊢
          ((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          speWordsAt (sp + 0x3e8#64) w0 w1 w2 w3 w4 w5 ∗
          ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          ((sp + 0x88#64) ↦₆₄ w0) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ w4) ∗
          ((sp + 0xb8#64) ↦₆₄ w2) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ w3) ∗
          cells (sp + 0xa90#64) 6 ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim st' sf ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        M.liveBytes st' ≤ M.liveBytes st)
      Qp := by
  have hx28_s : s.readReg64 .x28 = s.sp + 0xa90#64 := by rw [hx28, hsp_eq]
  have hstep1 := p2_err5_1568_hooks_placed_wp (st := st) ext hH s coroPtr pkBuf skBuf outPtr
    w0 w1 w2 w3 w4 w5 u_88 u_a8 u_b8 u_d0
    hpc hrun hsp_align hx19 hx28_s
  rw [hsp_eq] at hstep1
  refine p2_bind_sepWP_qp_frame_state_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx10_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs1, _hlive1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have hx25_1' : s1.readReg64 .x25 = sp + 0x210#64 := hx25_1.trans hx25
  have hvregs1_0 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1.trans hvregs
  change s1.pc = stageP1EntryPlaced + 0x1648#64 at hpc1
  have hfunnel := stageP2_err_funnel_hooks_placed_ok
    (st := M.stepEvents (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1) st)
    (Qp := fun _ _ => False) hH s0 s1 sp coroPtr outPtr prevCap prevPtr
    w0 w1 w2 w3 w4 w5 w1 outPtr
    b_2c0 b_390 b_4f2 hprev_lt hw0_ne_pending hw0_ne_ok rfl
    hCode1 hsp1 hpc1 hrun1 hsp1_align
    hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1' hx26_1 hx27_1 hx28_1 hvregs1_0
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hCodef, _⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hCodef))))
  refine p2_bind_sepWPp_steps_frame_state hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcsf, hvregsf, hCodef⟩
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨htrf.trans htr1, ?_, hspf, hcsf, hvregsf, hCodef,
    M.liveBytes_stepEvents_freeOnly_le (p2Arm5ErrEvents_freeOnly prevCap) st⟩
  dsimp only [p2Arm5ErrEvents]
  rw [M.stepEvents_append]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

abbrev p2_arm5_err_4k_placed_ok := @p2_arm5_err_hooks_placed_ok
abbrev p2_arm5_err_ext_placed_ok := @p2_arm5_err_hooks_placed_ok

/-! ## 3. Store-Error Unwind Arm 6 (`+0x09f4 -> s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Budget-Threaded Arm 6 (`+0x09f4 -> s0.readReg64 .x30`, direct `futDropBudgetSpec` +
explicit `p2Arm6ErrEvents` decomposition) on `stageP1ProgPlaced ext`:
`IdentityKeyStore::get_local_registration_id` `.error e` unwind through `hregId_drop`,
`p2_err6b_a_hooks_placed_wp`, `hDropSs3` (dropping the unpromoted Bob `SessionState` at
`coroPtr + 0x4f8..0x650`), `p2_err6b_b_1568_hooks_placed_wp` (freeing Kyber keypair), and
`stageP2_err_funnel_hooks_placed_ok`. -/
theorem p2_arm6_err_drop_events_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {skit : IdentitySelfStoreSpec ikit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hregId_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + skit.regIdFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropBudgetSpec))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr
    idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8) (e : skit.RegIdErr)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
       ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
       ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0x4f8#64) G st ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (∃ evs_ss : List AllocEvent,
          FreeOnlyEvs evs_ss ∧
          let st' := M.stepEvents (p2Arm6ErrEvents skit.regIdBoxSize evs_ss prevCap) st0
          (P_f ⊢
            speWordsAt (sp + 0x3e0#64) (skit.regIdErr.w0 e) (skit.regIdErr.w1 e)
              (skit.regIdErr.w2 e) (skit.regIdErr.w3 e) (skit.regIdErr.w4 e)
              (skit.regIdErr.w5 e) ∗
            ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
            ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
            ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
            ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
            ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            memRegion (coroPtr + 0x4f8#64) 344 ∗
            ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x88#64) ↦₆₄ skit.regIdErr.w0 e) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ skit.regIdErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ skit.regIdErr.w2 e) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.regIdErr.w3 e) ∗
            cells (sp + 0xa90#64) 6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt skit.regIdErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim st' sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          M.liveBytes st' ≤ M.liveBytes st0) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  dsimp only [regIdPollOutAt, speErrAt]
  have hstep1 := p2_err6a_ext_placed_wp ext s coroPtr regIdFutPtr
    (0#64 + skit.regIdFutVtOff) (0#64 + skit.regIdFutDropOff)
    (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
    (skit.regIdErr.w3 e) (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0
    u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    (skit.regIdErr.w0_ne_pending e) (skit.regIdFutDrop_ne_zero rfl)
    hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine p2_call_nopanic_rocl_steps_frame_placed (spec := futDropBudgetSpec) (x := ()) (T := emp)
    hCode1 hregId_drop hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [futDropBudgetSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [futDropBudgetSpec]
  refine SepWPp.pure_elim fun ⟨htr2_1, hvm2_1⟩ => ?_
  have hvm2 : VmPreserved s s2 := hvm1.trans hvm2_1
  refine SepWPp.transport_budgetPool hvm2 (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (skit.regIdBoxAt_memRegion regIdFutPtr idStorePtr 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hstep3 := p2_err6b_a_hooks_placed_wp (st := st0) ext hH s2 coroPtr regIdFutPtr
    (0#64 + skit.regIdFutVtOff) (skit.regIdErr.w0 e) skit.regIdBoxSize
    (skit.regIdErr.w0_ne_ok e) skit.regIdBoxSize_ne_zero skit.regIdBoxSize_lt
    hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx24_cs2.trans hx24_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_state_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx0_3, hx19_3, hx22_3, hx23_3, hx25_3, _,
    hx27_3, hx28_3, _, hx30_3, hvregs3_2, _hlive3⟩
  have hsp3_al : s3.spAligned = true := by simp only [State.spAligned, hsp3, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  refine p2_call_nopanic_lscl_steps_frame_placed
    (spec := dropSessionStructureLocal2Spec M A lim)
    (x := ((⟨coroPtr + 0x4f8#64, G, st⟩ : DropSessionStructureGhost),
      M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st0))
    (T := sessionStateAt A.repAlloc (coroPtr + 0x4f8#64) G st ∗
      A.pool lim (M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st0) s3 ∗
      stackAt s3.sp dropSessionStructureLocal2Stack)
    hCode3 hDropSs3
    hpc3 hrun3 hsp3_al hx30_3
    rfl
    (And.intro hx0_3 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s3.readReg64 .lr) by
      simp (config := { decide := true }) [show s3.readReg64 .lr = _ from hx30_3, wp_norm]))
    (by rw [hsp3]; sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun evs_ss => SepWPp.pure_elim fun ⟨htr4_3, hevs_ss⟩ => ?_
  have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4, ← hsp_eq]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, _, _, hx22_cs4, hx23_cs4, _,
    hx25_cs4, _, hx27_cs4, hx28_cs4, _, hvregs4_3⟩
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx22_4 : s4.readReg64 .x22 = (skit.regIdErr.w1 e) >>> 32 := by
    rw [hx22_cs4, hx22_3, hx22_cs2, hx22_1]
  have hx23_4 : s4.readReg64 .x23 = ((skit.regIdErr.w1 e).extractLsb' 0 32).zeroExtend 64 := by
    rw [hx23_cs4, hx23_3, hx23_cs2, hx23_1]
  have hx27_4 : s4.readReg64 .x27 = skit.regIdErr.w5 e := by
    rw [hx27_cs4, hx27_3, hx27_cs2, hx27_1]
  have hx28_4 : s4.readReg64 .x28 = s4.sp + 0xa90#64 := by
    rw [hx28_cs4, hx28_3, hx28_cs2, hx28_1, hx28, hsp4]
  have hstep5 := p2_err6b_b_1568_hooks_placed_wp
    (st := M.stepEvents evs_ss (M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st0))
    ext hH s4 coroPtr pkBuf skBuf outPtr
    (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
    (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)
    hpc4 hrun4 hsp4_align hx19_4 hx22_4 hx23_4 hx27_4 hx28_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_qp_frame_state_placed hCode4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hCode5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5_4, hx10_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
    hx25_5, hx26_5, hx27_5, hx28_5, _, hvregs5_4, _hlive5⟩
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5, ← hsp_eq]; exact hsp_align
  have hx25_5' : s5.readReg64 .x25 = sp + 0x210#64 := by
    rw [hx25_5, hx25_cs4, hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs5 : calleeSavedVRegs s5 = calleeSavedVRegs s0 := by
    rw [hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s5.pc = stageP1EntryPlaced + 0x1648#64 at hpc5
  have hfunnel := stageP2_err_funnel_hooks_placed_ok
    (st := M.stepEvents (rustDeallocEvents 1568 1 ++ rustDeallocEvents 3168 1)
      (M.stepEvents evs_ss (M.stepEvents (rustDeallocEvents skit.regIdBoxSize 8) st0)))
    (Qp := fun _ _ => False) hH s0 s5 sp coroPtr outPtr prevCap prevPtr
    (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
    (skit.regIdErr.w3 e) (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)
    (((skit.regIdErr.w1 e).extractLsb' 0 32).zeroExtend 64) outPtr
    b_2c0 b_390 b_4f2 hprev_lt
    (skit.regIdErr.w0_ne_pending e) (skit.regIdErr.w0_ne_ok e)
    (p2_zeroExtend32_extractLsb_lo (skit.regIdErr.w1 e))
    hCode5 hsp5 hpc5 hrun5 hsp5_align
    hx10_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5' hx26_5 hx27_5 hx28_5 hvregs5
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hCodef, _⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hCodef))))
  refine p2_bind_sepWPp_steps_frame_state hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcsf, hvregsf, hCodef⟩
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr5_4, htr4_3, htr3_2, htr2_1, htr1],
    ⟨evs_ss, hevs_ss, ?_,
      M.liveBytes_stepEvents_freeOnly_le
        (p2Arm6ErrEvents_freeOnly skit.regIdBoxSize hevs_ss prevCap) st0⟩,
    hspf, hcsf, hvregsf, hCodef⟩
  simp only [p2Arm6ErrEvents, M.stepEvents_append]
  rw [p2_dropSs3Stack_eq sp]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Budget-Threaded Arm 6 (`+0x09f4 -> s0.readReg64 .x30`, `IdentitySelfStoreKitPlacedOkI` +
explicit `p2Arm6ErrEvents` decomposition) on `stageP1ProgPlaced ext`. -/
theorem p2_arm6_err_events_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {skit : IdentitySelfStoreSpec ikit}
    {senv : IdentitySelfStoreBudgetEnv skit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr
    idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8) (e : skit.RegIdErr)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
       ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
       ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0x4f8#64) G st ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (∃ evs_ss : List AllocEvent,
          FreeOnlyEvs evs_ss ∧
          let st' := M.stepEvents (p2Arm6ErrEvents skit.regIdBoxSize evs_ss prevCap) st0
          (P_f ⊢
            speWordsAt (sp + 0x3e0#64) (skit.regIdErr.w0 e) (skit.regIdErr.w1 e)
              (skit.regIdErr.w2 e) (skit.regIdErr.w3 e) (skit.regIdErr.w4 e)
              (skit.regIdErr.w5 e) ∗
            ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
            ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
            ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
            ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
            ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            memRegion (coroPtr + 0x4f8#64) 344 ∗
            ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x88#64) ↦₆₄ skit.regIdErr.w0 e) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ skit.regIdErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ skit.regIdErr.w2 e) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.regIdErr.w3 e) ∗
            cells (sp + 0xa90#64) 6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt skit.regIdErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim st' sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          M.liveBytes st' ≤ M.liveBytes st0) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp :=
  p2_arm6_err_drop_events_hooks_placed_ok hH hDropSs3 (hskitOk.regIdFutDrop (by decide)) G st s0 s
    sp coroPtr outPtr prevCap prevPtr idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 b_2c0 b_390 b_4f2 e
    hprev_lt hCode hsp_eq hpc hrun hsp_align hx19 hx21 hx23 hx25 hx26 hx28 hvregs

/-- Budget-Threaded Arm 6 (`+0x09f4 -> s0.readReg64 .x30`, direct `futDropBudgetSpec` +
packaged `FreeOnlyEvs` postcondition) on `stageP1ProgPlaced ext`. -/
theorem p2_arm6_err_drop_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {skit : IdentitySelfStoreSpec ikit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hregId_drop : subroutine_ok (stageP1ProgPlaced ext) (0#64 + skit.regIdFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropBudgetSpec))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr
    idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8) (e : skit.RegIdErr)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
       ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
       ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0x4f8#64) G st ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            speWordsAt (sp + 0x3e0#64) (skit.regIdErr.w0 e) (skit.regIdErr.w1 e)
              (skit.regIdErr.w2 e) (skit.regIdErr.w3 e) (skit.regIdErr.w4 e)
              (skit.regIdErr.w5 e) ∗
            ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
            ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
            ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
            ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
            ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            memRegion (coroPtr + 0x4f8#64) 344 ∗
            ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x88#64) ↦₆₄ skit.regIdErr.w0 e) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ skit.regIdErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ skit.regIdErr.w2 e) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.regIdErr.w3 e) ∗
            cells (sp + 0xa90#64) 6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt skit.regIdErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          M.liveBytes (M.stepEvents evs st0) ≤ M.liveBytes st0) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine SepWPp.mono_run
    (p2_arm6_err_drop_events_hooks_placed_ok hH hDropSs3 hregId_drop G st s0 s
      sp coroPtr outPtr prevCap prevPtr idStorePtr regIdFutPtr pkBuf skBuf
      v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 b_2c0 b_390 b_4f2 e
      hprev_lt hCode hsp_eq hpc hrun hsp_align hx19 hx21 hx23 hx25 hx26 hx28 hvregs)
    fun sf P_f ⟨htrf, ⟨evs_ss, hevs_ss, hentf, hlivef⟩, hrest⟩ =>
      ⟨htrf,
        ⟨p2Arm6ErrEvents skit.regIdBoxSize evs_ss prevCap,
          p2Arm6ErrEvents_freeOnly skit.regIdBoxSize hevs_ss prevCap,
          hentf, hlivef⟩,
        hrest⟩

/-- Budget-Threaded Arm 6 (`+0x09f4 -> s0.readReg64 .x30`, `IdentitySelfStoreKitPlacedOkI` +
packaged `FreeOnlyEvs` postcondition) on `stageP1ProgPlaced ext`. -/
theorem p2_arm6_err_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st0 : M.σ}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {skit : IdentitySelfStoreSpec ikit}
    {senv : IdentitySelfStoreBudgetEnv skit}
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hDropSs3 :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr
    idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8) (e : skit.RegIdErr)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x9f4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
       ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
       ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       sessionStateAt A.repAlloc (coroPtr + 0x4f8#64) G st ∗
       ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢
            speWordsAt (sp + 0x3e0#64) (skit.regIdErr.w0 e) (skit.regIdErr.w1 e)
              (skit.regIdErr.w2 e) (skit.regIdErr.w3 e) (skit.regIdErr.w4 e)
              (skit.regIdErr.w5 e) ∗
            ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
            ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
            ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
            ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
            ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            memRegion (coroPtr + 0x4f8#64) 344 ∗
            ((coroPtr + 0x718#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x728#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
            ((sp + 0x88#64) ↦₆₄ skit.regIdErr.w0 e) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((sp + 0xa8#64) ↦₆₄ skit.regIdErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
            ((sp + 0xb8#64) ↦₆₄ skit.regIdErr.w2 e) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.regIdErr.w3 e) ∗
            cells (sp + 0xa90#64) 6 ∗
            memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            memRegion (sp + 0x370#64) 36 ∗
            decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
            speErrAt skit.regIdErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt sp dropSessionStructureLocal2Stack) ∧
          M.liveBytes (M.stepEvents evs st0) ≤ M.liveBytes st0) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp :=
  p2_arm6_err_drop_hooks_placed_ok hH hDropSs3 (hskitOk.regIdFutDrop (by decide)) G st s0 s
    sp coroPtr outPtr prevCap prevPtr idStorePtr regIdFutPtr pkBuf skBuf
    v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0 b_2c0 b_390 b_4f2 e
    hprev_lt hCode hsp_eq hpc hrun hsp_align hx19 hx21 hx23 hx25 hx26 hx28 hvregs

abbrev p2_arm6_err_4k_placed_ok := @p2_arm6_err_hooks_placed_ok
abbrev p2_arm6_err_ext_placed_ok := @p2_arm6_err_hooks_placed_ok

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsCPlacedBudget
