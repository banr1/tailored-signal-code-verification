/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsC
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext

/-!
# Relocatable Stage P2 Rejection and Store-Error Unwind Arms 5–6

Proves placed `SepWPp` unwinds to `s0.readReg64 .x30` on Block `518` (`stageP1ProgPlaced ext`) for
Arms 5 (`+0x125c`) and 6 (`+0x09f4`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option maxRecDepth 200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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

set_option maxHeartbeats 1200000 in
/-- Arm 5 (`+0x125c -> s0.readReg64 .x30`) on `stageP1ProgPlaced ext`:
`initialize_bob_session` `Err` unwind through `p2_err5_1568_hooks_placed_wp`
(freeing Kyber keypair at `coroPtr + 0x718..0x730`) and `stageP2_err_funnel_hooks_placed_ok`. -/
theorem p2_arm5_err_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hH : StageP2ClosureHooksPlaced A ext)
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
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
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
          speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hx28_s : s.readReg64 .x28 = s.sp + 0xa90#64 := by rw [hx28, hsp_eq]
  have hstep1 := p2_err5_1568_hooks_placed_wp ext hH s coroPtr pkBuf skBuf outPtr
    w0 w1 w2 w3 w4 w5 u_88 u_a8 u_b8 u_d0
    hpc hrun hsp_align hx19 hx28_s
  rw [hsp_eq] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx10_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have hx25_1' : s1.readReg64 .x25 = sp + 0x210#64 := hx25_1.trans hx25
  have hvregs1_0 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1.trans hvregs
  change s1.pc = stageP1EntryPlaced + 0x1648#64 at hpc1
  have hfunnel := stageP2_err_funnel_hooks_placed_ok (Qp := fun _ _ => False) hH s0 s1 sp coroPtr outPtr prevCap prevPtr
    w0 w1 w2 w3 w4 w5 w1 outPtr
    b_2c0 b_390 b_4f2 hprev_lt hw0_ne_pending hw0_ne_ok rfl
    hCode1 hsp1 hpc1 hrun1 hsp1_align
    hx10_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1' hx26_1 hx27_1 hx28_1 hvregs1_0
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hCodef⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hCodef))))
  refine p2_bind_sepWPp_steps_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcsf, hvregsf, hCodef⟩
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨htrf.trans htr1, ?_, hspf, hcsf, hvregsf, hCodef⟩
  sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Arm 6 (`+0x09f4 -> s0.readReg64 .x30`) on `stageP1ProgPlaced ext`:
`IdentityKeyStore::get_local_registration_id` `.error e` unwind through `hskitOk.regIdFutDrop`,
`p2_err6b_a_hooks_placed_wp`, `hDropSs3` (dropping the unpromoted Bob `SessionState` at
`coroPtr + 0x4f8..0x650`), `p2_err6b_b_1568_hooks_placed_wp` (freeing Kyber keypair), and
`stageP2_err_funnel_hooks_placed_ok`. -/
theorem p2_arm6_err_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A 0#64} {skit : IdentitySelfStoreSpec ikit}
    (hH : StageP2ClosureHooksPlaced A ext)
    (hDropSs3 :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
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
       sessionStateAt A (coroPtr + 0x4f8#64) G st ∗
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
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
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
          speErrAt skit.regIdErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
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
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine p2_call_nopanic_rocl_steps_frame_placed (x := ()) (T := emp)
    hCode1 (hskitOk.regIdFutDrop (by decide))
    hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (skit.regIdBoxAt_memRegion regIdFutPtr idStorePtr 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hstep3 := p2_err6b_a_hooks_placed_wp ext hH s2 coroPtr regIdFutPtr
    (0#64 + skit.regIdFutVtOff) (skit.regIdErr.w0 e) skit.regIdBoxSize
    (skit.regIdErr.w0_ne_ok e) skit.regIdBoxSize_ne_zero skit.regIdBoxSize_lt
    hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx24_cs2.trans hx24_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx0_3, hx19_3, hx22_3, hx23_3, hx25_3, _,
    hx27_3, hx28_3, _, hx30_3, hvregs3_2⟩
  have hsp3_al : s3.spAligned = true := by simp only [State.spAligned, hsp3, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  refine p2_call_nopanic_lscl_steps_frame_placed
    (spec := dropSessionStructureLocal2Spec A)
    (x := (⟨coroPtr + 0x4f8#64, G, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0x4f8#64) G st ∗
      A.pool ∗ stackAt s3.sp dropSessionStructureLocal2Stack)
    hCode3 hDropSs3
    hpc3 hrun3 hsp3_al hx30_3
    rfl hx0_3 (by rw [hsp3]; sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp3]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4_3 => ?_
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
  have hstep5 := p2_err6b_b_1568_hooks_placed_wp ext hH s4 coroPtr pkBuf skBuf outPtr
    (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
    (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)
    hpc4 hrun4 hsp4_align hx19_4 hx22_4 hx23_4 hx27_4 hx28_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_qp_frame_placed hCode4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hCode5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5_4, hx10_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5,
    hx25_5, hx26_5, hx27_5, hx28_5, _, hvregs5_4⟩
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5, ← hsp_eq]; exact hsp_align
  have hx25_5' : s5.readReg64 .x25 = sp + 0x210#64 := by
    rw [hx25_5, hx25_cs4, hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs5 : calleeSavedVRegs s5 = calleeSavedVRegs s0 := by
    rw [hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s5.pc = stageP1EntryPlaced + 0x1648#64 at hpc5
  have hfunnel := stageP2_err_funnel_hooks_placed_ok (Qp := fun _ _ => False) hH s0 s5 sp coroPtr outPtr prevCap prevPtr
    (skit.regIdErr.w0 e) (skit.regIdErr.w1 e) (skit.regIdErr.w2 e)
    (skit.regIdErr.w3 e) (skit.regIdErr.w4 e) (skit.regIdErr.w5 e)
    (((skit.regIdErr.w1 e).extractLsb' 0 32).zeroExtend 64) outPtr
    b_2c0 b_390 b_4f2 hprev_lt
    (skit.regIdErr.w0_ne_pending e) (skit.regIdErr.w0_ne_ok e)
    (p2_zeroExtend32_extractLsb_lo (skit.regIdErr.w1 e))
    hCode5 hsp5 hpc5 hrun5 hsp5_align
    hx10_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5' hx26_5 hx27_5 hx28_5 hvregs5
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hCodef⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hCodef))))
  refine p2_bind_sepWPp_steps_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcsf, hvregsf, hCodef⟩
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr5_4, htr4_3, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hCodef⟩
  rw [p2_dropSs3Stack_eq sp]
  sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
