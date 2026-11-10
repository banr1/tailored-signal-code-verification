/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb

/-!
# Relocatable Stage P2 Store-Error Unwind Arms 3–4

Proves placed `SepWPp` unwinds to `s0.readReg64 .x30` on Block `518` (`stageP1ProgPlaced ext`) for
Store-Error Arms 3 (`+0x09c4`) and 4 (`+0x07bc`).
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
/-- Arm 3 (`+0x09c4 -> s0.readReg64 .x30`) on `stageP1ProgPlaced ext`:
`PreKeyStore::get_pre_key` `.error e` unwind through `hpkOk.getFutDrop`,
`p2_err3b_1568_hooks_placed_wp` (freeing Kyber keypair), and `stageP2_err_funnel_hooks_placed_ok`. -/
theorem p2_arm3_err_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {pkKit : PreKeyStoreSpec A 0#64}
    (hH : StageP2ClosureHooksPlaced A ext) (hpkOk : PreKeyStoreKitPlacedOk pkKit ext)
    (s0 s : State) (sp coroPtr outPtr prevCap prevPtr preKeyStorePtr opkFutPtr pkBuf skBuf ctxPtr
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : pkKit.GetErr)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x9c4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (preKeyGetPollOutAt pkKit (sp + 0xa90#64) (.error e) ∗ memRegion (sp + 0xac8#64) 8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
       ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (0#64 + pkKit.getFutVtOff)) ∗
          ((0#64 + pkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + pkKit.getFutDropOff)) ∗
          ((0#64 + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
          ((0#64 + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ pkKit.getErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((sp + 0xb8#64) ↦₆₄ pkKit.getErr.w2 e) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ pkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt pkKit.getErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  dsimp only [preKeyGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err56_to_preKeyRecordOut64 pkKit.getErr (sp + 0xa90#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ac8 => ?_
  have hstep1 := p2_err3a_ext_placed_wp ext s coroPtr ctxPtr opkFutPtr
    (0#64 + pkKit.getFutVtOff) (0#64 + pkKit.getFutDropOff)
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) u_ac8
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0
    (pkKit.getFutDrop_ne_zero rfl) hpc hrun hsp_align hx19 hx21 hx23 hx26 hx27
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_cells6_a90 sp 0xffffffffffffffff#64
      (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
      (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) u_ac8)
    (by sep_focus) ?_
  refine p2_call_nopanic_rocl_steps_frame_placed (x := ()) (T := emp)
    hCode1 (hpkOk.getFutDrop (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (pkKit.getBoxAt_memRegion opkFutPtr preKeyStorePtr opkId 1#8) (by sep_focus) ?_
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hstep3 := p2_err3b_1568_hooks_placed_wp ext hH s2 coroPtr opkFutPtr
    (0#64 + pkKit.getFutVtOff) pkBuf skBuf outPtr
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) pkKit.getBoxSize
    pkKit.getBoxSize_ne_zero pkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1) (hx26_cs2.trans hx26_1)
    (hx27_cs2.trans hx27_1) hx28_2
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s3.pc = stageP1EntryPlaced + 0x1648#64 at hpc3
  have hfunnel := stageP2_err_funnel_hooks_placed_ok (Qp := fun _ _ => False) hH s0 s3 sp coroPtr outPtr prevCap prevPtr
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) (pkKit.getErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 hprev_lt
    (pkKit.getErr.w0_ne_pending e) (pkKit.getErr.w0_ne_ok e) rfl
    hCode3 hsp3 hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hCodef⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hCodef))))
  refine p2_bind_sepWPp_steps_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcsf, hvregsf, hCodef⟩
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hCodef⟩
  dsimp only [speErrAt]; sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Arm 4 (`+0x07bc -> s0.readReg64 .x30`) on `stageP1ProgPlaced ext`:
`IdentityKeyStore::get_identity_key_pair` `.error e` unwind through `hskitOk.kpFutDrop`,
`p2_err4b_1568_hooks_placed_wp` (freeing `idKpFutPtr` and Kyber keypair), and
`stageP2_err_funnel_hooks_placed_ok`. -/
theorem p2_arm4_err_hooks_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A 0#64} {skit : IdentitySelfStoreSpec ikit}
    (hH : StageP2ClosureHooksPlaced A ext) (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (s0 s : State) (sp coroPtr msgPtr ctxPtr outPtr prevCap prevPtr
    idStorePtr idKpFutPtr pkBuf skBuf fp
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 b_fp78 : BitVec 8) (e : skit.KpErr)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hsp_eq : s.sp = sp)
    (hpc : s.pc = stageP1EntryPlaced + 0x7bc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx24 : s.readReg64 .x24 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64) (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s.readReg64 .x27 = ctxPtr) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x3c8#64) 7 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
       ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
       ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       (if prevCap = 0 then emp
        else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x100#64) 336 ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 72 ∗
          memRegion (sp + 0x3c8#64) 7 ∗
          memRegion (fp + 0xffffffffffffff80#64) 9 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
          ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
          ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
          ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ skit.kpErr.w4 e) ∗ ((sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((sp + 0xb8#64) ↦₆₄ skit.kpErr.w2 e) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ skit.kpErr.w3 e) ∗
          cells (sp + 0xa90#64) 6 ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt skit.kpErr outPtr e ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine SepWPp.weaken_frame (p2_kpPollErr_unpack skit (sp + 0x3e0#64) e) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun b1 =>
    SepWPp.exists_elim fun b2 => SepWPp.exists_elim fun b3 =>
    SepWPp.exists_elim fun b4 => SepWPp.exists_elim fun b5 =>
    SepWPp.exists_elim fun b6 => SepWPp.exists_elim fun w6 =>
    SepWPp.exists_elim fun b63 => ?_
  refine SepWPp.weaken_frame (p2_memRegion7_to_bytes7At (sp + 0x3c8#64)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun s0_b => SepWPp.exists_elim fun s1_b =>
    SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s3_b =>
    SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s5_b =>
    SepWPp.exists_elim fun s6_b => ?_
  have hx24_s : s.readReg64 .x24 = s.sp + 0x370#64 := by rw [hx24, hsp_eq]
  have hstep1 := p2_err4a_fp_ext_placed_wp ext s coroPtr msgPtr ctxPtr idKpFutPtr
    (0#64 + skit.kpFutVtOff) (0#64 + skit.kpFutDropOff) fp
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0
    u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 opkId
    b0 b1 b2 b3 b4 b5 b6 b63 s0_b s1_b s2_b s3_b s4_b s5_b s6_b b_fp78
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) w6
    (skit.kpFutDrop_ne_zero rfl) hpc hrun hsp_align hx19 hx21 hx23 hx24_s hx26 hx27 hx29
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  have h72 := p2_keyPair64Unaligned_to_memRegion72 (sp + 0x3e0#64) b0 b1 b2 b3 b4 b5 b6 b63
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) w6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h72
  refine SepWPp.weaken_frame h72 (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_bytes7At_to_memRegion7 (sp + 0x3c8#64) b0 b1 b2 b3 b4 b5 b6)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_fp80_to_memRegion9 fp w6 b63) (by sep_focus) ?_
  refine p2_call_nopanic_rocl_steps_frame_placed (x := ()) (T := emp)
    hCode1 (hskitOk.kpFutDrop (by decide))
    hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]; exact (pure_true_sepConj emp).symm)
    True.intro (by sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (skit.kpBoxAt_memRegion idKpFutPtr idStorePtr 1#8) (by sep_focus) ?_
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hstep3 := p2_err4b_1568_hooks_placed_wp ext hH s2 coroPtr idKpFutPtr
    (0#64 + skit.kpFutVtOff) pkBuf skBuf outPtr
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w4 e) (skit.kpErr.w5 e) skit.kpBoxSize
    skit.kpBoxSize_ne_zero skit.kpBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx20_cs2.trans hx20_1) (hx21_cs2.trans hx21_1)
    (hx22_cs2.trans hx22_1) (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1)
    (hx27_cs2.trans hx27_1) hx28_2
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  change s3.pc = stageP1EntryPlaced + 0x1648#64 at hpc3
  have hfunnel := stageP2_err_funnel_hooks_placed_ok (Qp := fun _ _ => False) hH s0 s3 sp coroPtr outPtr prevCap prevPtr
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) (skit.kpErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 hprev_lt
    (skit.kpErr.w0_ne_pending e) (skit.kpErr.w0_ne_ok e) rfl
    hCode3 hsp3 hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hCodef⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hCodef))))
  refine p2_bind_sepWPp_steps_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨htrf, hspf, hcsf, hvregsf, hCodef⟩
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hCodef⟩
  dsimp only [speErrAt]; sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
