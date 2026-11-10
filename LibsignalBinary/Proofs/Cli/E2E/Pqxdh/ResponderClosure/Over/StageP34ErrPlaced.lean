/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrAPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSession
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

/-!
# Placed Stage P4 `store_session` `Ok` Epilogue on 1-Element `previous_sessions`

Proves the `[LibsignalPlacement]` Stage P4 `Ok` epilogue `stageP4_storeSession_ok_tail_prev1_vregs_placed`
(`+0x444 → s0.readReg64 .x30`) over `prevVecAt [enc]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Record.Serialization.SerializeBodyAux
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0 stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Placed Stage P4 `store_session` `Ok` Epilogue (`+0x444 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 800000 in
theorem p4_seg4d_ok_ext_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s : State) (coroPtr storeSessionFutPtr storeSessionFutVt futSize futAlign
    curStateWord0 ptextMid0 ptextMid1 u_370 u_378 : BitVec 64)
    (ptextHead ptextTail u_380 : BitVec 32)
    (hsize_nz : futSize ≠ 0#64)
    (hcur_ne : curStateWord0 + 1#64 ≠ 0#64)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x444#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = storeSessionFutPtr)
    (hx23 : s.readReg64 .x23 = storeSessionFutVt)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
       ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
       ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
       ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
       ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
       ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
       ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗
       ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₃₂ u_380) ∗
       A.live storeSessionFutPtr futSize.toNat futAlign.toNat ∗
       memRegion storeSessionFutPtr futSize.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xf8#64) ↦₆₄ curStateWord0) ∗
          ((coroPtr + 0x280#64) ↦₃₂ ptextHead) ∗
          ((coroPtr + 0x284#64) ↦₆₄ ptextMid0) ∗
          ((coroPtr + 0x28c#64) ↦₆₄ ptextMid1) ∗
          ((coroPtr + 0x294#64) ↦₃₂ ptextTail) ∗
          ((storeSessionFutVt + 0x8#64) ↦₆₄ᵣ futSize) ∗
          ((storeSessionFutVt + 0x10#64) ↦₆₄ᵣ futAlign) ∗
          ((s.sp + 0x370#64) ↦₆₄ ptextMid0) ∗
          ((s.sp + 0x378#64) ↦₆₄ ptextMid1) ∗
          ((s.sp + 0x380#64) ↦₃₂ ptextTail) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = ptextHead.zeroExtend 64 ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryP34Placed + 0x48c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsize_beq : (futSize == 0#64) = false := beq_eq_false_iff_ne.mpr hsize_nz
  have hcur_beq : (curStateWord0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcur_ne
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = storeSessionFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = storeSessionFutVt := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hx28' : s.readReg64 (Reg.gpr 28#5) = 0xfffffffffffffffe#64 := hx28
  dsimp only [dpClosureEntryP34Placed] at hpc
  wp_steps
  wp_call hdealloc (storeSessionFutPtr, futSize.toNat, futAlign.toNat)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [dpClosureEntryP34Placed, arm64_norm], by simp_all [arm64_norm]⟩

private theorem p4_fold_sret_ok_prev1_placed {A : RustAlloc} (outPtr ptCap ptPtr w_24 : BitVec 64)
    (u_384 w_2c : BitVec 32) (pt : List (BitVec 8))
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64) :
    (outPtr ↦₆₄ 0xfffffffffffffffe#64) ∗
    ((outPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
    ((outPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
    ((outPtr + 0x14#64) ↦₆₄
      ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
    ((outPtr + 0x1c#64) ↦₆₄ (u_384 ++ (BitVec.ofNat 64 pt.length).extractLsb' 32 32)) ∗
    ((outPtr + 0x24#64) ↦₆₄ w_24) ∗
    ((outPtr + 0x2c#64) ↦₃₂ w_2c) ∗
    (ptPtr ↦ₛ pt) ∗
    (if ptCap = 0#64 then emp
     else A.live ptPtr ptCap.toNat 1 ∗
       memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ⊢
    vecResultAt A outPtr (.ok pt) := by
  rw [pointsTo32_pair_out1c']
  have hreplace :
      ∀ {A B R P Q : SepProp},
        (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
    intro A B R P Q hab hp hq
    rw [hp, ← hq]
    exact sepConj_mono_left hab
  exact Entails.trans
    (hreplace (memRegion16_out20_fold' outPtr w_24 u_384 w_2c) (by sep_focus) (by ac_rfl))
    (p4_fold_decResultAt_ok A outPtr ptCap ptPtr pt hpt_le hcap_lt hptr_nz)

private theorem sp370_words_entails_memRegion36_prev1_placed (sp v0 v1 v2 v3 : BitVec 64)
    (v4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ v0) ∗
    ((sp + 0x378#64) ↦₆₄ v1) ∗
    ((sp + 0x380#64) ↦₆₄ v2) ∗
    ((sp + 0x388#64) ↦₆₄ v3) ∗
    ((sp + 0x390#64) ↦₃₂ v4) ⊢
    memRegion (sp + 0x370#64) 36 := by
  have h := stagingCellsAt_entails_memRegion36 (sp + 0x370#64) v0 v1 v2 v3 v4
  unfold stagingCellsAt at h
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

set_option maxHeartbeats 1200000 in
/-- Placed Stage P4 `+0x444 → s0.readReg64 .x30` `Ok` epilogue on 1-element `prevVecAt [enc]`. -/
theorem stageP4_storeSession_ok_tail_prev1_vregs_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (coroPtr boxPtr outPtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryP34Placed + 0x444#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = boxPtr)
    (hx23 : s.readReg64 .x23 = 0#64 + kit.storeFutVtOff)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
       ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live boxPtr kit.storeBoxSize 8 ∗
       memRegion boxPtr kit.storeBoxSize ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp (storeSessionCallStack kit))
      (fun sf P_f =>
        Steps (lsProg_518 ext) s sf ∧
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          memRegion (coroPtr + 0x280#64) 24 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          vecResultAt A outPtr (.ok pt) ∗
          ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp (storeSessionCallStack kit)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  refine SepWPp.with_steps ?_
  have hbox_eq : kit.storeBoxSize = (BitVec.ofNat 64 kit.storeBoxSize).toNat :=
    (Nat.mod_eq_of_lt kit.storeBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  let ptLen := BitVec.ofNat 64 pt.length
  have hpt_coro :
      ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗ ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
      ((coroPtr + 0x290#64) ↦₆₄ ptLen) =
      ((coroPtr + 0x280#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗
      ((coroPtr + 0x284#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)) ∗
      ((coroPtr + 0x28c#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)) ∗
      ((coroPtr + 0x294#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words3_eq_head_mid_tail (coroPtr + 0x280#64) ptCap ptPtr ptLen
  have hbox_sz :
      A.live boxPtr kit.storeBoxSize 8 ∗ memRegion boxPtr kit.storeBoxSize =
      A.live boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat (8#64 : BitVec 64).toNat ∗
        memRegion boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat := by
    rw [← hbox_eq]; rfl
  refine P3P4.SepWPp.weaken_frame (p4_sessionStateAt_expose_cap_ne A (coroPtr + 0xf8#64) G st)
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcap_ne => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_coro) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hbox_sz) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq' s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w_390 => SepWPp.exists_elim fun w_388 =>
    SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p4_seg4d_ok_ext_placed_wp ext hdealloc s coroPtr boxPtr
    (0#64 + kit.storeFutVtOff) (BitVec.ofNat 64 kit.storeBoxSize) 8#64
    G.localIk.cap
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    u_370 u_378 (ptCap.extractLsb' 0 32) (ptLen.extractLsb' 32 32) u_380
    kit.storeBoxSize_ne_zero hcap_ne hpc hrun hsp_al hx19 hx21 hx23 hx24 hx28
  refine bind_sepWP_lscro_frame hcro hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, _, _, hlr1, hvregs1_0⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (p4_sessionStateAt_expose_cap A (coroPtr + 0xf8#64) G st).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hpt_coro.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (coro280_words3_entails_memRegion24 coroPtr ptCap ptPtr ptLen) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_dropSS3 kit s.sp hsp_ub)) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  simp only [sepConj_assoc]
  refine call_lscro_nopanic
    (x := (⟨coroPtr + 0xf8#64, G, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) G st ∗ A.pool ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hcro1 (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hDropSS3)
    hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_dropSS3 kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (pointsTo32_pair_sp380' s.sp (ptLen.extractLsb' 32 32) u_384))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion48_eq_exists_pollCells outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2] using hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = (ptCap.extractLsb' 0 32).zeroExtend 64 :=
    hx22_cs2.trans hx22_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun o6_u => SepWPp.exists_elim fun o5_u =>
    SepWPp.exists_elim fun o4_u => SepWPp.exists_elim fun o3_u =>
    SepWPp.exists_elim fun o2_u => SepWPp.exists_elim fun o1_u =>
    SepWPp.exists_elim fun w0_u => ?_
  have hstep3 := p4_seg4e_prev1_of_dealloc_placed_wp ext hdealloc s2 coroPtr outPtr prevCap prevPtr
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    (u_384 ++ ptLen.extractLsb' 32 32) w_388
    w0_u o2_u o3_u o4_u o5_u
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (ptCap.extractLsb' 0 32) w_390 o1_u o6_u b_2c0 enc
    hpc2 hrun2 hsp2_al hx19_2 hx22_2 hx25_2 hx26_2
  rw [hsp2] at hstep3
  unfold pollCellsAt at *
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hstep3 ⊢
  refine bind_sepWP_lscro_frame hcro2 hstep3 (by sep_focus)
    fun sf hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
    hx27f, hx28f, hx29f, _, hvregsf⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp370_words_entails_memRegion36_prev1_placed s.sp
      (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
      (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
      (u_384 ++ ptLen.extractLsb' 32 32) w_388 w_390)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (p4_fold_sret_ok_prev1_placed outPtr ptCap ptPtr w_388 u_384 w_390 pt hpt_le hcap_lt hptr_nz)
    (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
  refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
    hvregsf.trans (hvregs_cs2.trans (hvregs1_0.trans hvregs)), hcrof⟩
  exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
