/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSessionProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsStoreSession

/-!
# Stage P4.4 Dispatch Proof with `calleeSavedVRegs`

Proves `stageP4_storeSession_ok_tail_vregs` and `stageP4_storeSession_dispatch_vregs_kits`,
threading `calleeSavedVRegs` (`D8..D15`) across `Ok(())` and `Err(())` returns to
`s0.readReg64 .x30`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

private theorem coro_f8_eq_e0_add_18 (coroPtr : BitVec 64) :
    coroPtr + 0xf8#64 = (coroPtr + 0xe0#64) + 0x18#64 := by
  bv_omega

private theorem coro_e8_eq_e0_add_8 (coroPtr : BitVec 64) :
    coroPtr + 0xe8#64 = (coroPtr + 0xe0#64) + 0x8#64 := by
  bv_omega

private theorem coro_f0_eq_e0_add_10 (coroPtr : BitVec 64) :
    coroPtr + 0xf0#64 = (coroPtr + 0xe0#64) + 0x10#64 := by
  bv_omega

private theorem p4_fold_sret_ok {A : RustAlloc} (outPtr ptCap ptPtr w_24 : BitVec 64)
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

private theorem sp370_words_entails_memRegion36 (sp v0 v1 v2 v3 : BitVec 64) (v4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ v0) ∗
    ((sp + 0x378#64) ↦₆₄ v1) ∗
    ((sp + 0x380#64) ↦₆₄ v2) ∗
    ((sp + 0x388#64) ↦₆₄ v3) ∗
    ((sp + 0x390#64) ↦₃₂ v4) ⊢
    memRegion (sp + 0x370#64) 36 := by
  have h := stagingCellsAt_entails_memRegion36 (sp + 0x370#64) v0 v1 v2 v3 v4
  unfold stagingCellsAt at h
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

set_option maxHeartbeats 800000 in
theorem stageP4_storeSession_ok_tail_vregs_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (s0 s : State)
    (coroPtr boxPtr outPtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x444#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = boxPtr)
    (hx23 : s.readReg64 .x23 = img.base + kit.storeFutVtOff)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
       ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live boxPtr kit.storeBoxSize 8 ∗
       memRegion boxPtr kit.storeBoxSize ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp (storeSessionCallStack kit))
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          memRegion (coroPtr + 0xf8#64) 344 ∗
          memRegion (coroPtr + 0x280#64) 24 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          vecResultAt A outPtr (.ok pt) ∗
          ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp (storeSessionCallStack kit)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
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
  refine SepWPp.weaken_frame (p4_sessionStateAt_expose_cap_ne A (coroPtr + 0xf8#64) G st)
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcap_ne => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hpt_coro) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hbox_sz) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq' s.sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub))
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w_390 => SepWPp.exists_elim fun w_388 =>
    SepWPp.exists_elim fun u_384 => SepWPp.exists_elim fun u_380 =>
    SepWPp.exists_elim fun u_378 => SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p4_seg4d_ok_vregs_ext_wp_p4 img.base ext hA s coroPtr boxPtr
    (img.base + kit.storeFutVtOff) (BitVec.ofNat 64 kit.storeBoxSize) 8#64
    G.localIk.cap
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    u_370 u_378 (ptCap.extractLsb' 0 32) (ptLen.extractLsb' 32 32) u_380
    kit.storeBoxSize_ne_zero hcap_ne hpc hrun hsp_al hx19 hx21 hx23 hx24 hx28
  refine SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, _, _, hlr1, hvregs1_0⟩
  refine SepWPp.weaken_frame
    (Entails.of_eq (p4_sessionStateAt_expose_cap A (coroPtr + 0xf8#64) G st).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hpt_coro.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (coro280_words3_entails_memRegion24 coroPtr ptCap ptPtr ptLen) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_alloc kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_dropSS3 kit s.sp hsp_ub)) (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  simp only [sepConj_assoc]
  refine SepWPp.call_frame_frozen_nopanic
    (x := (⟨coroPtr + 0xf8#64, G, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) G st ∗ A.pool ∗
          stackAt s.sp dropSessionStructureLocal2Stack)
    hF1 hsym1 hDropSS3 hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_dropSS3 kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (pointsTo32_pair_sp380' s.sp (ptLen.extractLsb' 32 32) u_384))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (memRegion48_eq_exists_pollCells outPtr)) (by sep_focus) ?_
  refine SepWPp.weaken_frame
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
    SepWPp.exists_elim fun o3_u => SepWPp.exists_elim fun o2_u =>
    SepWPp.exists_elim fun o1_u => SepWPp.exists_elim fun o0_u =>
    SepWPp.exists_elim fun w0_u => ?_
  have hstep3 := p4_seg4e_vregs_ext_wp img.base ext s2 coroPtr outPtr prevStatesPtr
    (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
    (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
    (u_384 ++ ptLen.extractLsb' 32 32) w_388
    w0_u o1_u o2_u o3_u o5_u
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (ptCap.extractLsb' 0 32) w_390 o0_u o6_u b_2c0
    hpc2 hrun2 hsp2_al hx19_2 hx22_2 hx25_2 hx26_2
  rw [hsp2] at hstep3
  unfold pollCellsAt
  simp only [BitVec.add_zero, sepConj_assoc] at hstep3 ⊢
  refine SepWPp.bind_sepWP_frame hF2 hsym2 hstep3 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
    hx27f, hx28f, hx29f, _, hvregsf_2⟩
  refine SepWPp.weaken_frame
    (p4_fold_sret_ok outPtr ptCap ptPtr w_388 u_384 w_390 pt hpt_le hcap_lt hptr_nz)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp370_words_entails_memRegion36 s.sp
      (ptPtr.extractLsb' 0 32 ++ ptCap.extractLsb' 32 32)
      (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb' 32 32)
      (u_384 ++ ptLen.extractLsb' 32 32) w_388 w_390)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
  refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
    hvregsf_2.trans (hvregs_cs2.trans (hvregs1_0.trans hvregs)), hFf, hsymf⟩
  exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩

theorem stageP4_storeSession_ok_tail_vregs {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base)
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (s0 s : State)
    (coroPtr boxPtr outPtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x444#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = boxPtr)
    (hx23 : s.readReg64 .x23 = img.base + kit.storeFutVtOff)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
       ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live boxPtr kit.storeBoxSize 8 ∗
       memRegion boxPtr kit.storeBoxSize ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp (storeSessionCallStack kit))
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
          ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
          memRegion (coroPtr + 0xf8#64) 344 ∗
          memRegion (coroPtr + 0x280#64) 24 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          vecResultAt A outPtr (.ok pt) ∗
          ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp (storeSessionCallStack kit)) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      Qp :=
  stageP4_storeSession_ok_tail_vregs_p4 img ext kit (.of_allocContracts hA) hDropSS3 s0 s coroPtr
    boxPtr outPtr prevStatesPtr ptCap ptPtr b_2c0 pt G st Qp hpt_le hcap_lt hptr_nz hsp_ub hF hsym
    hpc hrun hsp_align hx19 hx21 hx23 hx24 hx25 hx26 hx28 hvregs

private theorem coro2c8_16_split_eq (coroPtr : BitVec 64) :
    memRegion (coroPtr + 0x2c8#64) 16 =
      ∃∗ u_2d0 : BitVec 64, ∃∗ u_2c8 : BitVec 64,
        ((coroPtr + 0x2c8#64) ↦₆₄ u_2c8) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ u_2d0) := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2c8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x2d0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (coroPtr + 0x2c8#64),
      ProofLib.memRegion_eight (coroPtr + 0x2d0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem coro2c8_16_fold (coroPtr v0 v1 : BitVec 64) :
    ((coroPtr + 0x2c8#64) ↦₆₄ v0) ∗ ((coroPtr + 0x2d0#64) ↦₆₄ v1) ⊢
      memRegion (coroPtr + 0x2c8#64) 16 := by
  rw [ProofLib.memRegion_split' (b := coroPtr + 0x2c8#64) (n := 8) (k := 8)
        (b' := coroPtr + 0x2d0#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

set_option maxHeartbeats 1200000 in
/-- Substage P4.4 dispatch (`SessionStore::store_session`, `+0x3cc → s0.readReg64 .x30`)
preserving `calleeSavedVRegs`. -/
theorem stageP4_storeSession_dispatch_vregs_kits_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hsVt : SessionOnlyVtablesOk img kit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (sst0 : kit.StoreState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ok : kit.addrOk peer.val)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hfs : FsAt kit.envOk Qfs (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x3cc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4StoreSessionOkPost img kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        prevStatesPtr pt peer sst0 ss ∗ F) →
      Q sf Pf)
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4StoreSessionErrPost img kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        prevStatesPtr peer sst0 ss ∗ F) →
      Q sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4StoreSessionPre img kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt peer sst0 G ss ∗ F)
      Q (PanicOomProp s0) := by
  have herr_ub : stageP4ErrUnwindStack ≤ 2 ^ 64 :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hsp_ub
  have hbox_eq : kit.storeBoxSize = (BitVec.ofNat 64 kit.storeBoxSize).toNat :=
    (Nat.mod_eq_of_lt kit.storeBoxSize_lt).symm
  have hsp_al : s.spAligned = true := hsp_align
  refine SepWPp.intro_ro (R_ro := storeSessionVtablesAt img kit)
    (fun hm => storeSessionVtablesAt_intro hsVt hF hm) ?_
  unfold stageP4StoreSessionPre stageP4StoreSessionShared storeSessionVtablesAt
  simp only [sepConj_assoc]
  have h4a := p4_seg4a_vregs_ext_wp img.base ext s coroPtr remoteAddrPtr sessionStorePtr kit.ss_vt
    (img.base + kit.storeShimOff) hpc hrun hx19
  refine SepWPp.bind_sepWP_frame_steps h4a (by sep_focus)
    fun s1 P1 hpc1 hrun1 hst1 ⟨hP1, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1,
      hx24_1, hx25_1, hx26_1, hx27_1, _, _, hlr1, hvregs1_0⟩ => ?_
  refine SepWPp.weaken_frame hP1 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_shim kit s.sp hsp_ub))
    (by sep_focus) ?_
  have hvregs1 : calleeSavedVRegs s1 = calleeSavedVRegs s0 := hvregs1_0.trans hvregs
  have hF1 : img.FrozenLoaded s1 := hF.of_keepsFrozen hst1.keepsFrozen
  have hsym1 : s1.symtab = img.symtab := hst1.symtab_eq.trans hsym
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_al
  have htr_pfx1 : s0.trace <+: s1.trace := htr1 ▸ htr_pfx
  refine SepWPp.call_inImage_frame
    (x := ({ self := sessionStorePtr, addrA := remoteAddrPtr,
             recA := coroPtr + 0xe0#64 } : StoreShimCall))
    (T := A.pool ∗ stackAt s.sp kit.storeShimStack)
    (φ := s1.readReg64 .x0 = sessionStorePtr ∧ s1.readReg64 .x1 = remoteAddrPtr ∧
          s1.readReg64 .x2 = coroPtr + 0xe0#64)
    hF1 hsym1 htr_pfx1 hkit.storeShim hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [kitStoreShimSpec]; rw [hsp1]; exact Entails.of_eq (by ac_rfl))
    ⟨hx0_1, hx1_1, hx2_1⟩ (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 hsp2_al hcs2 hF2 hsym2 hst2 => ?_)
  dsimp only [kitStoreShimSpec]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_shim kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (coro2c8_16_split_eq coroPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_2d0 => SepWPp.exists_elim fun u_2c8 => ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, _, _, hvregs_cs2⟩
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs_cs2.trans hvregs1
  let boxPtr := s2.readReg64 .x0
  have h4b := p4_seg4b_vregs_ext_wp img.base ext s2 coroPtr ctxPtr boxPtr
    (img.base + kit.storeFutVtOff) (img.base + kit.storePollOff) u_2c8 u_2d0
    hpc2 hrun2 rfl hx1_2 (hx19_cs2.trans hx19_1) (hx27_cs2.trans (hx27_1.trans hx27))
  refine SepWPp.bind_sepWP_frame_steps h4b (by sep_focus)
    fun s3 P3 hpc3 hrun3 hst3 ⟨hP3, hsp3_2, htr3_2, hx0_3, _, hx8_3, hx19_3,
      hx24_3, hx25_3, hx26_3, _, _, _, hlr3, hvregs3_2⟩ => ?_
  refine SepWPp.weaken_frame hP3 (by sep_focus) ?_
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3_2.trans hvregs2
  have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
  have hF3 : img.FrozenLoaded s3 := hF2.of_keepsFrozen hst3.keepsFrozen
  have hsym3 : s3.symtab = img.symtab := hst3.symtab_eq.trans hsym2
  have hsp3_al : s3.spAligned = true := by simpa [State.spAligned, hsp3] using hsp_al
  have hst_to3 : Steps (tripleRatchetProgAtExt img.base ext) s s3 :=
    hst1.trans (hst2.trans hst3)
  have htr_to3 : s3.trace = s.trace := by rw [htr3_2, htr2_1, htr1]
  have htr_pfx3 : s0.trace <+: s3.trace := htr_to3 ▸ htr_pfx
  have henv3 : kit.envOk s3.fs.files := (hfs.of_steps_nil hst_to3 htr_to3).envOk_here
  have hrec_fold :
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      sessionStateAt A (coroPtr + 0xf8#64) G ss.state ⊢
      sessionRecordAt A (coroPtr + 0xe0#64) ⟨0#64, prevStatesPtr, some G⟩ ⟨some ss⟩ := by
    rw [coro_e8_eq_e0_add_8, coro_f0_eq_e0_add_10, coro_f8_eq_e0_add_18]
    exact p4_sessionRecordAt_some_prev_of_state A (coroPtr + 0xe0#64) prevStatesPtr G ss
      hprev_nz hExtra
  have hrec_unfold :
      sessionRecordAt A (coroPtr + 0xe0#64) ⟨0#64, prevStatesPtr, some G⟩ ⟨some ss⟩ ⊢
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      sessionStateAt A (coroPtr + 0xf8#64) G ss.state := by
    rw [coro_e8_eq_e0_add_8, coro_f0_eq_e0_add_10, coro_f8_eq_e0_add_18]
    exact p4_sessionRecordAt_some_prev_to_state A (coroPtr + 0xe0#64) prevStatesPtr G ss
  refine SepWPp.weaken_frame hrec_fold (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_poll kit s.sp hsp_ub))
    (by sep_focus) ?_
  let pollCall : StorePollCall :=
    { fut := boxPtr
      out := s.sp + 0x3e0#64
      call := { addrA := remoteAddrPtr, addr := peer, recA := coroPtr + 0xe0#64,
                g := ⟨0#64, prevStatesPtr, some G⟩, record := ⟨some ss⟩ } }
  refine SepWPp.call_inImage_frame
    (x := (pollCall, sessionStorePtr, sst0))
    (T := kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 0#8 ∗
          kit.storeAt sessionStorePtr sst0 ∗ memRegion (s.sp + 0x3e0#64) 48 ∗
          protocolAddressAt A peer remoteAddrPtr ∗
          sessionRecordAt A (coroPtr + 0xe0#64) ⟨0#64, prevStatesPtr, some G⟩ ⟨some ss⟩ ∗
          A.pool ∗ stackAt s.sp kit.storePollStack)
    (φ := kit.envOk s3.fs.files ∧
          s3.readReg64 .x0 = boxPtr ∧ s3.readReg64 .x8 = s.sp + 0x3e0#64 ∧
          kit.RecOk ⟨some ss⟩ ∧ kit.addrOk peer.val)
    hF3 hsym3 htr_pfx3 hkit.storePoll hpc3 hrun3 hsp3_al hlr3
    (by
      dsimp only [kitStorePollSpecE, withEnvPre, kitStorePollSpec, pollCall]
      rw [hsp3]
      refine Entails.pure_left fun ⟨henv, hx0', hx8', hrok, haok⟩ => ?_
      refine Entails.pure_right henv (Entails.pure_right ⟨hx0', hx8', hrok, haok⟩ ?_)
      exact Entails.of_eq (by ac_rfl))
    ⟨henv3, hx0_3, by rw [hx8_3, hsp2], hrec_ok, haddr_ok⟩ (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 hsp4_al hcs4 hF4 hsym4 hst4 => ?_)
  dsimp only [kitStorePollSpecE, withEnvPre, kitStorePollSpec, pollCall]
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hrel, htr4_3⟩ => ?_
  refine SepWPp.weaken_frame hrec_unfold (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (stack_storeSession_to_poll kit s.sp hsp_ub).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x340#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_360s => SepWPp.exists_elim fun u_358s =>
    SepWPp.exists_elim fun u_350s => SepWPp.exists_elim fun u_348s =>
    SepWPp.exists_elim fun u_340s => ?_
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := hvregs_cs4.trans hvregs3
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx24_4 : s4.readReg64 .x24 = s4.sp + 0x370#64 := by
    rw [hx24_cs4, hx24_3, hx24_cs2, hx24_1, hx24, hsp4]
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1, hx25, hsp4]
  have hx26_4 : s4.readReg64 .x26 = outPtr :=
    hx26_cs4.trans (hx26_3.trans (hx26_cs2.trans (hx26_1.trans hx26)))
  have hbox_dealloc :
      A.live boxPtr kit.storeBoxSize 8 ∗
      kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8 ⊢
      A.live boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat (8#64 : BitVec 64).toNat ∗
      memRegion boxPtr (BitVec.ofNat 64 kit.storeBoxSize).toNat := by
    refine Entails.trans (sepConj_mono_right
      (kit.storeBoxAt_memRegion boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8)) ?_
    rw [← hbox_eq]; exact Entails.refl _
  have hfold_2c8 := coro2c8_16_fold coroPtr boxPtr (img.base + kit.storeFutVtOff)
  rcases ans with ⟨⟩ | ⟨⟩
  · -- Err () arm: +0x3f8 → storeFutDrop → +0x444 → +0x550 → s0.x30
    refine SepWPp.weaken_frame (storePollErr_unpack_repack img.base (s.sp + 0x3e0#64))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun o1 =>
      SepWPp.exists_elim fun o2 => SepWPp.exists_elim fun o3 =>
      SepWPp.exists_elim fun o4 => SepWPp.exists_elim fun o5 =>
      SepWPp.exists_elim fun o6 => SepWPp.exists_elim fun H_err =>
      SepWPp.pure_elim fun ⟨hw0_eq, hrepack⟩ => ?_
    have hw0_ne_pend : w0 + 3#64 ≠ 0#64 := by rw [hw0_eq]; decide
    have hw0_ne_ok : w0 + 2#64 ≠ 0#64 := by rw [hw0_eq]; decide
    have h4c := p4_seg4c_gen_vregs_ext_wp img.base ext s4 coroPtr boxPtr
      (img.base + kit.storeFutVtOff) (img.base + kit.storeFutDropOff) w0
      o2 o3 o4 o5 u_340s u_348s u_350s u_358s o1 o6 u_360s
      hw0_ne_pend (kit.storeFutDrop_ne_zero hb)
      hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h4c
    refine SepWPp.bind_sepWP_frame_steps h4c (by sep_focus)
      fun s5 P5 hpc5 hrun5 hst5 ⟨hP5, hsp5_4, htr5_4, _, hx19_5, hx21_5, hx22_5,
        hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    refine SepWPp.weaken_frame hP5 (by sep_focus) ?_
    have hF5 : img.FrozenLoaded s5 := hF4.of_keepsFrozen hst5.keepsFrozen
    have hsym5 : s5.symtab = img.symtab := hst5.symtab_eq.trans hsym4
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5_4] using hsp_al
    refine SepWPp.call_futDrop hF5 hsym5 hkit.storeFutDrop hpc5 hrun5 hsp5_al hlr5
      fun s6 hpc6 hrun6 hsp6_5 hsp6_al hcs6 htr6_5 hF6 hsym6 hst6 => ?_
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5_4
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, hx22_cs6, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    refine SepWPp.weaken_frame hbox_dealloc (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_storeSession_to_errUnwind kit s.sp hsp_ub))
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub))
      (by sep_focus) ?_
    have h4d_err := p4_seg4d_err_vregs_ext_wp_p4 img.base ext hA s6 coroPtr boxPtr
      (img.base + kit.storeFutVtOff) (BitVec.ofNat 64 kit.storeBoxSize) 8#64 w0
      kit.storeBoxSize_ne_zero hw0_ne_ok hpc6 hrun6 hsp6_al
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      (hx28_cs6.trans hx28_5)
    rw [hsp6] at h4d_err
    refine SepWPp.bind_sepWP_frame_steps h4d_err (by sep_focus)
      fun s7 P7 hpc7 hrun7 hst7 ⟨hP7, hsp7_6, htr7_6, hx8_7, hx19_7, hx22_7,
        hx24_7, hx25_7, hx26_7, _, hx28_7, _, hvregs7_6⟩ => ?_
    refine SepWPp.weaken_frame hP7 (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (stack_errUnwind_to_alloc s.sp herr_ub).symm)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hsp7 : s7.sp = s.sp := hsp7_6
    have hF7 : img.FrozenLoaded s7 := hF6.of_keepsFrozen hst7.keepsFrozen
    have hsym7 : s7.symtab = img.symtab := hst7.symtab_eq.trans hsym6
    have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7]; exact hsp_align
    have hx22_7' : s7.readReg64 .x22 = o1.zeroExtend 64 :=
      hx22_7.trans (hx22_cs6.trans hx22_5)
    have hx24_7' : s7.readReg64 .x24 = s7.sp + 0x370#64 := by
      rw [hx24_7, hx24_cs6, hx24_5, hsp7]
    have hx25_7' : s7.readReg64 .x25 = s7.sp + 0x210#64 := by
      rw [hx25_7, hx25_cs6, hx25_5, hsp7]
    have hx26_7' : s7.readReg64 .x26 = outPtr :=
      hx26_7.trans (hx26_cs6.trans (hx26_5.trans hx26_4))
    have hunwind := stageP4_err_unwind_550_vregs_ok_p4 img ext hA hDropSS3 s0 s7 coroPtr
      (s.sp + 0x340#64) ptCap ptPtr outPtr w0 prevStatesPtr
      o2 o3 o4 o5 o1 o6 b_2c0 pt G ss.state (PanicOomProp s0)
      hpt_le herr_ub hF7 hsym7 hpc7 hrun7 hsp7_align hx8_7 hx19_7 hx22_7'
      hx24_7' hx25_7' hx26_7' hx28_7
      (hvregs7_6.trans (hvregs_cs6.trans (hvregs5_4.trans hvregs4)))
    rw [hsp7] at hunwind
    refine SepWPp.frame_ret_oom hunwind (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_unw, hP1, hspf, htrf, hcsf, hvregsf, hFf, hsymf⟩ => ?_
    have hst_all : Steps (tripleRatchetProgAtExt img.base ext) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans (hst7.trans hst_unw))))
    have htr_all : sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) := by
      rw [htrf, htr7_6, htr6_5, htr5_4, htr4_3, htr_to3]
    refine hErr sf _ hst_all hrel hpcf hrunf hspf htr_all hcsf hvregsf hFf hsymf ?_
    have hreplace :
        ∀ {A B R P Q : SepProp},
          (A ⊢ B) → P = A ∗ R → B ∗ R = Q → (P ⊢ Q) := by
      intro A B R P Q hab hp hq
      rw [hp, ← hq]
      exact sepConj_mono_left hab
    refine Entails.trans (sepConj_mono_left hP1) ?_
    unfold stageP4StoreSessionErrPost stageP4StoreSessionShared storeSessionVtablesAt
    simp only [sepConj_assoc]
    rw [stack_storeSession_to_errUnwind kit s.sp hsp_ub]
    exact hreplace (hrepack outPtr) (by sep_focus) (by ac_rfl)
  · -- Ok () arm: +0x3f8 → storeFutDrop → stageP4_storeSession_ok_tail_vregs → s0.x30
    refine SepWPp.weaken_frame
      (Entails.of_eq (storePollOk_eq_exists_pollCells img.base (s.sp + 0x3e0#64)))
      (by sep_focus) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun o1 => SepWPp.exists_elim fun o6 =>
      SepWPp.exists_elim fun o5 => SepWPp.exists_elim fun o4 =>
      SepWPp.exists_elim fun o3 => SepWPp.exists_elim fun o2 => ?_
    have h4c := p4_seg4c_gen_vregs_ext_wp img.base ext s4 coroPtr boxPtr
      (img.base + kit.storeFutVtOff) (img.base + kit.storeFutDropOff)
      0xfffffffffffffffe#64 o2 o3 o4 o5 u_340s u_348s u_350s u_358s o1 o6 u_360s
      (by decide) (kit.storeFutDrop_ne_zero hb)
      hpc4 hrun4 hsp4_al hx19_4 hx24_4 hx25_4
    rw [hsp4] at h4c
    refine SepWPp.bind_sepWP_frame_steps h4c (by sep_focus)
      fun s5 P5 hpc5 hrun5 hst5 ⟨hP5, hsp5_4, htr5_4, _, hx19_5, hx21_5, _,
        hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, _, hlr5, hvregs5_4⟩ => ?_
    refine SepWPp.weaken_frame hP5 (by sep_focus) ?_
    have hF5 : img.FrozenLoaded s5 := hF4.of_keepsFrozen hst5.keepsFrozen
    have hsym5 : s5.symtab = img.symtab := hst5.symtab_eq.trans hsym4
    have hsp5_al : s5.spAligned = true := by simpa [State.spAligned, hsp5_4] using hsp_al
    refine SepWPp.call_futDrop hF5 hsym5 hkit.storeFutDrop hpc5 hrun5 hsp5_al hlr5
      fun s6 hpc6 hrun6 hsp6_5 _ hcs6 htr6_5 hF6 hsym6 hst6 => ?_
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5_4
    have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, _, hx23_cs6, hx24_cs6, hx25_cs6,
      hx26_cs6, _, hx28_cs6, _, hvregs_cs6⟩
    have hbox_dealloc_ok :
        A.live boxPtr kit.storeBoxSize 8 ∗
        kit.storeBoxAt boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8 ⊢
        A.live boxPtr kit.storeBoxSize 8 ∗ memRegion boxPtr kit.storeBoxSize :=
      sepConj_mono_right
        (kit.storeBoxAt_memRegion boxPtr sessionStorePtr remoteAddrPtr (coroPtr + 0xe0#64) 1#8)
    refine SepWPp.weaken_frame hbox_dealloc_ok (by sep_focus) ?_
    refine SepWPp.weaken_frame (stagingCellsAt_entails_memRegion36 (s.sp + 0x340#64) _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (pollCellsAt_entails_memRegion48 (s.sp + 0x3e0#64) _ _ _ _ _ _ _)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame hfold_2c8 (by sep_focus) ?_
    have hx24_6' : s6.readReg64 .x24 = s6.sp + 0x370#64 := by
      rw [hx24_cs6, hx24_5, hsp6]
    have hx25_6' : s6.readReg64 .x25 = s6.sp + 0x210#64 := by
      rw [hx25_cs6, hx25_5, hsp6]
    have hx26_6' : s6.readReg64 .x26 = outPtr :=
      hx26_cs6.trans (hx26_5.trans hx26_4)
    have htail := stageP4_storeSession_ok_tail_vregs_p4 img ext kit hA hDropSS3 s0 s6
      coroPtr boxPtr outPtr prevStatesPtr ptCap ptPtr b_2c0 pt G ss.state (PanicOomProp s0)
      hpt_le hcap_lt hptr_nz hsp_ub hF6 hsym6 hpc6 hrun6 hsp6_align
      (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
      hx24_6' hx25_6' hx26_6' (hx28_cs6.trans hx28_5)
      (hvregs_cs6.trans (hvregs5_4.trans hvregs4))
    rw [hsp6] at htail
    refine SepWPp.frame_ret_oom htail (by sep_focus)
      fun sf P1 hpcf hrunf ⟨hst_tail, hP1, hspf, htrf, hcsf, hvregsf, hFf, hsymf⟩ => ?_
    have hst_all : Steps (tripleRatchetProgAtExt img.base ext) s sf :=
      hst_to3.trans (hst4.trans (hst5.trans (hst6.trans hst_tail)))
    have htr_all : sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) := by
      rw [htrf, htr6_5, htr5_4, htr4_3, htr_to3]
    refine hOk sf _ hst_all hrel hpcf hrunf hspf htr_all hcsf hvregsf hFf hsymf ?_
    refine Entails.trans (sepConj_mono_left hP1) ?_
    unfold stageP4StoreSessionOkPost stageP4StoreSessionShared storeSessionVtablesAt
    simp only [sepConj_assoc]
    exact Entails.of_eq (by ac_rfl)

theorem stageP4_storeSession_dispatch_vregs_kits {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A img.base)
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hsVt : SessionOnlyVtablesOk img kit)
    {Qfs : Prop}
    (s0 s : State)
    (coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr prevStatesPtr ptCap ptPtr : BitVec 64)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (sst0 : kit.StoreState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (F : SepProp) (Q : State → SepProp → Prop)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ok : kit.addrOk peer.val)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : storeSessionCallStack kit ≤ 2 ^ 64)
    (hfs : FsAt kit.envOk Qfs (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x3cc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hOk : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4StoreSessionOkPost img kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        prevStatesPtr pt peer sst0 ss ∗ F) →
      Q sf Pf)
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()) →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4StoreSessionErrPost img kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        prevStatesPtr peer sst0 ss ∗ F) →
      Q sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4StoreSessionPre img kit s0 s coroPtr outPtr remoteAddrPtr sessionStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt peer sst0 G ss ∗ F)
      Q (PanicOomProp s0) :=
  stageP4_storeSession_dispatch_vregs_kits_p4 img ext Scope encRecord kit (.of_allocContracts hA)
    hDropSS3 hkit hsVt s0 s coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr prevStatesPtr
    ptCap ptPtr b_2c0 pt peer sst0 G ss F Q hb hprev_nz hExtra hrec_ok haddr_ok hpt_le hcap_lt
    hptr_nz hsp_ub hfs hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hvregs hOk hErr

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
