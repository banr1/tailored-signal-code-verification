/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrA
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Stage P2 Over-Path Error Unwind Arms 3 and 4

Proves the populated-`SessionRecord` Stage P2 error unwind paths for `PreKeyStore::get_pre_key`
(Arm 3, `+0x09c4 → x30`) and `IdentityKeyStore::get_identity_key_pair` (Arm 4, `+0x07bc → x30`),
dropping the loaded Kyber keypair and `SessionRecord` via the `+0x1648` error funnel.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxRecDepth 200000
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

/-! ## Error Arm 3 (`+0x09c4 → x30`) -/

set_option maxHeartbeats 1200000 in
/-- Error Arm 3 (`+0x09c4 → s0.readReg64 .x30`): `PreKeyStore::get_pre_key` error unwind on a
populated `SessionRecord`. -/
theorem p2_over_arm3_err_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {pkKit : PreKeyStoreSpec A img.base}
    (hA : AllocContracts img.base A ext) (hpkOk : PreKeyStoreKitOkImgE img pkKit ext)
    (s0 s : State) (sp coroPtr outPtr preKeyStorePtr opkFutPtr pkBuf skBuf ctxPtr
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : pkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x9c4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (preKeyGetPollOutAt pkKit (sp + 0xa90#64) (.error e) ∗ memRegion (sp + 0xac8#64) 8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + pkKit.getFutVtOff)) ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       ((img.base + pkKit.getFutVtOff) ↦₆₄ᵣ (img.base + pkKit.getFutDropOff)) ∗
       ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + pkKit.getFutVtOff)) ∗
          ((img.base + pkKit.getFutVtOff) ↦₆₄ᵣ (img.base + pkKit.getFutDropOff)) ∗
          ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
          ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
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
          speErrAt pkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp := by
  dsimp only [preKeyGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err56_to_preKeyRecordOut64 pkKit.getErr (sp + 0xa90#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ac8 => ?_
  have hstep1 := p2_err3a_ext_wp img.base ext s coroPtr ctxPtr opkFutPtr
    (img.base + pkKit.getFutVtOff) (img.base + pkKit.getFutDropOff)
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) u_ac8
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0
    (pkKit.getFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx26 hx27
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_cells6_a90 sp 0xffffffffffffffff#64
      (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
      (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) u_ac8)
    (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ hpkOk.getFutDrop hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hF1, hsym1⟩ (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (pkKit.getBoxAt_memRegion opkFutPtr preKeyStorePtr opkId 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hstep3 := p2_err3b_1568_gen_wp img.base ext hA s2 coroPtr opkFutPtr
    (img.base + pkKit.getFutVtOff) pkBuf skBuf outPtr
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) pkKit.getBoxSize
    pkKit.getBoxSize_ne_zero pkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1) (hx26_cs2.trans hx26_1)
    (hx27_cs2.trans hx27_1) hx28_2
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_over_err_funnel_ext_ok (Qp := fun _ _ => False)
    hA s0 s3 sp coroPtr outPtr
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) (pkKit.getErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt hb
    (pkKit.getErr.w0_ne_pending e) (pkKit.getErr.w0_ne_ok e) rfl
    ⟨hF3, hsym3⟩ hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hinvf⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hinvf))))
  refine p2_bind_sepWPp_nopanic_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf ⟨htrf, hspf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hinvf⟩
  dsimp only [speErrAt]; sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## Error Arm 4 (`+0x07bc → x30`) -/

set_option maxHeartbeats 1200000 in
/-- Error Arm 4 (`+0x07bc → s0.readReg64 .x30`): `IdentityKeyStore::get_identity_key_pair` error
unwind on a populated `SessionRecord`. -/
theorem p2_over_arm4_err_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A img.base} {skit : IdentitySelfStoreSpec ikit}
    (hA : AllocContracts img.base A ext) (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (s0 s : State) (sp coroPtr msgPtr ctxPtr outPtr
    idStorePtr idKpFutPtr pkBuf skBuf fp
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 b_fp78 : BitVec 8) (e : skit.KpErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x7bc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx24 : s.readReg64 .x24 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64) (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s.readReg64 .x27 = ctxPtr) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x3c8#64) 7 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + skit.kpFutVtOff)) ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
       ((img.base + skit.kpFutVtOff) ↦₆₄ᵣ (img.base + skit.kpFutDropOff)) ∗
       ((img.base + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((img.base + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 72 ∗
          memRegion (sp + 0x3c8#64) 7 ∗
          memRegion (fp + 0xffffffffffffff80#64) 9 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + skit.kpFutVtOff)) ∗
          ((img.base + skit.kpFutVtOff) ↦₆₄ᵣ (img.base + skit.kpFutDropOff)) ∗
          ((img.base + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
          ((img.base + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
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
          speErrAt skit.kpErr outPtr e ∗ logOff img ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
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
  have hstep1 := p2_err4a_fp_ext_wp img.base ext s coroPtr msgPtr ctxPtr idKpFutPtr
    (img.base + skit.kpFutVtOff) (img.base + skit.kpFutDropOff) fp
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0
    u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 opkId
    b0 b1 b2 b3 b4 b5 b6 b63 s0_b s1_b s2_b s3_b s4_b s5_b s6_b b_fp78
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) w6
    (skit.kpFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx24_s hx26 hx27 hx29
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
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
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ (subroutine_ok_inImage_of_subroutine_ok img hskitOk.kpFutDrop)
    hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hF1, hsym1⟩ (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (skit.kpBoxAt_memRegion idKpFutPtr idStorePtr 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hstep3 := p2_err4b_1568_gen_wp img.base ext hA s2 coroPtr idKpFutPtr
    (img.base + skit.kpFutVtOff) pkBuf skBuf outPtr
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w4 e) (skit.kpErr.w5 e) skit.kpBoxSize
    skit.kpBoxSize_ne_zero skit.kpBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx20_cs2.trans hx20_1) (hx21_cs2.trans hx21_1)
    (hx22_cs2.trans hx22_1) (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1)
    (hx27_cs2.trans hx27_1) hx28_2
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_over_err_funnel_ext_ok (Qp := fun _ _ => False)
    hA s0 s3 sp coroPtr outPtr
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) (skit.kpErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt hb
    (skit.kpErr.w0_ne_pending e) (skit.kpErr.w0_ne_ok e) rfl
    ⟨hF3, hsym3⟩ hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hinvf⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hinvf))))
  refine p2_bind_sepWPp_nopanic_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf ⟨htrf, hspf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hinvf⟩
  dsimp only [speErrAt]; sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## `StageP2ClosureHooks` Variants -/

set_option maxHeartbeats 1200000 in
theorem p2_over_arm3_err_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {pkKit : PreKeyStoreSpec A img.base}
    (hH : StageP2ClosureHooks A img.base ext)
    (hDropSs3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (hpkOk : PreKeyStoreKitOkImgE img pkKit ext)
    (s0 s : State) (sp coroPtr outPtr preKeyStorePtr opkFutPtr pkBuf skBuf ctxPtr
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : pkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x9c4#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (preKeyGetPollOutAt pkKit (sp + 0xa90#64) (.error e) ∗ memRegion (sp + 0xac8#64) 8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + pkKit.getFutVtOff)) ∗
       A.live opkFutPtr pkKit.getBoxSize 8 ∗
       pkKit.getBoxAt opkFutPtr preKeyStorePtr opkId 1#8 ∗
       ((img.base + pkKit.getFutVtOff) ↦₆₄ᵣ (img.base + pkKit.getFutDropOff)) ∗
       ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
       ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 16 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ opkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + pkKit.getFutVtOff)) ∗
          ((img.base + pkKit.getFutVtOff) ↦₆₄ᵣ (img.base + pkKit.getFutDropOff)) ∗
          ((img.base + pkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 pkKit.getBoxSize) ∗
          ((img.base + pkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
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
          speErrAt pkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp := by
  dsimp only [preKeyGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err56_to_preKeyRecordOut64 pkKit.getErr (sp + 0xa90#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ac8 => ?_
  have hstep1 := p2_err3a_ext_wp img.base ext s coroPtr ctxPtr opkFutPtr
    (img.base + pkKit.getFutVtOff) (img.base + pkKit.getFutDropOff)
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) u_ac8
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0
    (pkKit.getFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx26 hx27
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_cells6_a90 sp 0xffffffffffffffff#64
      (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
      (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) u_ac8)
    (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ hpkOk.getFutDrop hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hF1, hsym1⟩ (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (pkKit.getBoxAt_memRegion opkFutPtr preKeyStorePtr opkId 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hstep3 := p2_err3b_1568_hooks_wp img.base ext hH s2 coroPtr opkFutPtr
    (img.base + pkKit.getFutVtOff) pkBuf skBuf outPtr
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) pkKit.getBoxSize
    pkKit.getBoxSize_ne_zero pkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1) (hx26_cs2.trans hx26_1)
    (hx27_cs2.trans hx27_1) hx28_2
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_over_err_funnel_hooks_ok (Qp := fun _ _ => False)
    hH hDropSs3 s0 s3 sp coroPtr outPtr
    (pkKit.getErr.w0 e) (pkKit.getErr.w1 e) (pkKit.getErr.w2 e)
    (pkKit.getErr.w3 e) (pkKit.getErr.w4 e) (pkKit.getErr.w5 e) (pkKit.getErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt hb
    (pkKit.getErr.w0_ne_pending e) (pkKit.getErr.w0_ne_ok e) rfl
    ⟨hF3, hsym3⟩ hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hinvf⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hinvf))))
  refine p2_bind_sepWPp_nopanic_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf ⟨htrf, hspf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hinvf⟩
  dsimp only [speErrAt]; sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem p2_over_arm4_err_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {ikit : IdentityStoreSpec A img.base} {skit : IdentitySelfStoreSpec ikit}
    (hH : StageP2ClosureHooks A img.base ext)
    (hDropSs3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (hskitOk : IdentitySelfStoreKitOkI img ikit skit ext)
    (s0 s : State) (sp coroPtr msgPtr ctxPtr outPtr
    idStorePtr idKpFutPtr pkBuf skBuf fp
    v_b0 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 : BitVec 64)
    (opkId : BitVec 32) (b_2c0 b_390 b_4f2 b_fp78 : BitVec 8) (e : skit.KpErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x7bc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx24 : s.readReg64 .x24 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64) (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64)
    (hx27 : s.readReg64 .x27 = ctxPtr) (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = fp)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x3c8#64) 7 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_fp80) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_fp78) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + skit.kpFutVtOff)) ∗
       A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
       ((img.base + skit.kpFutVtOff) ↦₆₄ᵣ (img.base + skit.kpFutDropOff)) ∗
       ((img.base + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
       ((img.base + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       A.live pkBuf 1568 1 ∗ memRegion pkBuf 1568 ∗
       A.live skBuf 3168 1 ∗ memRegion skBuf 3168 ∗
       ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗ ((sp + 0xc0#64) ↦₆₄ u_c0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       cells (sp + 0xa90#64) 6 ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 72 ∗
          memRegion (sp + 0x3c8#64) 7 ∗
          memRegion (fp + 0xffffffffffffff80#64) 9 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + skit.kpFutVtOff)) ∗
          ((img.base + skit.kpFutVtOff) ↦₆₄ᵣ (img.base + skit.kpFutDropOff)) ∗
          ((img.base + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
          ((img.base + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
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
          speErrAt skit.kpErr outPtr e ∗ logOff img ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
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
  have hstep1 := p2_err4a_fp_ext_wp img.base ext s coroPtr msgPtr ctxPtr idKpFutPtr
    (img.base + skit.kpFutVtOff) (img.base + skit.kpFutDropOff) fp
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0
    u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 u_fp80 opkId
    b0 b1 b2 b3 b4 b5 b6 b63 s0_b s1_b s2_b s3_b s4_b s5_b s6_b b_fp78
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) w6
    (skit.kpFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx24_s hx26 hx27 hx29
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
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
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ (subroutine_ok_inImage_of_subroutine_ok img hskitOk.kpFutDrop)
    hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hF1, hsym1⟩ (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (skit.kpBoxAt_memRegion idKpFutPtr idStorePtr 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp)) (by sep_focus) ?_
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hstep3 := p2_err4b_1568_hooks_wp img.base ext hH s2 coroPtr idKpFutPtr
    (img.base + skit.kpFutVtOff) pkBuf skBuf outPtr
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w4 e) (skit.kpErr.w5 e) skit.kpBoxSize
    skit.kpBoxSize_ne_zero skit.kpBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx20_cs2.trans hx20_1) (hx21_cs2.trans hx21_1)
    (hx22_cs2.trans hx22_1) (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1)
    (hx27_cs2.trans hx27_1) hx28_2
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_dropSs3Stack_eq sp).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_over_err_funnel_hooks_ok (Qp := fun _ _ => False)
    hH hDropSs3 s0 s3 sp coroPtr outPtr
    (skit.kpErr.w0 e) (skit.kpErr.w1 e) (skit.kpErr.w2 e)
    (skit.kpErr.w3 e) (skit.kpErr.w4 e) (skit.kpErr.w5 e) (skit.kpErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt hb
    (skit.kpErr.w0_ne_pending e) (skit.kpErr.w0_ne_ok e) rfl
    ⟨hF3, hsym3⟩ hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hinvf⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hinvf))))
  refine p2_bind_sepWPp_nopanic_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf ⟨htrf, hspf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hinvf⟩
  dsimp only [speErrAt]; sep_norm; exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
