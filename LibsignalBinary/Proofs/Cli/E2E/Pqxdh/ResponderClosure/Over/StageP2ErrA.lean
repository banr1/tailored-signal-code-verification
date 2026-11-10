/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Untrusted
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Stage P2 Over-Path Error Unwind Funnel and Error Arms 1–2

Proves the populated-`SessionRecord` Stage P2 error unwind funnel (`+0x1648 → x30`) and store-error
unwind Arms 1 (`get_signed_pre_key`, `+0x0f38 → x30`) and 2 (`get_kyber_pre_key`, `+0x0998 → x30`),
dropping `sessionStateAt` at `coroPtr + 0xf8` and deallocating any spare `previous_sessions` buffer.
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

/-! ## Populated-Record Error Unwind Funnel (`+0x1648 → x30`) -/

set_option maxHeartbeats 1200000 in
/-- Populated-record Stage P2 error funnel (`+0x1648 → s0.readReg64 .x30`): drops `sessionStateAt`
at `coroPtr + 0xf8` and `prevSessionsEmptyAt` at `coroPtr`, writes `speWordsAt outPtr`, and restores
the caller stack pointer and callee-saved registers. -/
theorem stageP2_over_err_funnel_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hA : AllocContracts img.base A ext)
    (s0 s : State) (sp coroPtr outPtr
    w0 w1 w2 w3 w4 w5 r23 u_c8 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (herr_ne_neg3 : w0 ≠ 0xfffffffffffffffd#64)
    (herr_ne_neg2 : w0 ≠ 0xfffffffffffffffe#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1648#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx10 : s.readReg64 .x10 = w2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w1 >>> 32)
    (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w2 >>> 32)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ w4) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ w3) ∗
       memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       A.pool ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ w4) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ w3) ∗
          memRegion (sp + 0x370#64) 36 ∗
          cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗
          logOff img ∗
          A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        ImgCallInv img sf)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  have hstep1 := Kits.p2_err_tail_a_ext_wp img.base ext s coroPtr outPtr w0 w1 w2 w4 w5 r23 u_c8 b_4f2
    herr_ne_neg3 hr23_lo hpc hrun hsp_align
    hx10 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27
  rw [hsp_eq] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  have hinv1 : ImgCallInv img s1 := ⟨hF1, hsym1⟩
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  have hdrop := Kits.drop_process_prekey_impl_state1_ext_ok (b := img.base) (ext := ext)
  have hstk48 : stackAt sp allocHookStack =
      stackAt (sp - 48#64) (allocHookStack - 48) ∗ cells (sp - 48#64) 6 :=
    ProofLib.stackAt_split_cells sp (allocHookStack - 48) 6 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_nopanic_steps_frame
    (spec := dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hinv1 hdrop hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [dropProcessPrekeyImplState1Spec]
      rw [hsp1, show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl])
    hx0_1 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec]
  rw [hsp1,
      show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl,
      sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = w0 := hx20_cs2.trans hx20_1
  have hx21_2 : s2.readReg64 .x21 = w4 >>> 8 := hx21_cs2.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = w2 := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = r23 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = w1 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx27_2 : s2.readReg64 .x27 = w5 := hx27_cs2.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  have hstep3 := Kits.p2_err_tail_b1_ext_wp img.base ext s2 coroPtr outPtr w0 w1 w2 w3 w4 w5 r23
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8 b_390
    hb herr_ne_neg2 hr23_lo hpc2 hrun2 hsp2_align
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx19_3, _, hx21_3, hx25_3, hx26_3, hx28_3, _, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hc250 := cells6_fold (coroPtr + 0x250#64) w0 w1 w2 w3 w4 w5
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hx21_3' : s3.readReg64 .x21 = s3.sp + 0x370#64 := by rw [hx21_3, hsp3]
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_3, hsp3]
  have hx28_3' : s3.readReg64 .x28 = s3.sp + 0xa90#64 := by rw [hx28_3, hsp3]
  have hstep4 := Matched.p2_err_tail_b2_to_3588_ext_wp img.base ext s3 coroPtr w0 outPtr
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    u370 u378 u380 u388 (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) u390
    hpc3 hrun3 hsp3_align hx19_3 hx21_3' hx25_3' hx26_3 hx28_3'
  rw [hsp3] at hstep4
  refine p2_bind_sepWP_qp_frame hF3 hsym3 hstep4 (by sep_focus)
    fun s4 _ hpc4 hrun4 hF4 hsym4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4, htr4_3, hvregs4_3, hx19_4, hx22_4, hx25_4, hx26_4, hx28_4, _, _⟩
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (sp_a90_rejoin sp w0 w1 w2 w3 w4 w5) (by sep_focus) ?_
  have hdropTail := Matched.closure_err_drop_record_tail_ext_ok (Qp := fun _ _ => False)
    hA (GenP3.drop_session_structure3_ok_ext hA) s0 s4
    sp coroPtr outPtr w0
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) b_2c0
    g recG recSt
    ⟨hF4, hsym4⟩ hsp4 hsp_lt hpc4 hrun4 hsp4_align
    hx19_4 hx22_4 hx25_4 hx26_4 hx28_4
  refine p2_bind_sepWPp_nopanic_frame hdropTail (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (speWordsAt_realign_outPtr outPtr w0 w1 w2 w3 w4 w5)) (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  have hvregs_all : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine ⟨by rw [htrf, htr4_3, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregs_all, hinvf⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## Store-Error Unwind Arms 1 and 2 -/

set_option maxHeartbeats 1200000 in
/-- Error Arm 1 (`+0x0f38 → s0.readReg64 .x30`): `SignedPreKeyStore::get_signed_pre_key` error or
signature-mismatch unwind on a populated `SessionRecord`. -/
theorem p2_over_arm1_err_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {spkKit : SignedPreKeyStoreSpec A img.base}
    (hA : AllocContracts img.base A ext) (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (s0 s : State) (sp coroPtr outPtr spkStorePtr spkFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (signedPreKeyId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : spkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf38#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (spkGetPollOutAt spkKit (sp + 0x3e0#64) (.error e) ∗
       memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr signedPreKeyId 1#8 ∗
       ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
       ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 368 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
          ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
          ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
          ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt spkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  dsimp only [spkGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err88_to_preKeyRecordOut64 spkKit.getErr (sp + 0x3e0#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_418 => ?_
  have hstep1 := p2_err1a_ext_wp img.base ext s coroPtr spkFutPtr
    (img.base + spkKit.getFutVtOff) (img.base + spkKit.getFutDropOff) (spkKit.getErr.w0 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0
    (spkKit.getErr.w1 e) (spkKit.getErr.w2 e) (spkKit.getErr.w3 e)
    (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) u_418
    (spkKit.getFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (p2_memRegion_420_join sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_memRegion368 sp 0xffffffffffffffff#64
      (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
      (spkKit.getErr.w3 e) (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) u_418)
    (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ hspkOk.getFutDrop hpc1 hrun1 hsp1_al hx30_1
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
    (spkKit.getBoxAt_memRegion spkFutPtr spkStorePtr signedPreKeyId 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  have hstep3 := p2_err1b_gen_wp img.base ext hA s2 coroPtr spkFutPtr
    (img.base + spkKit.getFutVtOff) outPtr
    (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
    (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) ctxPtr u_a8 u_c0 spkKit.getBoxSize
    spkKit.getBoxSize_ne_zero spkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1) (hx26_cs2.trans hx26_1)
    (hx27_cs2.trans (hx27_1.trans hx27)) (hx28_cs2.trans hx28_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_over_err_funnel_ext_ok (Qp := fun _ _ => False)
    hA s0 s3 sp coroPtr outPtr
    (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
    (spkKit.getErr.w3 e) (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) (spkKit.getErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt hb
    (spkKit.getErr.w0_ne_pending e) (spkKit.getErr.w0_ne_ok e) rfl
    ⟨hF3, hsym3⟩ hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hinvf⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hinvf))))
  refine p2_bind_sepWPp_nopanic_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf ⟨htrf, hspf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hinvf⟩
  dsimp only [speErrAt]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Error Arm 2 (`+0x0998 → s0.readReg64 .x30`): `KyberPreKeyStore::get_kyber_pre_key` error
unwind on a populated `SessionRecord`. -/
theorem p2_over_arm2_err_ext_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {kpkKit : KyberPreKeyStoreSpec A img.base}
    (hA : AllocContracts img.base A ext) (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (s0 s : State) (sp coroPtr outPtr kyberStorePtr kyberFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8) (e : kpkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x998#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (kpkGetPollOutAt kpkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
       ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
       ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 368 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
          ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
          ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
          ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt kpkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  dsimp only [kpkGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err88_to_preKeyRecordOut64 kpkKit.getErr (sp + 0x3e0#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_418 => ?_
  have hstep1 := p2_err2a_ext_wp img.base ext s coroPtr kyberFutPtr
    (img.base + kpkKit.getFutVtOff) (img.base + kpkKit.getFutDropOff) (kpkKit.getErr.w0 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e) (kpkKit.getErr.w3 e)
    (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) u_418
    (kpkKit.getFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (p2_memRegion_420_join sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_memRegion368 sp 0xffffffffffffffff#64
      (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
      (kpkKit.getErr.w3 e) (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) u_418)
    (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ hkpkOk.getFutDrop hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hF1, hsym1⟩ (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (kpkKit.getBoxAt_memRegion kyberFutPtr kyberStorePtr kyberPreKeyId 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  have hstep3 := p2_err2b_gen_wp img.base ext hA s2 coroPtr kyberFutPtr
    (img.base + kpkKit.getFutVtOff) outPtr
    (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
    (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) ctxPtr u_c0 b_4f1 kpkKit.getBoxSize
    kpkKit.getBoxSize_ne_zero kpkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1)
    (hx27_cs2.trans (hx27_1.trans hx27)) (hx28_cs2.trans hx28_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_over_err_funnel_ext_ok (Qp := fun _ _ => False)
    hA s0 s3 sp coroPtr outPtr
    (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
    (kpkKit.getErr.w3 e) (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e)
    (((kpkKit.getErr.w1 e).extractLsb' 0 32).zeroExtend 64) outPtr
    b_2c0 b_390 b_4f2 g recG recSt hb
    (kpkKit.getErr.w0_ne_pending e) (kpkKit.getErr.w0_ne_ok e)
    (p2_zeroExtend32_extractLsb_lo (kpkKit.getErr.w1 e))
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
/-- Drops `sessionStateAt` at `coroPtr + 0xf8` and `prevSessionsEmptyAt` at `coroPtr` across
`+0x3588 → s0.readReg64 .x30` under `StageP2ClosureHooks`. -/
theorem p2_over_err_drop_record_tail_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hH : StageP2ClosureHooks A img.base ext)
    (hDropSs3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (s0 s : State)
    (sp coroPtr outPtr errTag w_370 w_378 w_380 w_388 : BitVec 64)
    (w_22 w_390 : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       ((sp + 0x370#64) ↦₆₄ w_370) ∗
       ((sp + 0x378#64) ↦₆₄ w_378) ∗
       ((sp + 0x380#64) ↦₆₄ w_380) ∗
       ((sp + 0x388#64) ↦₆₄ w_388) ∗
       ((sp + 0x390#64) ↦₃₂ w_390) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((outPtr + 0x0#64) ↦₆₄ errTag) ∗
          ((outPtr + 0x8#64) ↦₃₂ w_22) ∗
          ((outPtr + 0xc#64) ↦₆₄ w_370) ∗
          ((outPtr + 0x14#64) ↦₆₄ w_378) ∗
          ((outPtr + 0x1c#64) ↦₆₄ w_380) ∗
          ((outPtr + 0x24#64) ↦₆₄ w_388) ∗
          ((outPtr + 0x2c#64) ↦₃₂ w_390) ∗
          memRegion (sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        ImgCallInv img sf)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  refine SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A coroPtr g) (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := sessionStateAt_split_localIk_cap A (coroPtr + 0xf8#64) recG recSt
  refine SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun hcap_lt => ?_
  have hcap_ne : recG.localIk.cap ≠ 0xffffffffffffffff#64 := P3P4.cap_ne_noneCap_of_lt hcap_lt
  have hto_call := p2_err_drop_ss_to_call_ext_wp img.base ext s coroPtr recG.localIk.cap
    hcap_ne hpc hrun hsp_align hx19
  refine SepWPp.bind_sepWP_steps_frame hinv hto_call (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame
    (spec := dropSessionStructureLocal2Spec A)
    (x := ⟨coroPtr + 0xf8#64, recG, recSt⟩)
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗
      stackAt sp dropSessionStructureLocal2Stack)
    hinv1 hDropSs3 hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hvregs_cs2.trans (congrArg VRegFile.calleeSaved hvregs1)
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by
    rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by
    rw [hsp2]; exact hx25_cs2.trans (hx25_1.trans hx25)
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  rw [stack_dropSS_to_alloc sp hdss_le, savedRegsAt_eq_sp_c70 sp s0]
  refine SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj]
    have htail := p2_err_tail_prev_zero_ext_wp img.base ext s2 coroPtr outPtr errTag g.prevPtr
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv2 htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine ⟨?_, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hinvf⟩
    refine Entails.trans (P3P4.entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact P3P4.entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))
  · simp only [hcap, ↓reduceIte]
    have htail := Kits.p3_err_tail_prev_dealloc_hooks_wp img.base ext hH s2 coroPtr outPtr errTag
      g.prevCap g.prevPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0 hcap hprev_lt
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine SepWPp.ret_sepWP_steps_frame hinv2 htail (by sep_focus)
      fun sf _ _ _ hinvf hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _, hvregsf⟩
    refine ⟨?_, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hinvf⟩
    refine Entails.trans (P3P4.entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact P3P4.entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem stageP2_over_err_funnel_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hH : StageP2ClosureHooks A img.base ext)
    (hDropSs3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (s0 s : State) (sp coroPtr outPtr
    w0 w1 w2 w3 w4 w5 r23 u_c8 : BitVec 64)
    (b_2c0 b_390 b_4f2 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (herr_ne_neg3 : w0 ≠ 0xfffffffffffffffd#64)
    (herr_ne_neg2 : w0 ≠ 0xfffffffffffffffe#64)
    (hr23_lo : r23.extractLsb' 0 32 = w1.extractLsb' 0 32)
    (hinv : ImgCallInv img s)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1648#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx10 : s.readReg64 .x10 = w2)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = w0)
    (hx21 : s.readReg64 .x21 = w4 >>> 8)
    (hx22 : s.readReg64 .x22 = w1 >>> 32)
    (hx23 : s.readReg64 .x23 = r23)
    (hx24 : s.readReg64 .x24 = w2 >>> 32)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = w5)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ w4) ∗
       ((sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((sp + 0xd0#64) ↦₆₄ w3) ∗
       memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       A.pool ∗
       stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ w4) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ w3) ∗
          memRegion (sp + 0x370#64) 36 ∗
          cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speWordsAt outPtr w0 w1 w2 w3 w4 w5 ∗
          logOff img ∗
          A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        ImgCallInv img sf)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  have hstep1 := Kits.p2_err_tail_a_ext_wp img.base ext s coroPtr outPtr w0 w1 w2 w4 w5 r23 u_c8 b_4f2
    herr_ne_neg3 hr23_lo hpc hrun hsp_align
    hx10 hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx27
  rw [hsp_eq] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  have hinv1 : ImgCallInv img s1 := ⟨hF1, hsym1⟩
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  have hdrop := Kits.drop_process_prekey_impl_state1_ext_ok (b := img.base) (ext := ext)
  have hstk48 : stackAt sp allocHookStack =
      stackAt (sp - 48#64) (allocHookStack - 48) ∗ cells (sp - 48#64) 6 :=
    ProofLib.stackAt_split_cells sp (allocHookStack - 48) 6 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.call_nopanic_steps_frame
    (spec := dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hinv1 hdrop hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [dropProcessPrekeyImplState1Spec]
      rw [hsp1, show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl])
    hx0_1 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec]
  rw [hsp1,
      show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl,
      sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, hx20_cs2, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, hx26_cs2, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx20_2 : s2.readReg64 .x20 = w0 := hx20_cs2.trans hx20_1
  have hx21_2 : s2.readReg64 .x21 = w4 >>> 8 := hx21_cs2.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = w2 := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = r23 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = w1 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hx27_2 : s2.readReg64 .x27 = w5 := hx27_cs2.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s2.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28, hsp2]
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (coroPtr + 0x250#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (cells6_eq (sp + 0xa90#64))) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  have hstep3 := Kits.p2_err_tail_b1_ext_wp img.base ext s2 coroPtr outPtr w0 w1 w2 w3 w4 w5 r23
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8 b_390
    hb herr_ne_neg2 hr23_lo hpc2 hrun2 hsp2_align
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx27_2 hx28_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx19_3, _, hx21_3, hx25_3, hx26_3, hx28_3, _, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hc250 := cells6_fold (coroPtr + 0x250#64) w0 w1 w2 w3 w4 w5
  repeat (simp only [BitVec.add_assoc] at hc250); repeat (simp only [BitVec.reduceAdd] at hc250)
  refine SepWPp.weaken_frame hc250 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp370_36_split_eq sp)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u390 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u370 => ?_
  have hx21_3' : s3.readReg64 .x21 = s3.sp + 0x370#64 := by rw [hx21_3, hsp3]
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_3, hsp3]
  have hx28_3' : s3.readReg64 .x28 = s3.sp + 0xa90#64 := by rw [hx28_3, hsp3]
  have hstep4 := Matched.p2_err_tail_b2_to_3588_ext_wp img.base ext s3 coroPtr w0 outPtr
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    u370 u378 u380 u388 (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) u390
    hpc3 hrun3 hsp3_align hx19_3 hx21_3' hx25_3' hx26_3 hx28_3'
  rw [hsp3] at hstep4
  refine p2_bind_sepWP_qp_frame hF3 hsym3 hstep4 (by sep_focus)
    fun s4 _ hpc4 hrun4 hF4 hsym4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4, htr4_3, hvregs4_3, hx19_4, hx22_4, hx25_4, hx26_4, hx28_4, _, _⟩
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (sp_a90_rejoin sp w0 w1 w2 w3 w4 w5) (by sep_focus) ?_
  have hdropTail := p2_over_err_drop_record_tail_hooks_ok (Qp := fun _ _ => False)
    hH hDropSs3 s0 s4
    sp coroPtr outPtr w0
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
    (w1.extractLsb' 0 32) (w5.extractLsb' 32 32) b_2c0
    g recG recSt
    ⟨hF4, hsym4⟩ hsp4 hsp_lt hpc4 hrun4 hsp4_align
    hx19_4 hx22_4 hx25_4 hx26_4 hx28_4
  refine p2_bind_sepWPp_nopanic_frame hdropTail (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (speWordsAt_realign_outPtr outPtr w0 w1 w2 w3 w4 w5)) (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ?_
  have hvregs_all : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine ⟨by rw [htrf, htr4_3, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregs_all, hinvf⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem p2_over_arm1_err_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {spkKit : SignedPreKeyStoreSpec A img.base}
    (hH : StageP2ClosureHooks A img.base ext)
    (hDropSs3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (hspkOk : SignedPreKeyStoreKitOkImgE img spkKit ext)
    (s0 s : State) (sp coroPtr outPtr spkStorePtr spkFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (signedPreKeyId : BitVec 32) (b_2c0 b_390 b_4f2 : BitVec 8) (e : spkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0xf38#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (spkGetPollOutAt spkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
       A.live spkFutPtr spkKit.getBoxSize 8 ∗
       spkKit.getBoxAt spkFutPtr spkStorePtr signedPreKeyId 1#8 ∗
       ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
       ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
       ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 368 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + spkKit.getFutVtOff)) ∗
          ((img.base + spkKit.getFutVtOff) ↦₆₄ᵣ (img.base + spkKit.getFutDropOff)) ∗
          ((img.base + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
          ((img.base + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt spkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  dsimp only [spkGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err88_to_preKeyRecordOut64 spkKit.getErr (sp + 0x3e0#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_418 => ?_
  have hstep1 := p2_err1a_ext_wp img.base ext s coroPtr spkFutPtr
    (img.base + spkKit.getFutVtOff) (img.base + spkKit.getFutDropOff) (spkKit.getErr.w0 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0
    (spkKit.getErr.w1 e) (spkKit.getErr.w2 e) (spkKit.getErr.w3 e)
    (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) u_418
    (spkKit.getFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (p2_memRegion_420_join sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_memRegion368 sp 0xffffffffffffffff#64
      (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
      (spkKit.getErr.w3 e) (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) u_418)
    (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ hspkOk.getFutDrop hpc1 hrun1 hsp1_al hx30_1
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
    (spkKit.getBoxAt_memRegion spkFutPtr spkStorePtr signedPreKeyId 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  have hstep3 := p2_err1b_hooks_wp img.base ext hH s2 coroPtr spkFutPtr
    (img.base + spkKit.getFutVtOff) outPtr
    (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
    (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) ctxPtr u_a8 u_c0 spkKit.getBoxSize
    spkKit.getBoxSize_ne_zero spkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1) (hx26_cs2.trans hx26_1)
    (hx27_cs2.trans (hx27_1.trans hx27)) (hx28_cs2.trans hx28_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_over_err_funnel_hooks_ok (Qp := fun _ _ => False)
    hH hDropSs3 s0 s3 sp coroPtr outPtr
    (spkKit.getErr.w0 e) (spkKit.getErr.w1 e) (spkKit.getErr.w2 e)
    (spkKit.getErr.w3 e) (spkKit.getErr.w4 e) (spkKit.getErr.w5 e) (spkKit.getErr.w1 e) outPtr
    b_2c0 b_390 b_4f2 g recG recSt hb
    (spkKit.getErr.w0_ne_pending e) (spkKit.getErr.w0_ne_ok e) rfl
    ⟨hF3, hsym3⟩ hsp3 hsp_lt hpc3 hrun3 hsp3_align
    hx10_3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3' hx26_3 hx27_3 hx28_3 hvregs3
  have hfunnel_re := SepWPp.mono_run hfunnel fun sf P_f h =>
    let ⟨htrf, hentf, hspf, hcsf, hvregsf, hinvf⟩ := h
    And.intro hentf (And.intro htrf (And.intro hspf (And.intro hcsf (And.intro hvregsf hinvf))))
  refine p2_bind_sepWPp_nopanic_frame hfunnel_re (by sep_focus)
    fun sf _ hpcf hrunf ⟨htrf, hspf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf ?_
  refine ⟨by rw [htrf, htr3_2, htr2_1, htr1], ?_, hspf, hcsf, hvregsf, hinvf⟩
  dsimp only [speErrAt]
  sep_norm
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
theorem p2_over_arm2_err_hooks_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    {kpkKit : KyberPreKeyStoreSpec A img.base}
    (hH : StageP2ClosureHooks A img.base ext)
    (hDropSs3 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (hkpkOk : KyberPreKeyStoreKitOkImgE img kpkKit ext)
    (s0 s : State) (sp coroPtr outPtr kyberStorePtr kyberFutPtr ctxPtr
    v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_c0 u_d0 : BitVec 64)
    (kyberPreKeyId : BitVec 32) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8) (e : kpkKit.GetErr)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hinv : ImgCallInv img s) (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x998#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = coroPtr + 0x4f2#64) (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = coroPtr + 0x398#64) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (kpkGetPollOutAt kpkKit (sp + 0x3e0#64) (.error e) ∗ memRegion (sp + 0x438#64) 280 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
       A.live kyberFutPtr kpkKit.getBoxSize 8 ∗
       kpkKit.getBoxAt kyberFutPtr kyberStorePtr kyberPreKeyId 1#8 ∗
       ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
       ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
       ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ u_98) ∗ ((sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ memRegion (sp + 0x370#64) 36 ∗
       cells (sp + 0xa90#64) 6 ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ logOff img ∗ A.pool ∗ stackAt sp dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.trace = s.trace ∧
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 368 ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (img.base + kpkKit.getFutVtOff)) ∗
          ((img.base + kpkKit.getFutVtOff) ↦₆₄ᵣ (img.base + kpkKit.getFutDropOff)) ∗
          ((img.base + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
          ((img.base + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
          ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x370#64) 36 ∗ cells (sp + 0xa90#64) 6 ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          speErrAt kpkKit.getErr outPtr e ∗ logOff img ∗ A.pool ∗
          stackAt sp dropSessionStructureLocal2Stack) ∧
        sf.sp = sp + 0xcd0#64 ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ ImgCallInv img sf)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  dsimp only [kpkGetPollOutAt]
  refine SepWPp.weaken_frame (p2_err88_to_preKeyRecordOut64 kpkKit.getErr (sp + 0x3e0#64) e)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_418 => ?_
  have hstep1 := p2_err2a_ext_wp img.base ext s coroPtr kyberFutPtr
    (img.base + kpkKit.getFutVtOff) (img.base + kpkKit.getFutDropOff) (kpkKit.getErr.w0 e)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 u_90 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e) (kpkKit.getErr.w3 e)
    (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) u_418
    (kpkKit.getFutDrop_ne_zero hb) hpc hrun hsp_align hx19 hx21 hx23 hx26
  rw [hsp_eq, BitVec.add_zero] at hstep1
  refine p2_bind_sepWP_qp_frame hinv.1 hinv.2 hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, _, hx19_1, _, hx21_1, hx22_1, hx23_1, hx24_1,
    hx25_1, _, hx27_1, hx28_1, _, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (p2_memRegion_420_join sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_preKeyRecordOut64_to_memRegion368 sp 0xffffffffffffffff#64
      (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
      (kpkKit.getErr.w3 e) (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) u_418)
    (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame (x := ()) (T := emp)
    ⟨hF1, hsym1⟩ hkpkOk.getFutDrop hpc1 hrun1 hsp1_al hx30_1
    rfl ⟨hF1, hsym1⟩ (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, LibsignalPublicApi.StoreSession.futDropSpec]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2,
    hx25_cs2, _, hx27_cs2, hx28_cs2, _, hvregs2_1⟩
  refine SepWPp.weaken_frame
    (kpkKit.getBoxAt_memRegion kyberFutPtr kyberStorePtr kyberPreKeyId 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le)) (by sep_focus) ?_
  have hstep3 := p2_err2b_hooks_wp img.base ext hH s2 coroPtr kyberFutPtr
    (img.base + kpkKit.getFutVtOff) outPtr
    (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
    (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e) ctxPtr u_c0 b_4f1 kpkKit.getBoxSize
    kpkKit.getBoxSize_ne_zero kpkKit.getBoxSize_lt hpc2 hrun2 hsp2_align
    (hx19_cs2.trans hx19_1) (hx21_cs2.trans hx21_1) (hx22_cs2.trans hx22_1)
    (hx23_cs2.trans hx23_1) (hx24_cs2.trans hx24_1)
    (hx27_cs2.trans (hx27_1.trans hx27)) (hx28_cs2.trans hx28_1)
  rw [hsp2] at hstep3
  simp only [BitVec.add_assoc] at hstep3
  refine p2_bind_sepWP_qp_frame hinv2.1 hinv2.2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_dropSS_to_alloc sp hdss_le).symm) (by sep_focus) ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx10_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3,
    hx25_3, hx26_3, hx27_3, hx28_3, _, hvregs3_2⟩
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = sp + 0x210#64 := by rw [hx25_3, hx25_cs2, hx25_1, hx25]
  have hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hfunnel := stageP2_over_err_funnel_hooks_ok (Qp := fun _ _ => False)
    hH hDropSs3 s0 s3 sp coroPtr outPtr
    (kpkKit.getErr.w0 e) (kpkKit.getErr.w1 e) (kpkKit.getErr.w2 e)
    (kpkKit.getErr.w3 e) (kpkKit.getErr.w4 e) (kpkKit.getErr.w5 e)
    (((kpkKit.getErr.w1 e).extractLsb' 0 32).zeroExtend 64) outPtr
    b_2c0 b_390 b_4f2 g recG recSt hb
    (kpkKit.getErr.w0_ne_pending e) (kpkKit.getErr.w0_ne_ok e)
    (p2_zeroExtend32_extractLsb_lo (kpkKit.getErr.w1 e))
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
