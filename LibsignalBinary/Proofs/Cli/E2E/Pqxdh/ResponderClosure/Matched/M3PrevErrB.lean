/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErr
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe

/-!
# General-`prevCap` Stage P3 Non-Duplicate and Unified Error Paths

Proves `stageP3_err_tail_nondup_dec_prevEmpty_ext_ok`, `stageP3_sub5_err_nondup_prevEmpty_ext_ok`,
and `stageP3_sub5_err_prevEmpty_ext_ok` (`+0x1cd8 → s0.readReg64 .x30`) over general
`prevSessionsEmptyAt A coroPtr g`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `<alloc::raw_vec::RawVecInner>::finish_grow [local#1]` meets `finishGrowSpec A` on
`tripleRatchetProgAtExt b ext` under `AllocContractsMem4K b A ext` (`allocHookStack = 4096`). -/
theorem finish_grow_4k_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrowSpec A) := by
  apply CryptoVerification.LibsignalTripleRatchet.subroutine_ok_of_optNone
  refine finish_grow_ok_of_hooks_opt (by decide) ?_ ?_ ?_
  · apply CryptoVerification.LibsignalTripleRatchet.subroutine_ok_to_optNone
    have h := subroutine_ok_withStack_of_subroutine_ok
      (hA.shim_ok_at finishGrowName
        (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by fnoff_eq))
      allocHookStack
    refine subroutine_ok_mono h (fun x R s0 hpre => ?_) (fun x R s0 sf hpost => ?_)
    · dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpre
    · dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpost ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpost
  · exact CryptoVerification.LibsignalTripleRatchet.subroutine_ok_to_optNone
      (hA.alloc_ok_at finishGrowName
        (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by fnoff_eq))
  · exact CryptoVerification.LibsignalTripleRatchet.subroutine_ok_to_optNone
      (rustReallocExternWithStack_of_rustRealloc
        (hA.realloc_ok_at finishGrowName
          (num% (ls_off% "__rustc::__rust_realloc" -
            ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")) (by fnoff_eq))
        (by decide) (by decide))

set_option maxHeartbeats 1200000 in
/-- General-`prevCap` non-duplicate error tail (`+0x34dc#64 → s0.readReg64 .x30` when `errs.len = 1`)
under `AllocContractsMem4K`. -/
theorem stageP3_err_tail_nondup_dec_prevEmpty_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (coroPtr outPtr errsPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (_he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
       ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.weaken_frame
    (sessionStateAt_unpack_head_tail A (coroPtr + 0xf8#64) recG recSt)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bs336 => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (P₂ := ⌜bs336.length = 336 ∧ recG.localIk.cap.toNat < 2 ^ 63 ∧
      SessionInline recG recSt (unpack64 recG.localIk.cap ++ bs336)⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, hinl⟩ => ?_
  have hrepack278 := words3_repack_w32_2w64_w32 (s.sp + 0x278#64) w0 w1 w2
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack278
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion20_split_eq (s.sp + 0x250#64))) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_250 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (sp370_36_err_split_eq s.sp)) (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_38c => SepWPp.exists_elim fun u_384 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  have hstep1 := p3_err_tail_nondup_a1_ext_wp b ext s coroPtr errsPtr
    hpc hrun hsp_align hx19
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, hx21_1, hx22_1, hx23_1,
    hx24_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hA' : AllocContractsMem4K img.base A ext := hb ▸ hA
  have hdropSpe := drop_spe2_of_dealloc_ext (img := img) (ext := ext) himg hA'.dealloc
  have hpc1_drop : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.dropSpe2Name := by
    rw [hpc1, ← hb, tripleRatchetProgAtExt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")]
  rw [← hb] at hdropSpe hpc1_drop
  have hstack_drop :
      stackAt s.sp dropSessionStructure2Stack =
        memRegion (s.sp - 4192#64) 64 ∗ stackAt s.sp dropSpeStack :=
    stackAt_split_bottom s.sp dropSpeStack 64 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop) (by sep_focus) ?_
  refine call_frame_inImage_nopanic
    (spec := dropSpeSpec A)
    (x := (⟨errsPtr, utf8 "decrypt", e⟩ : DropSpeGhost))
    (T := speAt A (utf8 "decrypt") errsPtr e ∗ A.pool ∗ stackAt s.sp dropSpeStack)
    hF1 hsym1 hdropSpe hpc1_drop hrun1 hsp1_al hx30_1
    (by dsimp only [dropSpeSpec]; rw [hsp1_s])
    hx0_1
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [dropSpeSpec]
  rw [hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hjoin192 :
      memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 ⊢
        memRegion errsPtr 192 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144)
          (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hjoin192 (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp dropSpeStack =
        memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 32 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, _,
    hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = errsPtr := hx21_cs2.trans hx21_1
  have hx22_2 : s2.readReg64 .x22 = errsPtr := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = 1#64 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hx24, hsp2_s]
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2_s]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs2.trans (hx28_1.trans hx28)
  have hstep3 := p3_err_tail_nondup_a2_ext_4k_wp b ext hA s2 coroPtr errsPtr recG.localIk.cap
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    w3 w4 u_250 u_258 u_370 u_378 u_384 u_38c
    (w0.extractLsb' 0 32) (w2.extractLsb' 32 32) u_260 u_380
    (cap_ne_noneCap_of_lt hcap_lt) hpc2 hrun2 hsp2_align
    hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx28_2
  rw [hsp2_s] at hstep3
  refine P3P4.SepWPp.bind_sepWP_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx22_3, _, hx25_3, hx26_3, _, hx28_3, _,
    hx30_3, hvregs_3⟩
  have hstack_restore :
      memRegion (s.sp - 4192#64) 64 ∗ memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp dropSessionStructure2Stack := by
    rw [hstack_drop, hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore (by sep_focus) ?_
  have hpack_ss :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗ ((coroPtr + 0x100#64) ↦ₛ bs336) ∗
      sessionHeap A recG recSt ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG recSt := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      sessionStateAt_pack_head_tail A (coroPtr + 0xf8#64) recG recSt hinl
  refine P3P4.SepWPp.weaken_frame hpack_ss (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack278.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x270#64) 0x8000000000000018#64 w0 w1 w2 w3 w4)
    (by sep_focus) ?_
  have hfold250 :
      ((s.sp + 0x250#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((s.sp + 0x258#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((s.sp + 0x260#64) ↦₃₂ w2.extractLsb' 32 32) ⊢
      memRegion (s.sp + 0x250#64) 20 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using
      memRegion20_fold (s.sp + 0x250#64)
        (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w2.extractLsb' 32 32)
  refine P3P4.SepWPp.weaken_frame hfold250 (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  have hx25_3' : s3.readReg64 .x25 = s3.sp + 0x210#64 := by rw [hx25_3, hsp3_s]
  have hcommon := stageP3_err_tail_common_prevEmpty_ext_4k_ok img b ext hA
    s0 s3 coroPtr outPtr 0x8000000000000018#64
    w0 w1 w2 w3 w4 b_2c0 g recG recSt
    hF3 hsym3 hpc3 hrun3 hsp3_align
    (htr3_2.trans (htr2_1.trans (htr1_s.trans htr)))
    hx0_3 hx19_3 hx22_3 hx25_3' (hx26_3.trans hx26_2) hx28_3 hx30_3
  rw [hsp3_s] at hcommon
  refine P3P4.SepWPp.ret_sepWPp_frame hcommon (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  exact ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf, htrf, hcc, hFf, hsymf, by rw [hvregs_f, hvregs_3, hvregs_cs2, hvregs_1]⟩

/-- General-`prevCap` non-duplicate error tail (`+0x34dc#64 → s0.readReg64 .x30` when `errs.len = 1`). -/
theorem stageP3_err_tail_nondup_dec_prevEmpty_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocContracts b A ext)
    (s0 s : State) (coroPtr outPtr errsPtr w0 w1 w2 w3 w4 : BitVec 64)
    (e : SignalProtocolError) (he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = 0x8000000000000018#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ A.live errsPtr 192 8 ∗
       speAt A (utf8 "decrypt") errsPtr e ∗ memRegion (errsPtr + 0x30#64) 144 ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevSessionsEmptyAt A coroPtr g ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       memRegion (s.sp + 0x250#64) 20 ∗ ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
       ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗
       ((s.sp + 0x298#64) ↦₆₄ w4) ∗ memRegion (s.sp + 0x370#64) 36 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          words6At outPtr 0x8000000000000018#64 w0 w1 w2 w3 w4 ∗ memRegion (s.sp + 0x250#64) 20 ∗
          memRegion (s.sp + 0x270#64) 48 ∗ memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) :=
  stageP3_err_tail_nondup_dec_prevEmpty_ext_4k_ok img b ext himg hb
    (AllocContractsMem4K.of_AllocContracts hA)
    s0 s coroPtr outPtr errsPtr w0 w1 w2 w3 w4 e he_npan b_2c0 g recG recSt
    hF hsym hpc hrun hsp_align htr hx19 hx24 hx25 hx26 hx28

/-- Counterpart of `stageP3ErrPre` over general `prevSessionsEmptyAt A coroPtr g`. -/
def stageP3ErrPrePrevEmpty (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost)
    (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗ vecResultAt A (s.sp + 0x270#64) (.error e) ∗
  sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  prevSessionsEmptyAt A coroPtr g ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  memRegion outPtr 48 ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  memRegion (s.sp + 0x930#64) 48 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
  stackAt s.sp growOneSpeStack

/-- Counterpart of `stageP3ErrPost` at `s0.readReg64 .x30` (`Err e` / `st.version ≠ msgVer`),
after `+0x3588 → x30` drops `SessionStructure` and any spare `g.prevPtr` buffer into
`memRegion (coroPtr + 0xe0#64) 368`. -/
def stageP3ErrPostPrevEmpty (A : RustAlloc) (b : BitVec 64) (s0 s : State)
    (coroPtr outPtr : BitVec 64)
    (e : SignalProtocolError) : SepProp :=
  (∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
    ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
    ((s.sp + 0x3d8#64) ↦₆₄ errsLen)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗ memRegion (s.sp + 0xa90#64) 344 ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
  recordResultAt A outPtr (.error (SessionState.recordError .preKey e)) ∗
  memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x270#64) 48 ∗
  memRegion (s.sp + 0x370#64) 36 ∗ memRegion (s.sp + 0x930#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗ stackAt s.sp growOneSpeStack

set_option maxHeartbeats 1200000 in
/-- General-`prevCap` Substage P3.5 non-duplicate error path (`+0x1cd8#64 → s0.readReg64 .x30`)
under `AllocContractsMem4K`. -/
theorem stageP3_sub5_err_nondup_prevEmpty_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrevEmpty A b s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmpty A b s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  unfold stageP3ErrPrePrevEmpty stageP3ErrPostPrevEmpty
  have hrec_err : SessionState.recordError .preKey e = .invalidMessage .preKey .decryptionFailed :=
    recordError_preKey_of_speTag_ne_speWord23 he_npan htag_ne23
  rw [hrec_err]
  have hb_align : b &&& 0xfff#64 = 0#64 := hb ▸ ProofLib.ObjectLoad.base_aligned_of_loads himg
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWPp.intro_rodata_5ac90_5ac98 himg hb hF ?_
  have hdecomp :
      vecResultAt A (s.sp + 0x270#64) (.error e) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ H : SepProp,
        ⌜∀ c : BitVec 64,
          words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢
            speAt A (utf8 "decrypt") c e⌝ ∗ ((s.sp + 0x270#64) ↦₆₄ speTag e) ∗
        ((s.sp + 0x278#64) ↦₆₄ w0) ∗ ((s.sp + 0x280#64) ↦₆₄ w1) ∗
        ((s.sp + 0x288#64) ↦₆₄ w2) ∗ ((s.sp + 0x290#64) ↦₆₄ w3) ∗ ((s.sp + 0x298#64) ↦₆₄ w4) ∗
          H := by
    have h1 := speAt_decomp6 A (utf8 "decrypt") (s.sp + 0x270#64) e he_npan
    dsimp only [vecResultAt] at h1 ⊢
    refine Entails.trans h1 ?_
    apply Entails.sepExists_elim; intro w0
    apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro w2
    apply Entails.sepExists_elim; intro w3
    apply Entails.sepExists_elim; intro w4
    apply Entails.sepExists_elim; intro H
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
        (Entails.sepExists_right w4 (Entails.sepExists_right H ?_)))))
    unfold words6At
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hdecomp (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
    SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
    SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun H => ?_
  refine P3P4.SepWPp.weaken_frame
    (P₁ := ⌜∀ c : BitVec 64,
      words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c e⌝)
    (P₂ := ⌜∀ c : BitVec 64,
      words6At c (speTag e) w0 w1 w2 w3 w4 ∗ H ⊢
        speAt A (utf8 "decrypt") c e⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hreassemble => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x930#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u930 => SepWPp.exists_elim fun u938 =>
    SepWPp.exists_elim fun u940 => SepWPp.exists_elim fun u948 =>
    SepWPp.exists_elim fun u950 => SepWPp.exists_elim fun u958 => ?_
  have hstep1 := p3_err_nondup_a_ext_wp b ext s coroPtr outPtr (speTag e)
    w0 w1 w2 w3 w4 u930 u938 u940 u948 u950 u958
    hb_align (speTag_ne_ok_of_ne_panic he_npan) htag_ne23 hpc hrun hsp_align hx19 hx24
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, _, _, _, _, _, hx19_1, hx24_1, hx25_1, hx26_1, _, _, _,
    hx30_1, hvregs_1⟩
  refine P3P4.SepWPp.weaken_frame
    (words6_entails_memRegion48 (s.sp + 0x930#64) (speTag e) w0 w1 w2 w3 w4)
    (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have hlog : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName)
      ((pqxdhLogClosureSpec img).inImage img) :=
    hb ▸ pqxdh_log_closure_ok_ext (ext := ext) himg
  have hpc1_log : s1.pc =
    (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName := by
    rw [hpc1, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      show libsignalSessionCode.fnOff CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName =
        (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") from
        (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  have hlogOff_eq : logOff img = ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) := by
    dsimp only [logOff, CryptoVerification.LibsignalSession.logFilterAddr]
    rw [hb]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_frame_inImage_nopanic
    (spec := pqxdhLogClosureSpec img)
    (x := ())
    (φ := True)
    (T := ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s.sp pqxdhClosureStack)
    hF1 hsym1 hlog hpc1_log hrun1 hsp1_al hx30_1
    (by dsimp only [pqxdhLogClosureSpec]; rw [hlogOff_eq, hsp1_s, pure_true, emp_sepConj])
    trivial
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  dsimp only [pqxdhLogClosureSpec]
  rw [hlogOff_eq, hsp1_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  have hstack_restore1 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore1 (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2_s]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, _, _, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans hx26_1
  have hstep3 := p3_err_nondup_b_ext_wp b ext s2 coroPtr
    hpc2 hrun2 hsp2_align hx19_2
  rw [hsp2_s] at hstep3
  refine P3P4.SepWPp.bind_sepWP_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx19_3, hx21_3, hx24_3, hx25_3, hx26_3, _, _, _,
    hx30_3, hvregs_3⟩
  have hsp3_s : s3.sp = s.sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_s] using hsp_align
  have hgrow := grow_one_spe_ok_ext (b := b) (ext := ext) (finish_grow_4k_ok_ext hA)
  have hpc3_grow : s3.pc = (tripleRatchetProgAtExt b ext).fnAddr growOneSpeName := by
    rw [hpc3, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")]
  have htr3_0 : s3.trace = s0.trace := htr3_2.trans (htr2_1.trans (htr1_s.trans htr))
  refine P3P4.SepWPp.call_frame_frozen_oom
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool ∗ stackAt s.sp growOneSpeStack)
    hF3 hsym3 htr3_0 hgrow hpc3_grow hrun3 hsp3_al hx30_3
    (by
      rw [growOneSpe_pre_zero_eq A s3 (s.sp + 0x3c8#64) initErrsPtr hx0_3 hinit_ne, hsp3_s,
        pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial
    (by sep_focus)
    (hnext := fun s4 hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  rw [growOneSpe_post_zero_eq A s3 s4 (s.sp + 0x3c8#64) initErrsPtr, hsp3_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr4_3 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  have hsplit192 :
      memRegion errsPtr 192 =
        memRegion errsPtr 48 ∗ memRegion (errsPtr + 0x30#64) 144 := by
    rw [ProofLib.memRegion_split' (b := errsPtr) (n := 48) (k := 144)
          (b' := errsPtr + 0x30#64) rfl (by bv_omega) (by decide)]
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hsplit192) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq errsPtr))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun e0 => SepWPp.exists_elim fun e1 =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  have hsp4_s : s4.sp = s.sp := hsp4_3.trans hsp3_s
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4_s]; exact hsp_align
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, hx24_cs4, hx25_cs4, hx26_cs4, _, _, _, hvregs_cs4⟩
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hx21_cs4.trans hx21_3
  have hx24_4 : s4.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs4.trans (hx24_3.trans hx24_2)
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hx25_cs4, hx25_3, hx25_2, hsp4_s]
  have hx26_4 : s4.readReg64 .x26 = outPtr := hx26_cs4.trans (hx26_3.trans hx26_2)
  have hstep5 := p3_err_nondup_c_ext_4k_wp b ext hA s4 coroPtr errsPtr (speTag e)
    w0 w1 w2 w3 w4 e0 e1 e2 e3 e4 e5
    hb_align hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx25_4
  rw [hsp4_s] at hstep5
  refine P3P4.SepWPp.bind_sepWP_frame hF4 hsym4 hstep5 (by sep_focus)
    fun s5 hpc5 hrun5 hF5 hsym5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hx0_5, hx1_5, hx19_5, hx24_5, hx25_5, hx26_5, _, _, _,
    hvregs_5⟩
  have hsp5_s : s5.sp = s.sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  have htr5_0 : s5.trace = s0.trace := htr5_4.trans (htr4_3.trans htr3_0)
  have hreasm_errs :
      ((errsPtr + 0x0#64) ↦₆₄ speTag e) ∗ ((errsPtr + 0x8#64) ↦₆₄ w0) ∗
      ((errsPtr + 0x10#64) ↦₆₄ w1) ∗ ((errsPtr + 0x18#64) ↦₆₄ w2) ∗
      ((errsPtr + 0x20#64) ↦₆₄ w3) ∗ ((errsPtr + 0x28#64) ↦₆₄ w4) ∗ H ⊢
      speAt A (utf8 "decrypt") errsPtr e := by
    simpa only [words6At, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      using hreassemble errsPtr
  refine P3P4.SepWPp.weaken_frame hreasm_errs (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 512 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  have halloc17 := p3_alloc_2eac_ext_4k_ok (A := A) img b ext hA s0 s5
    emp hF5 hsym5 hpc5 hrun5 hsp5_align htr5_0 hx0_5 hx1_5
  rw [sepConj_emp, hsp5_s] at halloc17
  refine SepWPp.bind_sepWPp_frame_raw
    halloc17 (by sep_focus)
    fun s6 P_m6 hpc6 hrun6 ⟨hP6, hdf_ne, hsp6_5, htr6_5, hcs6, hF6, hsym6⟩ => ?_
  rw [sepConj_emp] at hP6
  refine P3P4.SepWPp.weaken_frame hP6 (by sep_focus) ?_
  have hstack_restore2 :
      memRegion (s.sp - 4608#64) 512 ∗ stackAt s.sp allocHookStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_alloc]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore2 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion17_split_eq (s6.readReg64 .x0)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun df_10 => SepWPp.exists_elim fun df_8 =>
    SepWPp.exists_elim fun df_0 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (cell_split_head8 (s.sp + 0x290#64) w3))
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6_s]; exact hsp_align
  rcases hcs6 with ⟨hx19_cs6, _, _, _, _, hx24_cs6, hx25_cs6, hx26_cs6, _, _, _, hvregs_cs6⟩
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hx19_cs6.trans hx19_5
  have hx24_6 : s6.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs6.trans (hx24_5.trans hx24_4)
  have hx25_6 : s6.readReg64 .x25 = s.sp + 0x210#64 := hx25_cs6.trans hx25_5
  have hx26_6 : s6.readReg64 .x26 = outPtr := hx26_cs6.trans (hx26_5.trans hx26_4)
  have hstep7 := p3_err_nondup_d_ext_wp b ext s6 coroPtr (s6.readReg64 .x0)
    0x6974707972636564#64 0x656c696166206e6f#64
    df_0 df_8 (speTag e) w0 w1 w2 df_10 (w3.extractLsb' 0 8)
    hb_align hdf_ne hpc6 hrun6 hsp6_align rfl hx19_6
  rw [hsp6_s] at hstep7
  refine P3P4.SepWPp.bind_sepWP_frame hF6 hsym6 hstep7 (by sep_focus)
    fun s7 hpc7 hrun7 hF7 hsym7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx19_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7,
    hvregs_7⟩
  have hsp7_s : s7.sp = s.sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7_s] using hsp_align
  refine SepWPp.drop_frame
    (P_drop := ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
               ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (dfPtr_words_eq_decryptionFailedStr (s6.readReg64 .x0)))
    (by sep_focus) ?_
  obtain ⟨w3', hw3'_unpack, hw3'_join⟩ := cell_join_head8 3#8 w3
  have hw3'_head : w3'.extractLsb' 0 8 = 3#8 := extractLsb0_8_of_unpack64_cons hw3'_unpack
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (hw3'_join (s.sp + 0x290#64))) (by sep_focus) ?_
  have hdropSs3 := drop_session_structure3_of_dealloc_ext (b := b) (ext := ext) hA.dealloc
  have hpc7_drop : s7.pc = (tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc7, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := (⟨s.sp + 0xa90#64, G₂, st₂⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₂ st₂ ∗ A.pool ∗
      stackAt s.sp dropSessionStructure2Stack)
    hF7 hsym7 hdropSs3 hpc7_drop hrun7 hsp7_al hx30_7
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]; rw [hsp7_s])
    hx0_7 (by sep_focus)
    (hnext := fun s8 hpc8 hrun8 hsp8_7 _ hcs8 hF8 hsym8 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [hsp7_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr8_7 => ?_
  have hsp8_s : s8.sp = s.sp := hsp8_7.trans hsp7_s
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8_s]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, _, _, _, hx24_cs8, hx25_cs8, hx26_cs8, _, hx28_cs8, _, hvregs_cs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx24_8 : s8.readReg64 .x24 = s8.sp + 0x370#64 := by
    rw [hx24_cs8, hx24_7, hx24_6, hsp8_s]
  have hx25_8 : s8.readReg64 .x25 = s8.sp + 0x210#64 := by
    rw [hx25_cs8, hx25_7, hx25_6, hsp8_s]
  have hx26_8 : s8.readReg64 .x26 = outPtr := hx26_cs8.trans (hx26_7.trans hx26_6)
  have hx28_8 : s8.readReg64 .x28 = 0x8000000000000018#64 := hx28_cs8.trans hx28_7
  have htail := stageP3_err_tail_nondup_dec_prevEmpty_ext_4k_ok img b ext himg hb hA
    s0 s8 coroPtr outPtr errsPtr
    17#64 (s6.readReg64 .x0) 17#64 w3' w4 e he_npan b_2c0 g recG recSt
    hF8 hsym8 hpc8 hrun8 hsp8_align
    (htr8_7.trans (htr7_6.trans (htr6_5.trans htr5_0)))
    hx19_8 hx24_8 hx25_8 hx26_8 hx28_8
  rw [hsp8_s] at htail
  refine P3P4.SepWPp.ret_sepWPp_frame htail (by sep_focus)
    fun sf _ _ ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
  have hrec := words6At_preKey_decryptionFailed_entails_recordResultAt A
    outPtr (s6.readReg64 .x0) w3' w4 hdf_ne hw3'_head
  have hstack_restore3 :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine ⟨?_, hspf, htrf, hcc, hFf, hsymf,
    by rw [hvregs_f, hvregs_cs8, hvregs_7, hvregs_cs6, hvregs_5, hvregs_cs4, hvregs_3,
      hvregs_cs2, hvregs_1]⟩
  refine Entails.sepExists_right 4#64 (Entails.sepExists_right errsPtr
    (Entails.sepExists_right 1#64 ?_))
  refine Entails.trans (entails_replace_sub hrec (by sep_focus) rfl) ?_
  exact entails_replace_sub hstack_restore3 (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus))

/-- General-`prevCap` Substage P3.5 non-duplicate error path (`+0x1cd8#64 → s0.readReg64 .x30`). -/
theorem stageP3_sub5_err_nondup_prevEmpty_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocContracts b A ext)
    (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (e : SignalProtocolError) (he_npan : e ≠ .panic) (htag_ne23 : speTag e ≠ speWord 23)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrevEmpty A b s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmpty A b s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) :=
  stageP3_sub5_err_nondup_prevEmpty_ext_4k_ok img b ext himg hb (AllocContractsMem4K.of_AllocContracts hA)
    s0 s coroPtr outPtr initErrsPtr hinit_ne e he_npan htag_ne23 b_2c0 g G₂ recG st₂ recSt
    hF hsym hpc hrun hsp_align htr hx19 hx24

/-- General-`prevCap` unified Substage P3.5 error path (`+0x1cd8#64 → s0.readReg64 .x30`)
under `AllocContractsMem4K`. -/
theorem stageP3_sub5_err_prevEmpty_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (e : SignalProtocolError) (he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrevEmpty A b s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmpty A b s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  by_cases htag23 : speTag e = speWord 23
  · obtain ⟨ratVer, counter, rfl⟩ := speTag_eq_speWord23_iff.mp htag23
    unfold stageP3ErrPrePrevEmpty stageP3ErrPostPrevEmpty
    have hstack_drop2 :
        stackAt s.sp growOneSpeStack =
          memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
      stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
    rw [hstack_drop2]
    have hdup := stageP3_sub5_err_dup_prevEmpty_ext_4k_ok img b ext hA
      s0 s coroPtr outPtr initErrsPtr ratVer counter b_2c0 g G₂ recG st₂ recSt
      hF hsym hpc hrun hsp_align htr hx19 hx24
    refine P3P4.SepWPp.ret_sepWPp_frame hdup (by sep_focus)
      fun sf _ _ ⟨hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩ => ?_
    have herrs :
        ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
        ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ⊢
        ∃∗ errsCap : BitVec 64, ∃∗ errsPtr : BitVec 64, ∃∗ errsLen : BitVec 64,
          ((s.sp + 0x3c8#64) ↦₆₄ errsCap) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ errsLen) :=
      Entails.sepExists_right 0#64 (Entails.sepExists_right initErrsPtr
        (Entails.sepExists_right 0#64 (Entails.refl _)))
    dsimp only [SessionState.recordError]
    exact ⟨entails_replace_sub herrs (by sep_focus) (P3P4.eq_of_sep_emp (by sep_focus)),
      hspf, htrf, hcc, hFf, hsymf, hvregs_f⟩
  · exact stageP3_sub5_err_nondup_prevEmpty_ext_4k_ok img b ext himg hb hA
      s0 s coroPtr outPtr initErrsPtr hinit_ne e he_npan htag23
      b_2c0 g G₂ recG st₂ recSt hF hsym hpc hrun hsp_align htr hx19 hx24

/-- General-`prevCap` unified Substage P3.5 error path (`+0x1cd8#64 → s0.readReg64 .x30`). -/
theorem stageP3_sub5_err_prevEmpty_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    (hA : AllocContracts b A ext)
    (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0)
    (e : SignalProtocolError) (he_npan : e ≠ .panic)
    (b_2c0 : BitVec 8)
    (g : RecordGhost) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (stageP3ErrPrePrevEmpty A b s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt)
      (fun sf P_f =>
        (P_f ⊢ stageP3ErrPostPrevEmpty A b s0 s coroPtr outPtr e) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) :=
  stageP3_sub5_err_prevEmpty_ext_4k_ok img b ext himg hb (AllocContractsMem4K.of_AllocContracts hA)
    s0 s coroPtr outPtr initErrsPtr hinit_ne e he_npan b_2c0 g G₂ recG st₂ recSt
    hF hsym hpc hrun hsp_align htr hx19 hx24

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
