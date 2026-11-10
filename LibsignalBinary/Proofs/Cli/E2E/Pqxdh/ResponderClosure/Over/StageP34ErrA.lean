/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyBase
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4ErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsErrUnwind
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP34ErrStepsA
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErr -- shake: keep

/-!
# Stage P3 and Stage P4 Error Epilogues on 1-Element `previous_sessions`

Composes `dropSessionStructure3` with the 1-element `previous_sessions` drop blocks across Stage P3
(`dropSessionStructure3 → s0.readReg64 .x30`) and Stage P4 (`+0x3588` and `+0x550 → s0.readReg64 .x30`),
collapsing `sessionStateAt` and `prevVecAt [enc]` into `memRegion (coroPtr + 0xe0#64) 368`.
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
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stage P3 Common Error Epilogue (`dropSessionStructure3 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Drops `sessionStateAt A (coroPtr + 0xf8#64) recG recSt` and 1-element
`prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]` into `memRegion (coroPtr + 0xe0#64) 368`
using `dealloc` alone. -/
theorem stageP3_err_tail_common_prev1_of_dealloc_ext_ok {A : RustAlloc} (img : Obj.Image)
    (b : BitVec 64)
    (ext : String → Option (State → State))
    (hdealloc :
      subroutine_ok (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A))
    (s0 s : State) (coroPtr outPtr errTag prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  have hdropSs3 := drop_session_structure3_of_dealloc_ext (b := b) (ext := ext) hdealloc
  have hpc_drop : s.pc =
      (tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := (⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hF hsym hdropSs3 hpc_drop hrun hsp_al hx30
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec])
    hx0 (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hF1 hsym1 => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1_s => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _, hvregs_cs1⟩
  have hx19_1 : s1.readReg64 .x19 = coroPtr := hx19_cs1.trans hx19
  have hx22_1 : s1.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64 := hx22_cs1.trans hx22
  have hx25_1 : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_cs1, hx25, hsp1_s]
  have hx26_1 : s1.readReg64 .x26 = outPtr := hx26_cs1.trans hx26
  have hx28_1 : s1.readReg64 .x28 = errTag := hx28_cs1.trans hx28
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (P3P4.outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0))
    (by sep_focus) ?_
  have hstack_alloc :
      stackAt s.sp dropSessionStructure2Stack =
        memRegion (s.sp - 4192#64) 96 ∗ stackAt s.sp allocHookStack :=
    stackAt_split_bottom s.sp allocHookStack 96 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_ret2c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0 => ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  have hstep2 := p3_err_tail_b_prev1_of_dealloc_ext_wp b ext hdealloc s1 coroPtr outPtr errTag
    prevCap prevPtr
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0 enc
    hpc1 hrun1 hsp1_align hx19_1 hx22_1 hx25_1 hx26_1 hx28_1
  rw [hsp1_s] at hstep2
  refine P3P4.SepWPp.bind_sepWP_frame hF1 hsym1 hstep2 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_alloc.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp370_36_err_fold s.sp
      (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
      w3 w4 (w2.extractLsb' 32 32))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (P3P4.decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame hout_words (by sep_focus) ?_
  exact SepWPp.done hpcf hrunf ⟨Entails.of_eq (P3P4.eq_of_sep_emp (by sep_focus)),
    hspf_s, htrf_1.trans (htr1_s.trans htr),
    ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
    hFf, hsymf, hvregs_f.trans hvregs_cs1⟩

theorem stageP3_err_tail_common_prev1_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s0 s : State) (coroPtr outPtr errTag prevCap prevPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")))
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x359c#64) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗ A.pool ∗
       stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
          memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt s.sp dropSessionStructure2Stack) ∧ sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) :=
  stageP3_err_tail_common_prev1_of_dealloc_ext_ok img b ext hA.dealloc s0 s coroPtr outPtr errTag
    prevCap prevPtr w0 w1 w2 w3 w4 b_2c0 enc recG recSt hF hsym hpc hrun hsp_align htr hx0 hx19
    hx22 hx25 hx26 hx28 hx30

/-! ## Stage P4 Error Unwind (`+0x3588` / `+0x550 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1000000 in
/-- Stage P4 `+0x3588 → s0.readReg64 .x30` unwind on
`prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]` under `StageP4Alloc` (`dealloc` only). -/
theorem stageP4_err_unwind_3588_prev1_vregs_ok_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (s0 s : State)
    (coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        (P_f ⊢
          pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp stageP4ErrUnwindStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      Qp := by
  refine SepWPp.with_steps ?_
  refine P3P4.SepWPp.weaken_frame (p4_sessionStateAt_expose_cap_ne A (coroPtr + 0xf8#64) G st)
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hcap_ne => ?_
  have hstep1 := p4_err_3588_vregs_ext_wp img.base ext s coroPtr G.localIk.cap hcap_ne hpc hrun hx19
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep1 (by sep_focus)
    fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hlr1, hvregs1⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (p4_sessionStateAt_expose_cap A (coroPtr + 0xf8#64) G st).symm)
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_errUnwind_to_dropSS3 s.sp hsp_ub))
    (by sep_focus) ?_
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  simp only [sepConj_assoc]
  refine P3P4.SepWPp.call_frame_frozen_nopanic
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
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_errUnwind_to_dropSS3 s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub)) (by sep_focus) ?_
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = w_22.zeroExtend 64 := hx22_cs2.trans (hx22_1.trans hx22)
  have hx25_2 : s2.readReg64 .x25 = s2.sp + 0x210#64 := by rw [hx25_cs2, hx25_1, hx25, hsp2]
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = errTag := hx28_cs2.trans (hx28_1.trans hx28)
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion48_eq_exists_pollCells outPtr)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun o6_u => SepWPp.exists_elim fun o5_u =>
    SepWPp.exists_elim fun o4_u => SepWPp.exists_elim fun o3_u =>
    SepWPp.exists_elim fun o2_u => SepWPp.exists_elim fun o1_u =>
    SepWPp.exists_elim fun w0_u => ?_
  have hstep3 := p3_err_tail_b_prev1_of_dealloc_ext_wp img.base ext hA.dealloc s2 coroPtr outPtr errTag
    prevCap prevPtr o2 o3 o4 o5 w0_u o2_u o3_u o4_u o5_u
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    w_22 o6 o1_u o6_u b_2c0 enc
    hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
  rw [hsp2] at hstep3
  unfold pollCellsAt stagingCellsAt
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hstep3 ⊢
  refine P3P4.SepWPp.bind_sepWP_frame hF2 hsym2 hstep3 (by sep_focus)
    fun sf hpcf hrunf hFf hsymf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hvregsf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f,
    hx27f, hx28f, hx29f, _⟩
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub).symm) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  have h370 := stagingCellsAt_entails_memRegion36 (s.sp + 0x370#64) o2 o3 o4 o5 o6
  unfold stagingCellsAt at h370
  simp only [BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h370
  refine P3P4.SepWPp.weaken_frame h370 (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (hdrP_coro_344_entails_368 coroPtr prevCap prevPtr 1#64) (by sep_focus) ?_
  refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
  refine ⟨hspf, by rw [htrf, htr2_1, htr1], ?_,
    hvregsf.trans (hvregs_cs2.trans (hvregs1.trans hvregs)), hFf, hsymf⟩
  exact ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, trivial⟩

theorem stageP4_err_unwind_3588_prev1_vregs_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (s0 s : State)
    (coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (enc : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      decryptPrekeyClosureName + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       stagingCellsAt (s.sp + 0x370#64) o2 o3 o4 o5 o6 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        (P_f ⊢
          pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp stageP4ErrUnwindStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      Qp :=
  stageP4_err_unwind_3588_prev1_vregs_ok_p4 img ext (StageP4Alloc.of_allocContracts hA) hDropSS3
    s0 s coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 w_22 o6 b_2c0 enc G st Qp hsp_ub hF hsym
    hpc hrun hsp_align hx19 hx22 hx25 hx26 hx28 hvregs

set_option maxHeartbeats 1000000 in
/-- Stage P4 `+0x550 → s0.readReg64 .x30` unwind on
`prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc]` under `StageP4Alloc` (`dealloc` only). -/
theorem stageP4_err_unwind_550_prev1_vregs_ok_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (s0 s : State)
    (coroPtr slot ptCap ptPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      decryptPrekeyClosureName + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        (P_f ⊢
          pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          memRegion (coroPtr + 0x280#64) 24 ∗
          memRegion slot 36 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp stageP4ErrUnwindStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      Qp := by
  refine SepWPp.with_steps ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (memRegion36_eq_exists_stagingCells (s.sp + 0x370#64))) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_390 => SepWPp.exists_elim fun u_388 =>
    SepWPp.exists_elim fun u_380 => SepWPp.exists_elim fun u_378 =>
    SepWPp.exists_elim fun u_370 => ?_
  by_cases hcap_z : ptCap = 0#64
  · subst hcap_z
    refine P3P4.SepWPp.weaken_frame (ptextBuf_dealloc_zero A ptPtr pt hpt_le) (by sep_focus) ?_
    simp only [emp_sepConj, sepConj_emp, sepConj_assoc]
    have hstep0 := p4_err_550_zero_vregs_ext_wp img.base ext s coroPtr slot ptPtr
      o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390
      hpc hrun hsp_align hx8 hx19 hx24
    refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep0 (by sep_focus)
      fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hvregs1⟩
    refine P3P4.SepWPp.weaken_frame
      (coro280_words3_entails_memRegion24 coroPtr 0#64 ptPtr (BitVec.ofNat 64 pt.length))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (stagingCellsAt_entails_memRegion36 slot o2 o3 o4 o5 o6) (by sep_focus) ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hx22_1' : s1.readReg64 .x22 = w_22.zeroExtend 64 := hx22_1.trans hx22
    have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hx25, hsp1]
    have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
    have hx28_1' : s1.readReg64 .x28 = errTag := hx28_1.trans hx28
    have htail := stageP4_err_unwind_3588_prev1_vregs_ok_p4 img ext hA hDropSS3 s0 s1
      coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 w_22 o6 b_2c0 enc G st (fun _ _ => False)
      hsp_ub hF1 hsym1 hpc1 hrun1 hsp1_align hx19_1 hx22_1' hx25_1' hx26_1' hx28_1'
      (hvregs1.trans hvregs)
    rw [hsp1] at htail
    refine SepWPp.bind_false_frame htail (by sep_focus)
      fun sf P_f hpcf hrunf ⟨_, hentf, hspf, htrf, hcsf, hvregsf, hFf, hsymf⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hentf) ?_
    refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
    exact ⟨hspf, by rw [htrf, htr1], hcsf, hvregsf, hFf, hsymf⟩
  · refine P3P4.SepWPp.weaken_frame
      (ptextBuf_dealloc_nonzero A ptCap ptPtr pt hcap_z hpt_le) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub)) (by sep_focus) ?_
    simp only [sepConj_assoc]
    have hstep0 := p4_err_550_nonzero_vregs_ext_wp_p4 img.base ext hA s coroPtr slot ptCap ptPtr
      o2 o3 o4 o5 u_370 u_378 u_380 u_388 o6 u_390
      hcap_z hpc hrun hsp_align hx8 hx19 hx24
    refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep0 (by sep_focus)
      fun s1 hpc1 hrun1 hF1 hsym1 hregs1 => ?_
    rcases hregs1 with ⟨hsp1, htr1, hx19_1, hx22_1, _, hx25_1, hx26_1, _, hx28_1, _, hvregs1⟩
    refine P3P4.SepWPp.weaken_frame
      (Entails.of_eq (stack_errUnwind_to_alloc s.sp hsp_ub).symm) (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (coro280_words3_entails_memRegion24 coroPtr ptCap ptPtr (BitVec.ofNat 64 pt.length))
      (by sep_focus) ?_
    refine P3P4.SepWPp.weaken_frame
      (stagingCellsAt_entails_memRegion36 slot o2 o3 o4 o5 o6) (by sep_focus) ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have hx22_1' : s1.readReg64 .x22 = w_22.zeroExtend 64 := hx22_1.trans hx22
    have hx25_1' : s1.readReg64 .x25 = s1.sp + 0x210#64 := by rw [hx25_1, hx25, hsp1]
    have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
    have hx28_1' : s1.readReg64 .x28 = errTag := hx28_1.trans hx28
    have htail := stageP4_err_unwind_3588_prev1_vregs_ok_p4 img ext hA hDropSS3 s0 s1
      coroPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 w_22 o6 b_2c0 enc G st (fun _ _ => False)
      hsp_ub hF1 hsym1 hpc1 hrun1 hsp1_align hx19_1 hx22_1' hx25_1' hx26_1' hx28_1'
      (hvregs1.trans hvregs)
    rw [hsp1] at htail
    refine SepWPp.bind_false_frame htail (by sep_focus)
      fun sf P_f hpcf hrunf ⟨_, hentf, hspf, htrf, hcsf, hvregsf, hFf, hsymf⟩ => ?_
    refine SepWPp.weaken_pre (sepConj_mono_left hentf) ?_
    refine SepWPp.done hpcf hrunf ⟨Entails.of_eq (by ac_rfl), ?_⟩
    exact ⟨hspf, by rw [htrf, htr1], hcsf, hvregsf, hFf, hsymf⟩

theorem stageP4_err_unwind_550_prev1_vregs_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (s0 s : State)
    (coroPtr slot ptCap ptPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 : BitVec 64)
    (w_22 o6 : BitVec 32) (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (Qp : State → SepProp → Prop)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hsp_ub : stageP4ErrUnwindStack ≤ 2 ^ 64)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr
      decryptPrekeyClosureName + 0x550#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = slot)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
       ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
       ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
       (ptPtr ↦ₛ pt) ∗
       (if ptCap = 0#64 then emp
        else A.live ptPtr ptCap.toNat 1 ∗
          memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
       stagingCellsAt slot o2 o3 o4 o5 o6 ∗
       memRegion (s.sp + 0x370#64) 36 ∗
       sessionStateAt A (coroPtr + 0xf8#64) G st ∗
       prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       memRegion outPtr 48 ∗
       decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt s.sp stageP4ErrUnwindStack)
      (fun sf P_f =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        (P_f ⊢
          pollCellsAt outPtr errTag w_22 o2 o3 o4 o5 o6 ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          memRegion (coroPtr + 0x280#64) 24 ∗
          memRegion slot 36 ∗
          memRegion (s.sp + 0x370#64) 36 ∗
          decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt s.sp stageP4ErrUnwindStack) ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab)
      Qp :=
  stageP4_err_unwind_550_prev1_vregs_ok_p4 img ext (StageP4Alloc.of_allocContracts hA) hDropSS3
    s0 s coroPtr slot ptCap ptPtr outPtr errTag prevCap prevPtr o2 o3 o4 o5 w_22 o6 b_2c0 pt enc
    G st Qp hpt_le hsp_ub hF hsym hpc hrun hsp_align hx8 hx19 hx22 hx24 hx25 hx26 hx28 hvregs

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
