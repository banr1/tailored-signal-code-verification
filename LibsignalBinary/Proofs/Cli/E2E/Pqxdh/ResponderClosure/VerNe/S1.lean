/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Consts
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Version-Mismatch Entry Segment (`+0x1e04 → +0x1e78`)

Proves `overVerNe_1e04_to_1e78_4k_ok` and `overVerNe_1e04_to_1e78_ok` on `tripleRatchetProgAtExt`,
logging the initial `st.version ≠ msgVer` mismatch, growing `errs` (`RawVec<SignalProtocolError>`)
to capacity 4 (192 B), storing the first `UnrecognizedMessageVersion` entry (`errs.len = 1`), and
dropping the cloned `SessionStructure` at `sp + 0xa90`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem call_frame_inImage_nopanic_s1 {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q Qp := by
  refine P3P4.SepWPp.call_frame_frozen_nopanic hF hsym hcall hpc hrun hsp hlr
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    (T := T) (F := F) ?_ ⟨⟨hF, hsym⟩, hφ⟩ hP hpan_false hexit_false hnext hoom_false
  dsimp only [Spec.inImage]; rw [hspec, pure_sepConj_pure_assoc]

private theorem sp3e8_336_fold (sp e1 e2 e3 e4 e5 : BitVec 64) :
    ((sp + 0x3e8#64) ↦₆₄ e1) ∗
    ((sp + 0x3f0#64) ↦₆₄ e2) ∗
    ((sp + 0x3f8#64) ↦₆₄ e3) ∗
    ((sp + 0x400#64) ↦₆₄ e4) ∗
    ((sp + 0x408#64) ↦₆₄ e5) ∗
    memRegion (sp + 0x410#64) 296 ⊢
    memRegion (sp + 0x3e8#64) 336 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e8#64) (n := 8) (k := 328) (b' := sp + 0x3f0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f0#64) (n := 8) (k := 320) (b' := sp + 0x3f8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x3f8#64) (n := 8) (k := 312) (b' := sp + 0x400#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x400#64) (n := 8) (k := 304) (b' := sp + 0x408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x408#64) (n := 8) (k := 296) (b' := sp + 0x410#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))))

set_option maxHeartbeats 1000000 in
/-- Version-mismatch entry segment (`+0x1e04 → +0x1e78`) on `tripleRatchetProgAtExt` under `AllocContractsMem4K`. -/
theorem overVerNe_1e04_to_1e78_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsMem4K img.base A ext)
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF1 : img.FrozenLoaded s1) (hsym1 : s1.symtab = img.symtab)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       logOff img ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun s6b P_f =>
        (∃ errsPtr : BitVec 64,
          P_f ⊢
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗
            memRegion (s.sp + 0x3e8#64) 336 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            A.live errsPtr 192 8 ∗
            (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 12#64) 36 ∗
            memRegion (errsPtr + 48#64) 144 ∗
            logOff img ∗
            A.pool ∗
            stackAt s.sp growOneSpeStack) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        img.FrozenLoaded s6b ∧
        s6b.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  have hb_align : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo64_split_sp3e8 s.sp u3e8_w))
    (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_ext_wp img.base ext s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hb_align hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine P3P4.SepWPp.bind_sepWP_frame hF1 hsym1 hstep1 (by sep_focus)
    fun s2 hpc2 hrun2 hF2 hsym2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, _, hx19_2, hx24_2, hx27_2, hx29_2, hx30_2, hvregs_2⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  have hx24_2' : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_2.trans hx24_1
  have hx27_2' : s2.readReg64 .x27 = ctxPtr := hx27_2.trans hx27_1
  have hx29_2' : s2.readReg64 .x29 = s.sp + 0xc70#64 := hx29_2.trans hx29_1
  have hlog := pqxdh_log_closure_ok_ext (ext := ext) himg
  have hpc2_log : s2.pc =
    (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName := by
    rw [hpc2, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      show libsignalSessionCode.fnOff
          CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName =
        (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") from
        (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_frame_inImage_nopanic_s1
    (spec := pqxdhLogClosureSpec img) (x := ()) (φ := True)
    (T := logOff img ∗ stackAt s.sp pqxdhClosureStack)
    hF2 hsym2 hlog hpc2_log hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosureSpec]; rw [hsp2_s, pure_true, emp_sepConj])
    trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hF3 hsym3 => ?_)
  dsimp only [pqxdhLogClosureSpec]
  rw [hsp2_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr3_2 => ?_
  have hstack_restore3 :
      memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_log]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore3 (by sep_focus) ?_
  have hsp3_s : s3.sp = s.sp := hsp3_2.trans hsp2_s
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3_s]; exact hsp_align
  rcases hcs3 with ⟨hx19_cs3, _, _, _, _, hx24_cs3, _, _, hx27_cs3, _, hx29_cs3, hvregs_cs3⟩
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64 := hx24_cs3.trans hx24_2'
  have hx27_3 : s3.readReg64 .x27 = ctxPtr := hx27_cs3.trans hx27_2'
  have hx29_3 : s3.readReg64 .x29 = s.sp + 0xc70#64 := hx29_cs3.trans hx29_2'
  have hstep3 := p3_err_ver_b_ext_wp img.base ext s3 coroPtr hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hstep3
  refine P3P4.SepWPp.bind_sepWP_frame hF3 hsym3 hstep3 (by sep_focus)
    fun s4 hpc4 hrun4 hF4 hsym4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, hx29_4, hx30_4, hvregs_4⟩
  have hsp4_s : s4.sp = s.sp := hsp4_3
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  have hgrow := grow_one_spe_ok_ext (b := img.base) (ext := ext) (finish_grow_ok_of_mem4k hA)
  have hpc4_grow : s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr growOneSpeSym := by
    rw [hpc4, fnAddr_growOneSpe_eq]
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine P3P4.SepWPp.call_frame_frozen_oom
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool ∗ stackAt s.sp growOneSpeStack)
    hF4 hsym4 htr4_0 hgrow hpc4_grow hrun4 hsp4_al hx30_4
    (by
      rw [growOneSpe_pre_zero_eq A s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne, hsp4_s,
        pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial
    (by sep_focus)
    (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hF5 hsym5 => ?_)
  rw [growOneSpe_post_zero_eq A s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr5_4 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (pointsTo32_pair_sp3e8 s.sp msgVer (u3e8_w.extractLsb' 32 32)))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq errsPtr)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u_e5 => SepWPp.exists_elim fun u_e4 =>
    SepWPp.exists_elim fun u_e3 => SepWPp.exists_elim fun u_e2 =>
    SepWPp.exists_elim fun u_e1 => SepWPp.exists_elim fun u_e0 => ?_
  have hsp5_s : s5.sp = s.sp := hsp5_4.trans hsp4_s
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5_s]; exact hsp_align
  rcases hcs5 with ⟨hx19_cs5, _, hx21_cs5, _, _, hx24_cs5, _, _, hx27_cs5, _, hx29_cs5, hvregs_cs5⟩
  have hx19_5 : s5.readReg64 .x19 = coroPtr := hx19_cs5.trans hx19_4
  have hx21_5 : s5.readReg64 .x21 = 0#64 := hx21_cs5.trans hx21_4
  have hx24_5 : s5.readReg64 .x24 = s5.sp + 0x370#64 := by
    rw [hx24_cs5, hx24_4, hx24_3, hsp5_s]
  have hx27_5 : s5.readReg64 .x27 = ctxPtr := hx27_cs5.trans (hx27_4.trans hx27_3)
  have hx29_5 : s5.readReg64 .x29 = s.sp + 0xc70#64 := hx29_cs5.trans (hx29_4.trans hx29_3)
  have hstep5 := p3_err_ver_c_ext_wp img.base ext s5 coroPtr errsPtr
    0x8000000000000006#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align hx19_5 hx21_5 hx24_5
  rw [hsp5_s, hx27_5] at hstep5
  refine P3P4.SepWPp.bind_sepWP_frame hF5 hsym5 hstep5 (by sep_focus)
    fun s6 hpc6 hrun6 hF6 hsym6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, hx29_6, hx30_6, hvregs_6⟩
  refine P3P4.SepWPp.weaken_frame
    (errs48_fold_ver errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp3e8_336_fold s.sp (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_s] using hsp_align
  have hdropSs3 := drop_session_structure3_ok_of_mem4k (b := img.base) (ext := ext) hA
  have hpc6_drop : s6.pc =
    (tripleRatchetProgAtExt img.base ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name := by
    rw [hpc6, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine P3P4.SepWPp.call_frame_frozen_nopanic
    (x := (⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost))
    (T := sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hF6 hsym6 hdropSs3 hpc6_drop hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]; rw [hsp6_s])
    hx0_6 (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hF6b hsym6b => ?_)
  dsimp only [dropSessionStructure2Spec, dropSessionStructureLocal2Spec]
  rw [hsp6_s, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6b_6 => ?_
  have hstack_restore6b :
      memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack ⊢
        stackAt s.sp growOneSpeStack := by
    rw [hstack_drop2]; exact Entails.refl _
  refine P3P4.SepWPp.weaken_frame hstack_restore6b (by sep_focus) ?_
  rcases hcs6b with ⟨hx19_cs6b, _, _, _, _, _, _, _, _, _, hx29_cs6b, hvregs_cs6b⟩
  have hsp6b_s : s6b.sp = s.sp := hsp6b_6.trans hsp6_s
  have htr6b_0 : s6b.trace = s0.trace :=
    htr6b_6.trans (htr6_5.trans (htr5_4.trans htr4_0))
  have hx19_6b : s6b.readReg64 .x19 = coroPtr := hx19_cs6b.trans hx19_6
  have hx29_6b : s6b.readReg64 .x29 = s.sp + 0xc70#64 := hx29_cs6b.trans (hx29_6.trans hx29_5)
  have hvregs_6b : calleeSavedVRegs s6b = calleeSavedVRegs s1 := by
    rw [hvregs_cs6b, hvregs_6, hvregs_cs5, hvregs_4, hvregs_cs3, hvregs_2]
  refine SepWPp.done hpc6b hrun6b
    ⟨⟨errsPtr, Entails.of_eq (by ac_rfl)⟩,
     hsp6b_s, htr6b_0, hx19_6b, hx29_6b, hvregs_6b, hF6b, hsym6b⟩

theorem overVerNe_1e04_to_1e78_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hF1 : img.FrozenLoaded s1) (hsym1 : s1.symtab = img.symtab)
    (hpc1 : s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       logOff img ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun s6b P_f =>
        (∃ errsPtr : BitVec 64,
          P_f ⊢
            ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 4#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗
            memRegion (s.sp + 0x3e8#64) 336 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            A.live errsPtr 192 8 ∗
            (errsPtr ↦₆₄ 0x8000000000000006#64) ∗
            ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
            memRegion (errsPtr + 12#64) 36 ∗
            memRegion (errsPtr + 48#64) 144 ∗
            logOff img ∗
            A.pool ∗
            stackAt s.sp growOneSpeStack) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        img.FrozenLoaded s6b ∧
        s6b.symtab = img.symtab)
      (P3P4.PanicOomProp s0) :=
  overVerNe_1e04_to_1e78_4k_ok img ext himg (.of_AllocContracts hA)
    s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
    hF1 hsym1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
