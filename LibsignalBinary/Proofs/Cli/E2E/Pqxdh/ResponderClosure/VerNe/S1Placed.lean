/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNe
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenSub5
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenVerNeBlocks
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpe

/-!
# Relocatable Version-Mismatch Entry Segment (`+0x1e04 → +0x1e78`)

Relocatable (`[LibsignalPlacement]` / `[LibsignalFullPlacement]`) proofs of the initial
version-mismatch segment (`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518`.
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
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.CliHandshake.RespClosurePlaced
open ProofLib.GenPlacedFetches
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable `[LibsignalFullPlacement]` Stage P3 `VerNe` entry segment
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext`. -/
def OverVerNe1e04To1e78CliPlacedStmt [LibsignalFullPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64),
    initErrsPtr ≠ 0#64 →
    ∀ (msgVer : BitVec 32) (G₁ : SessionGhost) (st : SessionState (List (BitVec 8))),
      LibsignalFrozen lsmpl s1.mem →
      (lsProg_518 ext).CodeLoaded s1.mem →
      s1.pc = (blkPl_518).base + 0x1e04#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      (s.sp &&& 15#64 == 0#64) = true →
      s1.trace = s0.trace →
      s1.readReg64 .x9 = msgVer.setWidth 64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x24 = s.sp + 0x370#64 →
      s1.readReg64 .x27 = ctxPtr →
      s1.readReg64 .x29 = s.sp + 0xc70#64 →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
        (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
         ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         memRegion (s.sp + 0x3e0#64) 344 ∗
         sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
         pqLogLevelCellPlaced ∗
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
              pqLogLevelCellPlaced ∗
              A.pool ∗
              stackAt s.sp growOneSpeStack) ∧
          s6b.sp = s.sp ∧
          s6b.trace = s0.trace ∧
          s6b.readReg64 .x19 = coroPtr ∧
          s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
          calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
          (lsProg_518 ext).CodeLoaded s6b.mem)
        (P3P4.PanicOomProp s0)

/-! ## Spatial and call helpers -/

private theorem sp3e8_336_fold_s1 (sp e1 e2 e3 e4 e5 : BitVec 64) :
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

private theorem pointsTo64_split_sp3e8_s1 (sp w : BitVec 64) :
    ((sp + 0x3e8#64) ↦₆₄ w) =
      (((sp + 0x3e8#64) ↦₃₂ (w.extractLsb' 0 32)) ∗
       ((sp + 0x3ec#64) ↦₃₂ (w.extractLsb' 32 32))) := by
  have h1 : sp + 0x3ec#64 = (sp + 0x3e8#64) + 4#64 := by bv_omega
  rw [h1, pointsTo64_split32]

private theorem pointsTo32_pair_sp3e8_s1 (sp : BitVec 64) (lo hi : BitVec 32) :
    (((sp + 0x3e8#64) ↦₃₂ lo) ∗ ((sp + 0x3ec#64) ↦₃₂ hi)) =
      ((sp + 0x3e8#64) ↦₆₄ (hi ++ lo)) := by
  have h : sp + 0x3ec#64 = (sp + 0x3e8#64) + 4#64 := by bv_omega
  rw [h, pointsTo32_pair]

private theorem errs192_split_eq_s1 (errsPtr : BitVec 64) :
    memRegion errsPtr 192 = (∃∗ u_e5 : BitVec 64, ∃∗ u_e4 : BitVec 64, ∃∗ u_e3 : BitVec 64,
      ∃∗ u_e2 : BitVec 64, ∃∗ u_e1 : BitVec 64, ∃∗ u_e0 : BitVec 64,
      (errsPtr ↦₆₄ u_e0) ∗ ((errsPtr + 8#64) ↦₆₄ u_e1) ∗
      ((errsPtr + 16#64) ↦₆₄ u_e2) ∗ ((errsPtr + 24#64) ↦₆₄ u_e3) ∗
      ((errsPtr + 32#64) ↦₆₄ u_e4) ∗ ((errsPtr + 40#64) ↦₆₄ u_e5) ∗
      memRegion (errsPtr + 48#64) 144) := by
  rw [ProofLib.memRegion_split' (b := errsPtr) (n := 8) (k := 184) (b' := errsPtr + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 8#64) (n := 8) (k := 176) (b' := errsPtr + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 16#64) (n := 8) (k := 168) (b' := errsPtr + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 24#64) (n := 8) (k := 160) (b' := errsPtr + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 32#64) (n := 8) (k := 152) (b' := errsPtr + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 40#64) (n := 8) (k := 144) (b' := errsPtr + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight errsPtr, ProofLib.memRegion_eight (errsPtr + 8#64),
      ProofLib.memRegion_eight (errsPtr + 16#64), ProofLib.memRegion_eight (errsPtr + 24#64),
      ProofLib.memRegion_eight (errsPtr + 32#64), ProofLib.memRegion_eight (errsPtr + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private theorem errs48_fold_ver_s1 (errsPtr e2 e3 e4 e5 : BitVec 64) (msgVer u3ec : BitVec 32) :
    (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₆₄ (u3ec ++ msgVer)) ∗
    ((errsPtr + 16#64) ↦₆₄ e2) ∗ ((errsPtr + 24#64) ↦₆₄ e3) ∗ ((errsPtr + 32#64) ↦₆₄ e4) ∗
    ((errsPtr + 40#64) ↦₆₄ e5) ⊢
    (errsPtr ↦₆₄ 0x8000000000000006#64) ∗ ((errsPtr + 8#64) ↦₃₂ msgVer) ∗
    memRegion (errsPtr + 12#64) 36 := by
  have hpair : ((errsPtr + 8#64) ↦₆₄ (u3ec ++ msgVer)) =
      ((errsPtr + 8#64) ↦₃₂ msgVer) ∗ ((errsPtr + 12#64) ↦₃₂ u3ec) := by
    have h12 : errsPtr + 12#64 = (errsPtr + 8#64) + 4#64 := by bv_omega
    rw [h12, ← pointsTo32_pair]
  rw [hpair, sepConj_assoc,
      ProofLib.memRegion_split' (b := errsPtr + 12#64) (n := 4) (k := 32) (b' := errsPtr + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 16#64) (n := 8) (k := 24) (b' := errsPtr + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 24#64) (n := 8) (k := 16) (b' := errsPtr + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := errsPtr + 32#64) (n := 8) (k := 8) (b' := errsPtr + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))))

private theorem bind_sepWP_cl_frame_s1 {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem call_raw_nopanic_cl_s1 {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

private theorem call_raw_oom_cl_s1 {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hL : prog.CodeLoaded s.mem) (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm _
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, P3P4.allowPanic_oom_of_trace_eq htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

/-! ## Basic-block segments (`+0x1e04 → +0x1e78`) -/

private theorem p3_ver_ne_1e04_s1_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr u3e0 : BitVec 64) (msgVer u3e8 : BitVec 32)
    (hpc : s.pc = (blkPl_518).base + 0x1e04#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx9 : s.readReg64 .x9 = msgVer.setWidth 64)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 519) s
      (((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0x3e8#64) ↦₃₂ u3e8))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3e0#64) ↦₆₄ 0x8000000000000006#64) ∗ ((s.sp + 0x3e8#64) ↦₃₂ msgVer)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3b0#64 ∧
        s1.readReg64 .x2 = 7#64 ∧ s1.readReg64 .x3 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x4 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = (blkPl_518).base + 0x1e30#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgVer.setWidth 64 := hx9
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private theorem p3_err_ver_b_s1_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1e30#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 42) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0x3c8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = (blkPl_518).base + 0x1e48#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

private theorem p3_err_ver_c_s1_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr errsPtr errTag e1 e2 e3 e4 e5 u_c0 u_e0 u_e1 u_e2 u_e3 u_e4 u_e5 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1e48#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = 0#64) (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 512) s
      (((s.sp + 0xc0#64) ↦₆₄ u_c0) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗ ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗ ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗ ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗ ((s.sp + 0x408#64) ↦₆₄ e5) ∗
       ((errsPtr + 0x0#64) ↦₆₄ u_e0) ∗ ((errsPtr + 0x8#64) ↦₆₄ u_e1) ∗ ((errsPtr + 0x10#64) ↦₆₄ u_e2) ∗
       ((errsPtr + 0x18#64) ↦₆₄ u_e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ u_e4) ∗ ((errsPtr + 0x28#64) ↦₆₄ u_e5))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xc0#64) ↦₆₄ s.readReg64 .x27) ∗ ((s.sp + 0x3d0#64) ↦₆₄ errsPtr) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x3e0#64) ↦₆₄ errTag) ∗ ((s.sp + 0x3e8#64) ↦₆₄ e1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ e2) ∗ ((s.sp + 0x3f8#64) ↦₆₄ e3) ∗ ((s.sp + 0x400#64) ↦₆₄ e4) ∗
          ((s.sp + 0x408#64) ↦₆₄ e5) ∗ ((errsPtr + 0x0#64) ↦₆₄ errTag) ∗ ((errsPtr + 0x8#64) ↦₆₄ e1) ∗
          ((errsPtr + 0x10#64) ↦₆₄ e2) ∗ ((errsPtr + 0x18#64) ↦₆₄ e3) ∗ ((errsPtr + 0x20#64) ↦₆₄ e4) ∗
          ((errsPtr + 0x28#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1e78#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## `LibsignalCodeRoLoaded`-threaded composition -/

open CryptoVerification.LibsignalPublicApi

private theorem bind_sepWP_cro_frame_s1 [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hcrom : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
    hcro.of_keepsFrozen hsteps.keepsFrozen
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hcrom hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem call_raw_nopanic_cro_s1 [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm _
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcro.1, hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at _hoom_post; rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hcrom : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
      hcro.of_keepsFrozen hsteps.keepsFrozen
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hcrom hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

private theorem call_raw_oom_cro_s1 [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hL : prog.CodeLoaded s.mem) (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (P3P4.PanicOomProp s0)) :
    SepWPp prog ret s P Q (P3P4.PanicOomProp s0) := by
  intro R hm _
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcro.1, hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · dsimp only [withLsCodeLoaded] at _hoom_post; rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hcrom : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
      hcro.of_keepsFrozen hsteps.keepsFrozen
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hcrom hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, P3P4.allowPanic_oom_of_trace_eq htr⟩)⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 1000000 in
/-- `StoreKit.LibsignalCodeRoLoaded lsmpl`-threaded proof of `VerNe/S1`
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext`. -/
theorem overVerNe_1e04_to_1e78_cro_placed_at [LibsignalPlacement]
    {A : RustAlloc} (ext : String → Option (State → State))
    (hLogClosure : subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
      (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       pqLogLevelCellPlaced ∗
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
            pqLogLevelCellPlaced ∗
            A.pool ∗
            stackAt s.sp growOneSpeStack) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s6b.mem ∧
        (lsProg_518 ext).CodeLoaded s6b.mem)
      (P3P4.PanicOomProp s0) := by
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo64_split_sp3e8_s1 s.sp u3e8_w))
    (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_s1_placed_wp ext s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine bind_sepWP_cro_frame_s1 hcro1 hL1 hstep1 (by sep_focus)
    fun s2 hpc2 hrun2 hcro2 hL2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, hx29_2, hx30_2, hvregs_2⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  have hx24_2' : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_2.trans hx24_1
  have hx27_2' : s2.readReg64 .x27 = ctxPtr := hx27_2.trans hx27_1
  have hx29_2' : s2.readReg64 .x29 = s.sp + 0xc70#64 := hx29_2.trans hx29_1
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_raw_nopanic_cro_s1
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hcro2 hL2 hLogClosure hpc2 hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_s])
    trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hcro3 hL3 => ?_)
  dsimp only [pqxdhLogClosurePlacedSpec]
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
  have hstep3 := p3_err_ver_b_s1_placed_wp ext s3 coroPtr hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hstep3
  refine bind_sepWP_cro_frame_s1 hcro3 hL3 hstep3 (by sep_focus)
    fun s4 hpc4 hrun4 hcro4 hL4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, hx29_4, hx30_4, hvregs_4⟩
  have hsp4_s : s4.sp = s.sp := hsp4_3
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_raw_oom_cro_s1
    (spec := growOneSpeSpec A)
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro4 hL4 htr4_0 hGrow hpc4 hrun4 hsp4_al hx30_4
    (by
      rw [growOneSpe_pre_zero_eq A s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne, hsp4_s,
        pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial
    (by sep_focus)
    (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 hL5 => ?_)
  rw [growOneSpe_post_zero_eq A s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr5_4 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (pointsTo32_pair_sp3e8_s1 s.sp msgVer (u3e8_w.extractLsb' 32 32)))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq_s1 errsPtr)) (by sep_focus) ?_
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
  have hstep5 := p3_err_ver_c_s1_placed_wp ext s5 coroPtr errsPtr
    0x8000000000000006#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align hx19_5 hx21_5 hx24_5
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_cro_frame_s1 hcro5 hL5 hstep5 (by sep_focus)
    fun s6 hpc6 hrun6 hcro6 hL6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, hx29_6, hx30_6, hvregs_6⟩
  refine P3P4.SepWPp.weaken_frame
    (errs48_fold_ver_s1 errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp3e8_336_fold_s1 s.sp (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_s] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_raw_nopanic_cro_s1
    (spec := dropSessionStructureLocal2Spec A)
    (x := (⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost))
    (φ := s6.readReg64 .x0 = s.sp + 0xa90#64)
    (T := sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro6 hL6 hDropSS3 hpc6 hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_s])
    hx0_6 (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hcro6b hL6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
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
     hsp6b_s, htr6b_0, hx19_6b, hx29_6b, hvregs_6b, hcro6b, hL6b⟩

/-! ## `LibsignalFrozen` variant and `OverVerNe1e04To1e78CliPlacedStmt` -/

set_option maxHeartbeats 1000000 in
/-- `LibsignalFrozen lsmpl`-threaded proof of `VerNe/S1`
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext`
under `[LibsignalFullPlacement]`, discharging Block `519` internally. -/
theorem overVerNe_1e04_to_1e78_frozen_placed_at [LibsignalFullPlacement]
    {A : RustAlloc} (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       pqLogLevelCellPlaced ∗
       A.pool ∗
       stackAt s.sp growOneSpeStack)
      (fun s6b P_f =>
        ((∃ errsPtr : BitVec 64,
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
            pqLogLevelCellPlaced ∗
            A.pool ∗
            stackAt s.sp growOneSpeStack) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s6b.mem ∧
        (lsProg_518 ext).CodeLoaded s6b.mem) ∧
        LibsignalFrozen lsmpl s6b.mem)
      (P3P4.PanicOomProp s0) := by
  refine Matched.sepWPp_strengthen_frozen hfr1 ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hs1_sp]; exact hsp_align
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion344_3e0_split_eq s.sp)) (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (memRegion48_words6_split_eq (s.sp + 0x3e0#64)))
    (by sep_focus) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun u3e0 => SepWPp.exists_elim fun u3e8_w =>
    SepWPp.exists_elim fun e2 => SepWPp.exists_elim fun e3 =>
    SepWPp.exists_elim fun e4 => SepWPp.exists_elim fun e5 => ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (pointsTo64_split_sp3e8_s1 s.sp u3e8_w))
    (by sep_focus) ?_
  have hstep1 := p3_ver_ne_1e04_s1_placed_wp ext s1 coroPtr u3e0 msgVer
    (u3e8_w.extractLsb' 0 32) hpc1 hrun1 hsp1_align hx9_1 hx19_1
  rw [hs1_sp] at hstep1
  refine bind_sepWP_fr_frame hL1 hfr1 hstep1 (by sep_focus)
    fun s2 hpc2 hrun2 hL2 hfr2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, _, _, _, _, hx19_2, hx24_2, hx27_2, hx29_2, hx30_2, hvregs_2⟩
  have hsp2_s : s2.sp = s.sp := hsp2_1
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_s] using hsp_align
  have hx24_2' : s2.readReg64 .x24 = s.sp + 0x370#64 := hx24_2.trans hx24_1
  have hx27_2' : s2.readReg64 .x27 = ctxPtr := hx27_2.trans hx27_1
  have hx29_2' : s2.readReg64 .x29 = s.sp + 0xc70#64 := hx29_2.trans hx29_1
  have hstack_log :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 4176 ∗ stackAt s.sp pqxdhClosureStack :=
    stackAt_split_bottom s.sp pqxdhClosureStack 4176 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_log) (by sep_focus) ?_
  refine call_raw_nopanic_fr
    (spec := pqxdhLogClosurePlacedSpec) (x := ()) (φ := True)
    (T := pqLogLevelCellPlaced ∗ stackAt s.sp pqxdhClosureStack)
    hL2 hfr2 (pqxdh_log_closure_verNe_frozen_placed_ok_of_block (callerProg := lsProg_518 ext))
    hpc2 hrun2 hsp2_al hx30_2
    (by dsimp only [pqxdhLogClosurePlacedSpec]; rw [hsp2_s])
    trivial (by sep_focus)
    (hnext := fun s3 hpc3 hrun3 hsp3_2 _ hcs3 hL3 hfr3 => ?_)
  have hcro3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := Matched.lscro_of_frozen hfr3
  dsimp only [pqxdhLogClosurePlacedSpec]
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
  have hstep3 := p3_err_ver_b_s1_placed_wp ext s3 coroPtr hpc3 hrun3 hsp3_align hx19_3
  rw [hsp3_s] at hstep3
  refine bind_sepWP_cro_frame_s1 hcro3 hL3 hstep3 (by sep_focus)
    fun s4 hpc4 hrun4 hcro4 hL4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, hx0_4, hx19_4, hx21_4, hx24_4, hx27_4, hx29_4, hx30_4, hvregs_4⟩
  have hsp4_s : s4.sp = s.sp := hsp4_3
  have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_s] using hsp_align
  have htr4_0 : s4.trace = s0.trace := htr4_3.trans (htr3_2.trans (htr2_1.trans htr1))
  refine call_raw_oom_cro_s1
    (spec := growOneSpeSpec A)
    (x := (s.sp + 0x3c8#64, 0#64, initErrsPtr, ([] : List (BitVec 8))))
    (φ := True)
    (T := ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
          A.pool ∗ stackAt s.sp growOneSpeStack)
    hcro4 hL4 htr4_0 hGrow hpc4 hrun4 hsp4_al hx30_4
    (by
      rw [growOneSpe_pre_zero_eq A s4 (s.sp + 0x3c8#64) initErrsPtr hx0_4 hinit_ne, hsp4_s,
        pure_true, emp_sepConj]
      simp only [BitVec.add_assoc, BitVec.reduceAdd])
    trivial
    (by sep_focus)
    (hnext := fun s5 hpc5 hrun5 hsp5_4 _ hcs5 hcro5 hL5 => ?_)
  rw [growOneSpe_post_zero_eq A s4 s5 (s.sp + 0x3c8#64) initErrsPtr, hsp4_s]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left,
    sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun errsPtr => ?_
  refine SepWPp.pure_elim fun htr5_4 => ?_
  refine SepWPp.pure_elim fun _ => ?_
  refine P3P4.SepWPp.weaken_frame
    (Entails.of_eq (pointsTo32_pair_sp3e8_s1 s.sp msgVer (u3e8_w.extractLsb' 32 32)))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq (errs192_split_eq_s1 errsPtr)) (by sep_focus) ?_
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
  have hstep5 := p3_err_ver_c_s1_placed_wp ext s5 coroPtr errsPtr
    0x8000000000000006#64 (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5 ctxPtr
    u_e0 u_e1 u_e2 u_e3 u_e4 u_e5
    hpc5 hrun5 hsp5_align hx19_5 hx21_5 hx24_5
  rw [hsp5_s, hx27_5] at hstep5
  refine bind_sepWP_cro_frame_s1 hcro5 hL5 hstep5 (by sep_focus)
    fun s6 hpc6 hrun6 hcro6 hL6 hregs6 => ?_
  rcases hregs6 with ⟨hsp6_5, htr6_5, hx0_6, hx19_6, _, _, hx29_6, hx30_6, hvregs_6⟩
  refine P3P4.SepWPp.weaken_frame
    (errs48_fold_ver_s1 errsPtr e2 e3 e4 e5 msgVer (u3e8_w.extractLsb' 32 32))
    (by sep_focus) ?_
  refine P3P4.SepWPp.weaken_frame
    (sp3e8_336_fold_s1 s.sp (u3e8_w.extractLsb' 32 32 ++ msgVer) e2 e3 e4 e5)
    (by sep_focus) ?_
  have hsp6_s : s6.sp = s.sp := hsp6_5
  have hsp6_al : s6.spAligned = true := by simpa only [State.spAligned, hsp6_s] using hsp_align
  have hstack_drop2 :
      stackAt s.sp growOneSpeStack =
        memRegion (s.sp - 4608#64) 416 ∗ stackAt s.sp dropSessionStructure2Stack :=
    stackAt_split_bottom s.sp dropSessionStructure2Stack 416 (by decide)
  refine P3P4.SepWPp.weaken_frame (Entails.of_eq hstack_drop2) (by sep_focus) ?_
  refine call_raw_nopanic_cro_s1
    (spec := dropSessionStructureLocal2Spec A)
    (x := (⟨s.sp + 0xa90#64, G₁, st⟩ : DropSessionStructureGhost))
    (φ := s6.readReg64 .x0 = s.sp + 0xa90#64)
    (T := sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗ A.pool ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro6 hL6 hDropSS3 hpc6 hrun6 hsp6_al hx30_6
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp6_s])
    hx0_6 (by sep_focus)
    (hnext := fun s6b hpc6b hrun6b hsp6b_6 _ hcs6b hcro6b hL6b => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
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
     hsp6b_s, htr6b_0, hx19_6b, hx29_6b, hvregs_6b, hcro6b, hL6b⟩

/-- Pointwise proof of `OverVerNe1e04To1e78CliPlacedStmt`
(`(blkPl_518).base + 0x1e04 → (blkPl_518).base + 0x1e78`) on `lsProg_518 ext`
under `[LibsignalFullPlacement]`. -/
theorem overVerNe_1e04_to_1e78_cli_placed_at [LibsignalFullPlacement]
    {A : RustAlloc} (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s s1 : State) (coroPtr ctxPtr initErrsPtr : BitVec 64)
    (hinit_ne : initErrsPtr ≠ 0#64)
    (msgVer : BitVec 32)
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hfr1 : LibsignalFrozen lsmpl s1.mem)
    (hL1 : (lsProg_518 ext).CodeLoaded s1.mem)
    (hpc1 : s1.pc = (blkPl_518).base + 0x1e04#64)
    (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx9_1 : s1.readReg64 .x9 = msgVer.setWidth 64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr)
    (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hx29_1 : s1.readReg64 .x29 = s.sp + 0xc70#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x1e78#64) s1
      (((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A (s.sp + 0xa90#64) G₁ st ∗
       pqLogLevelCellPlaced ∗
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
            pqLogLevelCellPlaced ∗
            A.pool ∗
            stackAt s.sp growOneSpeStack) ∧
        s6b.sp = s.sp ∧
        s6b.trace = s0.trace ∧
        s6b.readReg64 .x19 = coroPtr ∧
        s6b.readReg64 .x29 = s.sp + 0xc70#64 ∧
        calleeSavedVRegs s6b = calleeSavedVRegs s1 ∧
        (lsProg_518 ext).CodeLoaded s6b.mem)
      (P3P4.PanicOomProp s0) := by
  intro R hm _
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, ⟨hP, hsp, htr, hx19, hx29, hvr, _, hLf⟩, _⟩ | hpan⟩ :=
    overVerNe_1e04_to_1e78_frozen_placed_at ext hGrow hDropSS3
      s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
      hfr1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 R hm hL1
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, hP, hsp, htr, hx19, hx29, hvr, hLf⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-- Proves `OverVerNe1e04To1e78CliPlacedStmt` on `lsProg_518 ext` under `[LibsignalFullPlacement]`. -/
theorem overVerNe_1e04_to_1e78_cli_placed [LibsignalFullPlacement]
    (hGrow : ∀ {A : RustAlloc} ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec A)))
    (hDropSS3 : ∀ {A : RustAlloc} ext,
      subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
        (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A))) :
    OverVerNe1e04To1e78CliPlacedStmt :=
  fun {A} ext s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
      hfr1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1 =>
    overVerNe_1e04_to_1e78_cli_placed_at ext
      (hGrow (A := A) ext) (hDropSS3 (A := A) ext)
      s0 s s1 coroPtr ctxPtr initErrsPtr hinit_ne msgVer G₁ st
      hfr1 hL1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1 hx29_1

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
