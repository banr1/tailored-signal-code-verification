/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2AuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.E2E.Bin.Hooks
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.TripleRatchet.Glue
import ProofLib.SepLogic.WPp

/-!
# Relocatable Stage P2 Shared Error-Return Record Teardown

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2` on Block `518` (`lsProg_518 ext`,
`(blkPl_518).base = lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Glue
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp eq_of_sep_emp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

theorem sessionRecordAt_some_eq_prev_sess_placed [LibsignalPlacement]
    (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess) :
    sessionRecordAt A (coroPtr + 0xe0#64) g r ⊢
      ∃∗ recG : SessionGhost,
        ⌜g.cur = some recG⌝ ∗
        prevSessionsEmptyAt A coroPtr g ∗
        sessionStateReprAt A (coroPtr + 0xf8#64) recG sess :=
  sessionRecordAt_some_eq_prev_sess A coroPtr g r sess hcur

theorem prevSessionsEmptyAt_restore_record_placed [LibsignalPlacement]
    (A : RustAlloc) (coroPtr : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hgc : g.cur = some recG) (hcur : r.currentSession = some sess) :
    prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ⊢
      sessionRecordAt A (coroPtr + 0xe0#64) g r :=
  prevSessionsEmptyAt_restore_record A coroPtr g recG r sess hgc hcur

theorem prevSessionsEmptyAt_unpack_placed [LibsignalPlacement]
    (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost) :
    prevSessionsEmptyAt A coroPtr g ⊢
      ⌜g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0#64⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ g.prevCap) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
      (if g.prevCap = 0#64 then emp
       else A.live g.prevPtr (g.prevCap.toNat * 24) 8 ∗
         memRegion g.prevPtr (g.prevCap.toNat * 24)) :=
  prevSessionsEmptyAt_unpack A coroPtr g

theorem prevSessionsEmptyAt_zero_placed [LibsignalPlacement]
    (A : RustAlloc) (coroPtr : BitVec 64) (g : RecordGhost)
    (hzero : g.prevCap = 0#64) :
    prevSessionsEmptyAt A coroPtr g ⊢
      ⌜g.prevPtr ≠ 0#64⌝ ∗
      ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
      ((coroPtr + 0xe8#64) ↦₆₄ g.prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 0#64) :=
  prevSessionsEmptyAt_zero A coroPtr g hzero

theorem coro_e0_3w_344_entails_368_placed [LibsignalPlacement]
    (coroPtr w0 w1 w2 : BitVec 64) :
    ((coroPtr + 0xe0#64) ↦₆₄ w0) ∗
    ((coroPtr + 0xe8#64) ↦₆₄ w1) ∗
    ((coroPtr + 0xf0#64) ↦₆₄ w2) ∗
    memRegion (coroPtr + 0xf8#64) 344 ⊢
      memRegion (coroPtr + 0xe0#64) 368 :=
  coro_e0_3w_344_entails_368 coroPtr w0 w1 w2

theorem sp370_4w64_w32_entails_36_placed [LibsignalPlacement]
    (sp w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) :
    ((sp + 0x370#64) ↦₆₄ w0) ∗
    ((sp + 0x378#64) ↦₆₄ w1) ∗
    ((sp + 0x380#64) ↦₆₄ w2) ∗
    ((sp + 0x388#64) ↦₆₄ w3) ∗
    ((sp + 0x390#64) ↦₃₂ w4) ⊢
      memRegion (sp + 0x370#64) 36 :=
  sp370_4w64_w32_entails_36 sp w0 w1 w2 w3 w4

theorem sessionStateAt_split_localIk_cap_placed [LibsignalPlacement]
    (A : RustAlloc) (ss : BitVec 64)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8))) :
    ∃ R_ss : SepProp,
      (sessionStateAt A ss recG recSt ⊢
        ⌜recG.localIk.cap.toNat < 2 ^ 63⌝ ∗ (ss ↦₆₄ recG.localIk.cap) ∗ R_ss) ∧
      ((ss ↦₆₄ recG.localIk.cap) ∗ R_ss ⊢
        sessionStateAt A ss recG recSt) :=
  sessionStateAt_split_localIk_cap A ss recG recSt

/-! ## `SepWPp` combinators carrying `StoreKit.LibsignalCodeRoLoaded` -/

theorem lscro_of_steps_m2_placed [LibsignalPlacement] {prog : Program} {s sm : State}
    (hsteps : Steps prog s sm) (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) :
    StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem :=
  hcro.of_keepsFrozen hsteps.keepsFrozen

theorem bind_sepWP_lscro_steps_m2_placed [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpcm hrunm (lscro_of_steps_m2_placed hsteps hcro) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem ret_sepWP_lscro_steps_m2_placed [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog ret s P_step (fun sf P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hret : ∀ sf : State, Steps prog s sf → sf.pc = ret → sf.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem → Q_regs sf →
      Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp :=
  bind_sepWP_lscro_steps_m2_placed hcro hstep hP fun sf hsteps hpc hrun hcro' hregs =>
    SepWPp.done hpc hrun (hret sf hsteps hpc hrun hcro' hregs)

theorem call_raw_nopanic_m2_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right; · rw [hoom_false] at hoom_post; exact (not_satisfies_false_sepConj hoom_post).elim
  · rw [← sepConj_assoc] at hpost; rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm (lscro_of_steps_m2_placed hsteps hcro) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_false] at hpost; exact (allowPanic_not_exited hpost).elim
  · rw [hexit_false] at hpost; exact (allowPanic_not_exited hpost).elim

theorem call_lscro_nopanic_m2_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hpre_eq : (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s = (⌜φ ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ T) := by
    dsimp only [StoreKit.withLsCodeRoLoaded]
    rw [hspec, sepConj_assoc, sepConj_comm T, ← sepConj_assoc, pure_sepConj_pure]
  exact call_raw_nopanic_m2_placed (spec := StoreKit.withLsCodeRoLoaded lsmpl spec) (x := x)
    (φ := φ ∧ StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (T := T) (F := F)
    hcro hcall hpc hrun hsp hlr hpre_eq ⟨hφ, hcro⟩ hP hpan_false hexit_false hnext hoom_false

theorem call_raw_oom_steps_m2_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) :=
    Arm64.Satisfies.mono (sepConj_mono_left hpre) hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpanm, hpost⟩ |
    ⟨code, _, hpost⟩ | ⟨_, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm (lscro_of_steps_m2_placed hsteps hcro) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hpost' : sm.mem ⊨ ((⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left (hpan sm)) hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpanm,
      (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ F, hpost',
      allowPanic_oom_of_prefix htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

theorem call_lscro_oom_steps_m2_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    {P P_spec F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P_spec ⊢ spec.pre x s)
    (hP : P = P_spec ∗ F)
    (hpan : ∀ sf, spec.onPanic x s sf ⊢ ⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0))
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  refine call_raw_oom_steps_m2_placed (spec := StoreKit.withLsCodeRoLoaded lsmpl spec) (x := x)
    (P_spec := P_spec) (F := F)
    hcro htr hcall hpc hrun hsp hlr
    (by
      dsimp only [StoreKit.withLsCodeRoLoaded]
      rw [sepConj_comm (spec.pre x s)]
      exact Entails.pure_right hcro hpre)
    hP hpan hnext hexit_false hoom_false

/-! ## Shared error-return record teardown (`(blkPl_518).base + 0x3588 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- Drops `sessionStateAt A (coroPtr + 0xf8#64) recG recSt` and `prevSessionsEmptyAt A coroPtr g`
across `(blkPl_518).base + 0x3588 → s0.readReg64 .x30` for arbitrary `g : RecordGhost`,
writing the 48-byte `Result::Err` payload `(errTag, w_22, w_370..w_390)` into `outPtr`. -/
theorem closure_err_drop_record_tail_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (sp coroPtr outPtr errTag w_370 w_378 w_380 w_388 : BitVec 64)
    (w_22 w_390 : BitVec 32) (b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_lt : dropSessionStructureLocal2Stack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x3588#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = w_22.zeroExtend 64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
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
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hdss_le : dropSessionStructureLocal2Stack ≤ 2 ^ 64 :=
    Nat.le_trans hsp_lt (Nat.le_of_lt sp.isLt)
  refine P3P4.SepWPp.weaken_frame (prevSessionsEmptyAt_unpack A coroPtr g) (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨hprev_lt, _⟩ => ?_
  obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := sessionStateAt_split_localIk_cap A (coroPtr + 0xf8#64) recG recSt
  refine P3P4.SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun hcap_lt => ?_
  have hcap_ne : recG.localIk.cap ≠ 0xffffffffffffffff#64 := by bv_omega
  have hto_call := p2_err_drop_ss_to_call_placed_wp ext s coroPtr recG.localIk.cap
    hcap_ne hpc hrun hsp_align hx19
  refine bind_sepWP_lscro_steps_m2_placed hcro hto_call (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx19_1, hx22_1, hx25_1, hx26_1, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine P3P4.SepWPp.weaken_frame hss_bwd (by sep_focus) ?_
  refine call_lscro_nopanic_m2_placed
    (spec := dropSessionStructureLocal2Spec A)
    (x := ⟨coroPtr + 0xf8#64, recG, recSt⟩)
    (T := sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗ A.pool ∗
      stackAt sp dropSessionStructureLocal2Stack)
    hcro1 (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hdrop_ss)
    hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [dropSessionStructureLocal2Spec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
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
  refine P3P4.SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  by_cases hcap : g.prevCap = 0#64
  · simp only [hcap, ↓reduceIte, emp_sepConj]
    have htail := p2_err_tail_prev_zero_placed_wp ext s2 coroPtr outPtr errTag g.prevPtr
      w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine ret_sepWP_lscro_steps_m2_placed hcro2 htail (by sep_focus)
      fun sf _ _ _ hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine ⟨?_, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hcrof⟩
    refine Entails.trans (entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr 0#64 g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (eq_of_sep_emp (by sep_focus))
  · simp only [hcap, ↓reduceIte]
    have htail := p2_err_tail_prev_dealloc_placed_wp ext hdealloc s2 coroPtr outPtr errTag
      g.prevCap g.prevPtr w_370 w_378 w_380 w_388 u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
      (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
      (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
      w_22 w_390 u_ret08 u_ret2c b_2c0 hcap hprev_lt
      hpc2 hrun2 hsp2_align hx19_2 hx22_2 hx25_2 hx26_2 hx28_2
    rw [hsp2] at htail
    refine ret_sepWP_lscro_steps_m2_placed hcro2 htail (by sep_focus)
      fun sf _ _ _ hcrof hregsf => ?_
    rcases hregsf with ⟨hspf, htrf, hvregsf, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
      hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
    refine ⟨?_, hspf, htrf.trans (htr2_1.trans htr1_s),
      ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, True.intro⟩,
      hvregsf.trans hvregs2_s,
      hcrof⟩
    refine Entails.trans (entails_replace_sub (coro_e0_3w_344_entails_368 coroPtr g.prevCap g.prevPtr 0#64)
      (by sep_focus) rfl) ?_
    exact entails_replace_sub (sp370_4w64_w32_entails_36 sp w_370 w_378 w_380 w_388 w_390)
      (by sep_focus) (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
end
