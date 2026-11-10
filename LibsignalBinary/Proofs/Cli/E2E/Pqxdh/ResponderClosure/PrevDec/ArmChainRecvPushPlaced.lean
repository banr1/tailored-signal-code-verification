/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPush
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DecInterfacePlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable Tag-7 (`receiver_chains`) Push Segment (`+0x2310 → +0x2160`)

Relocatable (`[LibsignalPlacement]`) verification of Segment B of the tag-7 (`receiver_chains`)
decode arm on Block `518` (`lsProg_518`), pushing the decoded `Chain` onto `receiver_chains` and
calling `RawVec<Chain>::grow_one` (Block `43`) when at capacity.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.CodeLayout
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ ExtraGQ GenFieldQ prostSSGQAt)
open CryptoVerification.CliHandshake.RespClosurePlaced
open Proofs.libsignal

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] State.readReg32
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem allowPanic_oom_of_trace_eq_pl {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    unfold allocFailedIn at ha ⊢
    rw [← htr]
    exact ⟨ha, hp⟩
  exact allowPanic_frame himp hm

private theorem SepWPp_weaken_frame_pl {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

private theorem SepWPp_bind_sepWP_frame_pl {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem libsignalCodeLoaded_preserve_pl {mpl : Obj.MultiPlacement} {prog : Program} {s sm : State}
    (hcl : LibsignalCodeLoaded mpl s.mem) (hsteps : Steps prog s sm) :
    LibsignalCodeLoaded mpl sm.mem :=
  fun i hi hmut X O svc => hsteps.codeLoaded (hcl i hi hmut X O svc)

private theorem SepWPp_bind_sepWP_frame_lscl_pl [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun (libsignalCodeLoaded_preserve_pl hcl hsteps)
      hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem SepWPp_call_frame_plain_oom_pl {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
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
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_eq_pl htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

private theorem SepWPp_call_frame_lscl_oom_pl [LibsignalPlacement]
    {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T) ∗ ⌜LibsignalCodeLoaded lsmpl s.mem⌝)
    (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcl, hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (libsignalCodeLoaded_preserve_pl hcl hsteps)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_eq_pl htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

private theorem stackAt_sub_eq_pl (sp : BitVec 64) (M N : Nat) (hMN : N ≤ M := by decide)
    (hbound : M < 2 ^ 64 := by decide) :
    stackAt sp M = stackAt sp N ∗ memRegion (sp - BitVec.ofNat 64 M) (M - N) := by
  have h1 : M = N + (M - N) := (Nat.add_sub_of_le hMN).symm
  have h2 := ProofLib.stackAt_split_bottom sp N (M - N) (by omega)
  rw [← h1] at h2
  rw [h2, sepConj_comm]

set_option maxHeartbeats 400000 in
private theorem step_2114_to_2160_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (ptr' len w_len : BitVec 64)
    (q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 : BitVec 128) (w6 dw6 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x2114#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx22 : s.readReg64 .x22 = len)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 0x2160#64) s
      (((g.q + 0x980#64) ↦₆₄ ptr') ∗
       ((g.q + 0x988#64) ↦₆₄ w_len) ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
       RawByteMove.chunks104_6QWAt (ptr' + len * 104#64) d0 d1 d2 d3 d4 d5 dw6)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x980#64) ↦₆₄ ptr') ∗
          ((g.q + 0x988#64) ↦₆₄ (len + 1#64)) ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
          RawByteMove.chunks104_6QWAt (ptr' + len * 104#64) q0 q1 q2 q3 q4 q5 w6) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = len := hx22
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  conv =>
    arg 4
    rw [chunks104_6QWAt_read_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
        chunks104_6QWAt_write_eq_rc (ptr' + len * 104#64) d0 d1 d2 d3 d4 d5 dw6]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm, isCalleeSavedVReg]⟩
  rw [chunks104_6QWAt_read_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_eq_rc (ptr' + len * 104#64) q0 q1 q2 q3 q4 q5 w6]

set_option maxHeartbeats 400000 in
private theorem step_2310_to_2114_of_ne_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (cap len : BitVec 64)
    (q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 : BitVec 128) (w6 dw6 : BitVec 64)
    (hne : len ≠ cap)
    (hpc : s.pc = (blkPl_518).base + 0x2310#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 0x2114#64) s
      (((g.q + 0x978#64) ↦₆₄ cap) ∗
       ((g.q + 0x988#64) ↦₆₄ len) ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) d0 d1 d2 d3 d4 d5 dw6)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x978#64) ↦₆₄ cap) ∗
          ((g.q + 0x988#64) ↦₆₄ len) ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x22 = len ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx0_32 : s.readReg32 (Reg.gpr 0#5) = 0#32 := by simp only [State.readReg32, hx0']; rfl
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  conv =>
    arg 4
    rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
        chunks104_6QWAt_write_a90_eq_rc g.q d0 d1 d2 d3 d4 d5 dw6]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm, isCalleeSavedVReg]⟩
  rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6]

set_option maxHeartbeats 400000 in
private theorem step_2310_to_growOne_of_eq_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (cap : BitVec 64)
    (q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 : BitVec 128) (w6 dw6 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x2310#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 43) s
      (((g.q + 0x978#64) ↦₆₄ cap) ∗
       ((g.q + 0x988#64) ↦₆₄ cap) ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
       RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) d0 d1 d2 d3 d4 d5 dw6)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x978#64) ↦₆₄ cap) ∗
          ((g.q + 0x988#64) ↦₆₄ cap) ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
          RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = g.q + 0x978#64 ∧
        s1.readReg64 Reg.lr = (blkPl_518).base + 0x234c#64 ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x22 = cap ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx0_32 : s.readReg32 (Reg.gpr 0#5) = 0#32 := by simp only [State.readReg32, hx0']; rfl
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  conv =>
    arg 4
    rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
        chunks104_6QWAt_write_a90_eq_rc g.q d0 d1 d2 d3 d4 d5 dw6]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm, isCalleeSavedVReg]⟩
  rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6]

set_option maxHeartbeats 400000 in
private theorem step_234c_to_2114_placed [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (len : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x234c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx22 : s.readReg64 .x22 = len)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 0x2114#64) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x22 = len ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = len := hx22
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨Entails.refl _, hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-! ## Shared Tail (`+0x2114 → +0x2160`) and Top-Level `OverDecRecvSegBPlacedStmt` -/

private def recv2114HeapPlaced (A : RustAlloc) (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ)
    (cap' ptr' : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) (H_c : SepProp) :
    SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    ((g.q + 0x978#64) ↦₆₄ cap') ∗
    ((g.q + 0x980#64) ↦₆₄ ptr') ∗
    ((g.q + 0x988#64) ↦₆₄ BitVec.ofNat 64 v.base.recv.length) ∗
    A.live ptr' (cap'.toNat * 104) 8 ∗
    arrayAt (fun c' a => prostChainGAt A a c') 104 ptr' v.base.recv ∗
    memRegion (ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64) 104 ∗
    memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
      ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
    prostSSGQRest A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
    H_c ∗
    memRegion (g.q + 0xaf8#64) 240 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool

set_option maxHeartbeats 400000 in
private theorem step_from_2114_to_2160_full_pl [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (cap' ptr' : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) (H_c : SepProp)
    (hlt : v.base.recv.length < cap'.toNat)
    (hcap_lt : cap'.toNat * 104 < 2 ^ 63)
    (hptr : ptr' ≠ 0#64)
    (hmov_c : ∀ b : BitVec 64,
      (RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H_c) ⊢ prostChainGAt A b c)
    (hregs : OverDecRegsPlaced ext s0 g 0x2114#64 s)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 v.base.recv.length) :
    SepWPp (lsProg_518 ext)
        ((blkPl_518).base + 0x2160#64) s
      (recv2114HeapPlaced A g rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply (.base (.recv c)))))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  set dst : BitVec 64 := ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64
  let F_2114 : SepProp :=
    overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    ((g.q + 0x978#64) ↦₆₄ cap') ∗
    A.live ptr' (cap'.toNat * 104) 8 ∗
    arrayAt (fun c' a => prostChainGAt A a c') 104 ptr' v.base.recv ∗
    memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
      ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
    prostSSGQRest A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    H_c ∗
    memRegion (g.q + 0xaf8#64) 240 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool
  have hsplit : recv2114HeapPlaced A g rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c =
      (∃∗ d0 : BitVec 128, ∃∗ d1 : BitVec 128, ∃∗ d2 : BitVec 128,
       ∃∗ d3 : BitVec 128, ∃∗ d4 : BitVec 128, ∃∗ d5 : BitVec 128,
       ∃∗ dw6 : BitVec 64,
        ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ BitVec.ofNat 64 v.base.recv.length) ∗
        RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        RawByteMove.chunks104_6QWAt dst d0 d1 d2 d3 d4 d5 dw6) ∗ F_2114 := by
    unfold recv2114HeapPlaced F_2114
    rw [show ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64 = dst from rfl,
        memRegion104_eq_exists_chunks104_6QWAt_rc dst]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply congrArg sepExists; funext _)
    ac_rfl
  rw [hsplit]
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  have hstep := step_2114_to_2160_placed ext s g ptr'
    (BitVec.ofNat 64 v.base.recv.length) (BitVec.ofNat 64 v.base.recv.length)
    q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
    hpc hrun hsp hal hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29
  refine SepWPp_bind_sepWP_frame_pl hstep rfl
    fun sf hpcf hrunf hCLf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hCLf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  have hc_dst := hmov_c dst
  have hss := prostSSGQAt_fold_apply_recv_ext A g.q cap' ptr' v c hlt hcap_lt hptr
  have ha90 := memRegion344_a90_join_rc g.q q0 q1 q2 q3 q4 q5 w6
  let F_keep : SepProp :=
    overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool
  have h1 :
      (((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        RawByteMove.chunks104_6QWAt dst q0 q1 q2 q3 q4 q5 w6) ∗ F_2114 ⊢
      (((g.q + 0x978#64) ↦₆₄ cap') ∗ ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A a c') 104 ptr' v.base.recv ∗
        prostChainGAt A dst c ∗
        memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
        prostSSGQRest A (g.q + 0x930#64) v) ∗
      (RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        memRegion (g.q + 0xaf8#64) 240) ∗
      F_keep := by
    refine Entails.trans (Q := (RawByteMove.chunks104_6QWAt dst q0 q1 q2 q3 q4 q5 w6 ∗ H_c) ∗
      (((g.q + 0x978#64) ↦₆₄ cap') ∗ ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A a c') 104 ptr' v.base.recv ∗
        memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
        prostSSGQRest A (g.q + 0x930#64) v ∗
        (RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
          memRegion (g.q + 0xaf8#64) 240) ∗
        F_keep))
      (Entails.of_eq (by unfold F_2114 F_keep; ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hc_dst) (Entails.of_eq (by ac_rfl))
  refine Entails.trans h1 ?_
  refine Entails.trans (sepConj_mono hss (sepConj_mono ha90 (Entails.refl F_keep))) ?_
  exact Entails.of_eq (by unfold overDecHeapExt F_keep; ac_rfl)

private abbrev toPrevDecG (g : VerNe.Chain3.OverDecG) : OverDecG :=
  ⟨g.q, g.r19, g.r20, g.r26, g.prevCap, g.prevPtr, g.encCap, g.encPtr, g.enc, g.sv⟩

private theorem step_from_2114_to_2160_full_lscl_pl [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State))
    (s0 s : State) (g : VerNe.Chain3.OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (cap' ptr' : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) (H_c : SepProp)
    (hlt : v.base.recv.length < cap'.toNat)
    (hcap_lt : cap'.toNat * 104 < 2 ^ 63)
    (hptr : ptr' ≠ 0#64)
    (hmov_c : ∀ b : BitVec 64,
      (RawByteMove.chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H_c) ⊢ prostChainGAt A b c)
    (hregs : VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2114#64 s)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 v.base.recv.length) :
    SepWPp (lsProg_518 (Rust.withPanics ext))
        ((blkPl_518).base + 0x2160#64) s
      (recv2114HeapPlaced A (toPrevDecG g) rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c)
      (fun sf P_f => VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ VerNe.Chain3.overDecHeapExt A g rest (v.apply (.base (.recv c)))))
      (PanicOomProp s0) := by
  intro R hm hL
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hregs_pl : OverDecRegsPlaced (Rust.withPanics ext) s0 (toPrevDecG g) 0x2114#64 s :=
    ⟨hpc, hrun, hsp, hal, htr, hL, hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  obtain ⟨sf, hsteps, ⟨hpc', hrun', P_f, hmf, hregsf, hentf⟩ | hpan⟩ :=
    step_from_2114_to_2160_full_pl A (Rust.withPanics ext) s0 s (toPrevDecG g) v c rest
      cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c hlt hcap_lt hptr hmov_c hregs_pl hx22 R hm hL
  · rcases hregsf with ⟨hpc_f, hrun_f, hsp_f, hal_f, htr_f, _hLf,
      hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
    exact ⟨sf, hsteps, Or.inl ⟨hpc', hrun', P_f, hmf,
      ⟨⟨hpc_f, hrun_f, hsp_f, hal_f, htr_f, libsignalCodeLoaded_preserve_pl hcl hsteps,
        hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩,
       hentf⟩⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

set_option maxHeartbeats 400000 in
/-- Segment B (`(blkPl_518).base + 0x2310 → +0x2160`) of the tag-7 (`receiver_chains`) arm, parameterized by the `grow_one` contract at `lsmpl.base 43`. -/
theorem overDecRecv_segB_placed_of_grow [LibsignalPlacement]
    (hGrow : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 43) (Stage1X.growOneChainSpecX A0)) :
    OverDecRecvSegBPlacedStmt := by
  intro ext s0 s g v c rest _hOk hFresh _hsuf _hlen hregs hx0
  have hfresh : v.base.recv.length < maxReceiverChains := hFresh.2
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  unfold overDecRecvPostMergeHeapPlaced
  rw [prostSSGQAt_eq_recv_sep_rest A0 (g.q + 0x930#64) v,
      memRegion344_a90_split_rc g.q]
  refine SepWPp_weaken_frame_pl (vecAt_recv_open_q_ext A0 g.q v.base.recv)
    (by sep_focus) ?_
  apply SepWPp_exists_left_rc; intro cap
  apply SepWPp_exists_left_rc; intro ptr
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨hlen_le, hcap_lt, hptr⟩
  refine SepWPp_weaken_frame_pl (prostChainGAt_move_chunks104_rc A0 (g.q + 0xbf0#64) c)
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i q0 q1 q2 q3 q4 q5 w6 H_c
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; intro hmov_c
  refine SepWPp_weaken_frame_pl
    (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_rc (g.q + 0xa90#64)))
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  by_cases hfull : v.base.recv.length = cap.toNat
  · refine SepWPp_weaken_frame_pl (vecBuf_recv_full_open_rc_ext A0 cap ptr v.base.recv hfull)
      (by sep_focus) ?_
    apply SepWPp_exists_left_rc; intro bs
    apply SepWPp_exists_left_rc; intro H_arr
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hbs_len, hmov_arr⟩
    have hlen_cap : BitVec.ofNat 64 v.base.recv.length = cap := ofNat_length_eq_cap_of_eq_rc hfull
    have hmax_lt : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by
      have h5 : maxReceiverChains = 5 := rfl
      omega
    rw [hlen_cap]
    have hstep1 := step_2310_to_growOne_of_eq_placed ext s g cap
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_pl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 _hCLs1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx0s1, hlrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : s1.spAligned = true := by
      simp only [State.spAligned]
      rwa [hsps1, ← hsp]
    rw [stackAt_sub_eq_pl g.q overDecStackX Stage1X.growOneChainStackX]
    refine SepWPp_weaken_frame_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_call_frame_plain_oom_pl
      (x := (g.q + 0x978#64, cap, ptr, bs))
      (htrs1.trans htr) (hGrow ext) hpcs1 hruns1 hals1 hlrs1
      (growOne_plain_pre_eq_q g.q cap ptr bs s1 hsps1)
      ⟨hbs_len, hx0s1, hptr, hmax_lt⟩
      (by sep_focus)
      (by intro sf; rfl)
      (by intro _ _; rfl)
      ?_
    intro sm hpcm hrunm hspm halm hcsm _hCLm
    obtain ⟨hx19m, hx20m, hx21m, hx22m, _, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    rw [hx19s1] at hx19m; rw [hx20s1] at hx20m; rw [hx21s1] at hx21m; rw [hx22s1] at hx22m
    rw [hx24s1] at hx24m; rw [hx25s1] at hx25m; rw [hx26s1] at hx26m; rw [hx27s1] at hx27m
    rw [hx28s1] at hx28m; rw [hx29s1] at hfpm; rw [hsps1] at hspm
    refine SepWPp_weaken_frame_pl
      (growOne_plain_post_elim_sp_q g.q cap ptr v.base.recv bs s1 sm hsps1 hfull hfresh hbs_len)
      rfl ?_
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro htrm
    have htrm' : sm.trace = s0.trace := htrm.trans (htrs1.trans htr)
    apply SepWPp_exists_left_rc; intro cap'
    apply SepWPp_exists_left_rc; intro p'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    refine SepWPp_weaken_frame_pl (hmov_arr p') (by sep_focus) ?_
    have hstep2 := step_234c_to_2114_placed ext sm g cap
      hpcm hrunm hspm hx19m hx20m hx21m hx22m hx24m hx25m hx26m hx27m hx28m hfpm
    refine SepWPp_bind_sepWP_frame_pl hstep2 (emp_sepConj _).symm
      fun s2 hpcs2 hruns2 hCLs2 hpost2 => ?_
    rcases hpost2 with ⟨hsps2, htrs2, hx19s2, hx20s2, hx21s2, hx22s2,
      hx24s2, hx25s2, hx26s2, hx27s2, hx28s2, hx29s2, hvregss2⟩
    have hals2 : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsps2, ← hsp]
    rw [← hlen_cap] at hx22s2 ⊢
    have hregs2 : OverDecRegsPlaced ext s0 g 0x2114#64 s2 :=
      ⟨hpcs2, hruns2, hsps2, hals2, htrs2.trans htrm', hCLs2,
       hx19s2, hx20s2, hx26s2, hx21s2, hx24s2, hx25s2, hx27s2, hx28s2, hx29s2,
       ((hvregss2.trans hvregsm).trans hvregss1).trans hvregs⟩
    refine SepWPp_weaken_frame_pl
      (P₂ := recv2114HeapPlaced A0 g rest v cap' p' q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq ?_) (sepConj_emp _).symm ?_
    · unfold recv2114HeapPlaced overPrevElemRest
      rw [stackAt_sub_eq_pl g.q overDecStackX Stage1X.growOneChainStackX]
      simp only [emp_sepConj]
      ac_rfl
    · rw [sepConj_emp]
      exact step_from_2114_to_2160_full_pl A0 ext s0 s2 g v c rest cap' p' q0 q1 q2 q3 q4 q5 w6 H_c
        hlt_cap' hcap_lt' hp' hmov_c hregs2 hx22s2
  · have hlt : v.base.recv.length < cap.toNat := by omega
    have hne : BitVec.ofNat 64 v.base.recv.length ≠ cap := len_ne_cap_of_lt_rc hlt
    rw [vecBuf_recv_not_full_open_rc_ext A0 cap ptr v.base.recv hlt hcap_lt]
    have hstep1 := step_2310_to_2114_of_ne_placed ext s g cap (BitVec.ofNat 64 v.base.recv.length)
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hne hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_pl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hCLs1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsps1, ← hsp]
    have hregs1 : OverDecRegsPlaced ext s0 g 0x2114#64 s1 :=
      ⟨hpcs1, hruns1, hsps1, hals1, htrs1.trans htr, hCLs1,
       hx19s1, hx20s1, hx26s1, hx21s1, hx24s1, hx25s1, hx27s1, hx28s1, hx29s1,
       hvregss1.trans hvregs⟩
    refine SepWPp_weaken_frame_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_weaken_frame_pl
      (P₂ := recv2114HeapPlaced A0 g rest v cap ptr q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq (by unfold recv2114HeapPlaced overPrevElemRest; ac_rfl))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact step_from_2114_to_2160_full_pl A0 ext s0 s1 g v c rest cap ptr q0 q1 q2 q3 q4 q5 w6 H_c
      hlt hcap_lt hptr hmov_c hregs1 hx22s1

/-- `LibsignalCodeLoaded`-backed Segment B (`(blkPl_518).base + 0x2310 → +0x2160`) of the tag-7 (`receiver_chains`) arm on `lsProg_518 (Rust.withPanics ext)` under `Stage1X.AllocContractsPlaced`. -/
def OverDecRecvSegBLsclPlacedStmtExt [LibsignalPlacement] (A : RustAlloc) : Prop :=
  ∀ (ext : String → Option (State → State)),
    Stage1X.AllocContractsPlaced A (Rust.withPanics ext) →
    ∀ (s0 s : State) (g : VerNe.Chain3.OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8)),
    (GenFieldQ.base (.recv c)).Ok →
    (GenFieldQ.base (.recv c)).Fresh v →
    ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc →
    g.enc.length < 2 ^ 62 →
    VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2310#64 s →
    s.readReg64 .x0 = 0#64 →
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x2160#64) s
      (overDecRecvPostMergeHeapExt A g rest v c)
      (fun sf P_f => VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ VerNe.Chain3.overDecHeapExt A g rest (v.apply (.base (.recv c)))))
      (PanicOomProp s0)

abbrev OverDecRecvSegBLsclPlacedStmt [LibsignalPlacement] : Prop :=
  OverDecRecvSegBLsclPlacedStmtExt A0

set_option maxHeartbeats 400000 in
theorem overDecRecv_segB_lscl_ok_ext [LibsignalPlacement] {A : RustAlloc} :
    OverDecRecvSegBLsclPlacedStmtExt A := by
  intro ext hAlloc s0 s g v c rest _hOk hFresh _hsuf _hlen hregs hx0
  have hfresh : v.base.recv.length < maxReceiverChains := hFresh.2
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  unfold overDecRecvPostMergeHeapExt
  rw [prostSSGQAt_eq_recv_sep_rest A (g.q + 0x930#64) v,
      memRegion344_a90_split_rc g.q]
  refine SepWPp_weaken_frame_pl (vecAt_recv_open_q_ext A g.q v.base.recv)
    (by sep_focus) ?_
  apply SepWPp_exists_left_rc; intro cap
  apply SepWPp_exists_left_rc; intro ptr
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨hlen_le, hcap_lt, hptr⟩
  refine SepWPp_weaken_frame_pl (prostChainGAt_move_chunks104_rc A (g.q + 0xbf0#64) c)
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i q0 q1 q2 q3 q4 q5 w6 H_c
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; intro hmov_c
  refine SepWPp_weaken_frame_pl
    (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_rc (g.q + 0xa90#64)))
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  by_cases hfull : v.base.recv.length = cap.toNat
  · refine SepWPp_weaken_frame_pl (vecBuf_recv_full_open_rc_ext A cap ptr v.base.recv hfull)
      (by sep_focus) ?_
    apply SepWPp_exists_left_rc; intro bs
    apply SepWPp_exists_left_rc; intro H_arr
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hbs_len, hmov_arr⟩
    have hlen_cap : BitVec.ofNat 64 v.base.recv.length = cap := ofNat_length_eq_cap_of_eq_rc hfull
    have hmax_lt : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by
      have h5 : maxReceiverChains = 5 := rfl
      omega
    rw [hlen_cap]
    have hstep1 := step_2310_to_growOne_of_eq_placed (Rust.withPanics ext) s (toPrevDecG g) cap
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_lscl_pl hcl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hcls1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx0s1, hlrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    dsimp only [toPrevDecG] at hsps1 hx0s1 hx19s1 hx20s1 hx21s1 hx26s1 hx27s1 hx28s1 hx29s1
    have hals1 : s1.spAligned = true := by
      simp only [State.spAligned]
      rwa [hsps1, ← hsp]
    have hG : subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 43)
        (withLsCl lsmpl (Stage1X.growOneChainSpecX A)) :=
      Stage1X.growOneChain_placed_ok_cl (Stage1X.growOneChain_placed_ok_x hAlloc)
    rw [stackAt_sub_eq_pl g.q overDecStackX Stage1X.growOneChainStackX]
    refine SepWPp_weaken_frame_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_call_frame_lscl_oom_pl
      (x := (g.q + 0x978#64, cap, ptr, bs))
      hcls1 (htrs1.trans htr) hG hpcs1 hruns1 hals1 hlrs1
      (growOne_lscl_pre_eq_q_ext A g.q cap ptr bs s1 hsps1)
      ⟨hbs_len, hx0s1, hptr, hmax_lt⟩
      (by sep_focus)
      (by intro sf; rfl)
      (by intro _ _; rfl)
      ?_
    intro sm hpcm hrunm hspm halm hcsm hclm
    obtain ⟨hx19m, hx20m, hx21m, hx22m, _, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    rw [hx19s1] at hx19m; rw [hx20s1] at hx20m; rw [hx21s1] at hx21m; rw [hx22s1] at hx22m
    rw [hx24s1] at hx24m; rw [hx25s1] at hx25m; rw [hx26s1] at hx26m; rw [hx27s1] at hx27m
    rw [hx28s1] at hx28m; rw [hx29s1] at hfpm; rw [hsps1] at hspm
    refine SepWPp_weaken_frame_pl
      (growOne_lscl_post_elim_sp_q_ext A g.q cap ptr v.base.recv bs s1 sm hsps1 hfull hfresh hbs_len)
      rfl ?_
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro _hclm'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro htrm
    have htrm' : sm.trace = s0.trace := htrm.trans (htrs1.trans htr)
    apply SepWPp_exists_left_rc; intro cap'
    apply SepWPp_exists_left_rc; intro p'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    refine SepWPp_weaken_frame_pl (hmov_arr p') (by sep_focus) ?_
    have hstep2 := step_234c_to_2114_placed (Rust.withPanics ext) sm (toPrevDecG g) cap
      hpcm hrunm hspm hx19m hx20m hx21m hx22m hx24m hx25m hx26m hx27m hx28m hfpm
    refine SepWPp_bind_sepWP_frame_lscl_pl hclm hstep2 (emp_sepConj _).symm
      fun s2 hpcs2 hruns2 hcls2 hpost2 => ?_
    rcases hpost2 with ⟨hsps2, htrs2, hx19s2, hx20s2, hx21s2, hx22s2,
      hx24s2, hx25s2, hx26s2, hx27s2, hx28s2, hx29s2, hvregss2⟩
    dsimp only [toPrevDecG] at hsps2 hx19s2 hx20s2 hx21s2 hx26s2 hx27s2 hx28s2 hx29s2
    have hals2 : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsps2, ← hsp]
    rw [← hlen_cap] at hx22s2 ⊢
    have hregs2 : VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2114#64 s2 :=
      ⟨hpcs2, hruns2, hsps2, hals2, htrs2.trans htrm', hcls2,
       hx19s2, hx20s2, hx26s2, hx21s2, hx24s2, hx25s2, hx27s2, hx28s2, hx29s2,
       ((hvregss2.trans hvregsm).trans hvregss1).trans hvregs⟩
    refine SepWPp_weaken_frame_pl
      (P₂ := recv2114HeapPlaced A (toPrevDecG g) rest v cap' p' q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq ?_) (sepConj_emp _).symm ?_
    · dsimp only [recv2114HeapPlaced, toPrevDecG, overPrevElemRestExt,
        VerNe.Chain3.overPrevElemRestExt, overDecStackX, VerNe.Chain3.overDecStackX]
      rw [stackAt_sub_eq_pl g.q 65536 Stage1X.growOneChainStackX]
      simp only [emp_sepConj]
      ac_rfl
    · rw [sepConj_emp]
      exact step_from_2114_to_2160_full_lscl_pl A ext s0 s2 g v c rest cap' p' q0 q1 q2 q3 q4 q5 w6 H_c
        hlt_cap' hcap_lt' hp' hmov_c hregs2 hx22s2
  · have hlt : v.base.recv.length < cap.toNat := by omega
    have hne : BitVec.ofNat 64 v.base.recv.length ≠ cap := len_ne_cap_of_lt_rc hlt
    rw [vecBuf_recv_not_full_open_rc_ext A cap ptr v.base.recv hlt hcap_lt]
    have hstep1 := step_2310_to_2114_of_ne_placed (Rust.withPanics ext) s (toPrevDecG g) cap
      (BitVec.ofNat 64 v.base.recv.length)
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hne hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_lscl_pl hcl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hcls1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    dsimp only [toPrevDecG] at hsps1 hx19s1 hx20s1 hx21s1 hx26s1 hx27s1 hx28s1 hx29s1
    have hals1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsps1, ← hsp]
    have hregs1 : VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2114#64 s1 :=
      ⟨hpcs1, hruns1, hsps1, hals1, htrs1.trans htr, hcls1,
       hx19s1, hx20s1, hx26s1, hx21s1, hx24s1, hx25s1, hx27s1, hx28s1, hx29s1,
       hvregss1.trans hvregs⟩
    refine SepWPp_weaken_frame_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_weaken_frame_pl
      (P₂ := recv2114HeapPlaced A (toPrevDecG g) rest v cap ptr q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq (by dsimp only [recv2114HeapPlaced, toPrevDecG, overPrevElemRestExt, VerNe.Chain3.overPrevElemRestExt, overDecStackX, VerNe.Chain3.overDecStackX]; ac_rfl))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact step_from_2114_to_2160_full_lscl_pl A ext s0 s1 g v c rest cap ptr q0 q1 q2 q3 q4 q5 w6 H_c
      hlt hcap_lt hptr hmov_c hregs1 hx22s1

theorem overDecRecv_segB_lscl_ok [LibsignalPlacement] : OverDecRecvSegBLsclPlacedStmt :=
  overDecRecv_segB_lscl_ok_ext

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
