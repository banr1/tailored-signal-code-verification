/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecv
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChainPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Placed Tag 7 (`receiver_chains`) Decode Arm (`+0x22e0 → +0x2160`)

Proves `[LibsignalPlacement]` tag-7 (`receiver_chains`) decode-arm specifications on `lsProg_518 ext`
from Segment B and `message::merge<Chain>` at `lsmpl.base 516`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ ExtraGQ GenFieldQ prostSSGQAt)
open CryptoVerification.CodeLayout
open CryptoVerification.CliHandshake.RespClosurePlaced
open Proofs.libsignal

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem allowPanic_oom_of_trace_eq_recv_pl {s0 s sf : State} {F : SepProp}
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

private theorem libsignalCodeLoaded_preserve_recv_pl {mpl : Obj.MultiPlacement} {prog : Program}
    {s sm : State} (hcl : LibsignalCodeLoaded mpl s.mem) (hsteps : Steps prog s sm) :
    LibsignalCodeLoaded mpl sm.mem :=
  fun i hi hmut X O svc => hsteps.codeLoaded (hcl i hi hmut X O svc)

private theorem SepWPp_weaken_frame_recv_pl {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

private theorem SepWPp_bind_sepWP_frame_recv_pl {prog : Program} {mid ret : BitVec 64} {s : State}
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

private theorem SepWPp_bind_sepWP_frame_lscl_recv_pl [LibsignalPlacement]
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
    hnext sm hpc hrun (libsignalCodeLoaded_preserve_recv_pl hcl hsteps)
      hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem SepWPp_call_frame_plain_oom_recv_pl {α : Type} {prog : Program}
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
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_eq_recv_pl htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

private theorem SepWPp_call_frame_lscl_oom_recv_pl [LibsignalPlacement]
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
        (libsignalCodeLoaded_preserve_recv_pl hcl hsteps)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_eq_recv_pl htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

set_option maxHeartbeats 400000 in
theorem overDecRecv_pre_step_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 s : State} {g : VerNe.Chain3.OverDecG} (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x22e0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hsaved : OverDecSavedRegs g s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 516) s
      (((g.q + 0xbf0#64) ↦₆₄ u0) ∗
        ((g.q + 0xbf8#64) ↦₆₄ u1) ∗ ((g.q + 0xc00#64) ↦₆₄ u2) ∗ ((g.q + 0xc08#64) ↦₆₄ u3) ∗
        ((g.q + 0xc10#64) ↦₆₄ u4) ∗ ((g.q + 0xc18#64) ↦₆₄ u5) ∗ ((g.q + 0xc20#64) ↦₆₄ u6) ∗
        ((g.q + 0xc28#64) ↦₆₄ u7) ∗ ((g.q + 0xc30#64) ↦₆₄ u8) ∗ ((g.q + 0xc38#64) ↦₆₄ u9))
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbf0#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc00#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc08#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc10#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc18#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc20#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc28#64) ↦₆₄ 8#64) ∗ ((g.q + 0xc30#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc38#64) ↦₆₄ noneCap)) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 0x2310#64 ∧
        OverDecSavedRegs g s1) := by
  rcases hsaved with ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have h24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := h24
  have h25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := h25
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  have hnoneCap : noneCap = 0xffffffffffffffff#64 := rfl
  rw [hnoneCap]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl),
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem overDecRecv_pre_step_80_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 s : State} {g : VerNe.Chain3.OverDecG}
    (hpc : s.pc = (blkPl_518).base + 0x22e0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hsaved : OverDecSavedRegs g s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 516) s
      (memRegion (g.q + 0xbf0#64) 80)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbf0#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc00#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc08#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc10#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc18#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc20#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc28#64) ↦₆₄ 8#64) ∗ ((g.q + 0xc30#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc38#64) ↦₆₄ noneCap)) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 0x2310#64 ∧
        OverDecSavedRegs g s1) := by
  rw [memRegion80_bf0_eq_cells10 g.q]
  refine SepWP.exists_elim fun u9 => SepWP.exists_elim fun u8 =>
    SepWP.exists_elim fun u7 => SepWP.exists_elim fun u6 =>
    SepWP.exists_elim fun u5 => SepWP.exists_elim fun u4 =>
    SepWP.exists_elim fun u3 => SepWP.exists_elim fun u2 =>
    SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  exact overDecRecv_pre_step_placed u0 u1 u2 u3 u4 u5 u6 u7 u8 u9
    hpc hrun hsp _hsp_align htr hsaved hx0

private abbrev toChain3G (g : OverDecG) : VerNe.Chain3.OverDecG :=
  ⟨g.q, g.r19, g.r20, g.r26, g.prevCap, g.prevPtr, g.encCap, g.encPtr, g.enc, g.sv⟩

set_option maxHeartbeats 400000 in
/-- Placed tag 7 (`receiver_chains`) decode arm (`OverDecArmPlacedStmtTR OverDecRecvField`) from
`OverDecRecvSegBPlacedStmt` and `chainMerge3RawSpecW`. -/
theorem overDecArm_recv_placed [LibsignalPlacement]
    (hsegB : OverDecRecvSegBPlacedStmt)
    (hChain5 : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 516) VerNe.Chain3.chainMerge3RawSpecW) :
    OverDecArmPlacedStmtTR OverDecRecvField := by
  intro ext s0 s g v fl rest hfl hok hfresh hsuf hlen hregs hx0 _hx22
  have hfl_eq : ∃ c : ChainG, fl = .base (.recv c) := by
    cases fl with
    | base bf =>
      cases bf <;> try contradiction
      exact ⟨_, rfl⟩
    | _ => contradiction
  rcases hfl_eq with ⟨c, rfl⟩
  have hpay_eq : (GenFieldQ.base (.recv c)).payload = c.payload := rfl
  have hc_ok : c.Ok := hok.1
  have hsuf_pay : (c.payload ++ rest) <:+ g.enc := by
    rw [← hpay_eq]; exact suffix_payload_of_suffix_enc_recv hsuf
  have hlen_pay : (c.payload ++ rest).length < 2 ^ 62 :=
    payload_append_length_lt62_of_suffix hsuf_pay hlen
  change OverDecRegsPlaced ext s0 g 0x22e0#64 s at hregs
  change s.readReg64 .x0 = 2#64 at hx0
  have hheap_eq : overDecHeap g (c.payload ++ rest) v =
      VerNe.Chain3.overDecHeap (toChain3G g) (c.payload ++ rest) v := rfl
  rw [hpay_eq, hheap_eq, overDecHeap_eq_recv_split (toChain3G g) v hsuf_pay]
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hCL, hsaved⟩
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  have hstep := overDecRecv_pre_step_80_placed (ext := ext) (g := toChain3G g)
    hpc hrun hsp hsp_align htr hsaved hx0
  refine SepWPp_bind_sepWP_frame_recv_pl hstep rfl
    fun s1 hpc1 hrun1 _hCL1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1, hsaved1⟩ => ?_
  dsimp only [toChain3G] at hsp1 hx1_1 hx2_1
  rw [← sepConj_assoc]
  refine SepWPp_weaken_frame_recv_pl (default_cells_bf0_entail_chain3GAt g.q) rfl ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length)
  have hx0_1_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by simp [hx0_1]
  refine SepWPp_call_frame_plain_oom_recv_pl
    (x := (⟨g.q + 0xbf0#64, c, g.q + 0xbe8#64, g.q + 0x920#64, curPtr, rest⟩ :
      ChainMergeGenGhost))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62)
    (T := VerNe.Chain3.chain3GAt A0 (g.q + 0xbf0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) curPtr (c.payload ++ rest) ∗
      stackAt g.q VerNe.Chain3.chainMerge3StackX)
    (F := overDecRecvFrameRest (toChain3G g) v (c.payload ++ rest).length)
    htr1 (hChain5 ext) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [VerNe.Chain3.chainMerge3RawSpecW]; rw [hsp1])
    ⟨hx0_1_w8, hx1_1, hx2_1, hc_ok, hlen_pay⟩
    (by dsimp only [curPtr, toChain3G]; ac_rfl)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hCL2 => ?_)
  dsimp only [VerNe.Chain3.chainMerge3RawSpecW]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hx0_2⟩ => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  have hsaved2 : OverDecSavedRegs (toChain3G g) s2 := overDecSavedRegs_of_calleeSaved hsaved1 hcs2
  dsimp only [OverDecSavedRegs, toChain3G] at hsaved2
  have hregs2 : OverDecRegsPlaced ext s0 g 0x2310#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hsp2_align, htr2, hCL2, hsaved2⟩
  have hpost_eq :
      prostChainGAt A0 (g.q + 0xbf0#64) c ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAfter (g.q + 0x920#64) curPtr (c.payload ++ rest) rest ∗
        stackAt g.q VerNe.Chain3.chainMerge3StackX ∗
        overDecRecvFrameRest (toChain3G g) v (c.payload ++ rest).length =
      overDecRecvPostMergeHeapPlaced g rest v c := by
    dsimp only [curPtr]
    exact overDecRecvPostMergeHeap_eq_unsplit (toChain3G g) v hsuf_pay
  rw [hpost_eq]
  exact hsegB ext s0 s2 g v c rest hok hfresh hsuf hlen hregs2 hx0_2

/-- `LibsignalCodeLoaded` Segment B contract (`+0x2310 → +0x2160`) on
`lsProg_518 (Rust.withPanics ext)`. -/
def OverDecRecvSegBChain3PlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State)),
    ∀ (s0 s : State) (g : VerNe.Chain3.OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8)),
    (GenFieldQ.base (.recv c)).Ok →
    (GenFieldQ.base (.recv c)).Fresh v →
    ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc →
    g.enc.length < 2 ^ 62 →
    VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2310#64 s →
    s.readReg64 .x0 = 0#64 →
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x2160#64) s
      (overDecRecvPostMergeHeap g rest v c)
      (fun sf P_f => VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ VerNe.Chain3.overDecHeap g rest (v.apply (.base (.recv c)))))
      (PanicOomProp s0)

set_option maxHeartbeats 400000 in
/-- `LibsignalCodeLoaded` tag 7 (`receiver_chains`) decode arm from
`OverDecRecvSegBChain3PlacedStmt` and `Chain5PlacedOkAtW`. -/
theorem overDecArm_recv_lscl [LibsignalPlacement]
    (hsegB : OverDecRecvSegBChain3PlacedStmt)
    (hChain5 : ∀ ext, VerNe.Chain3.Chain5PlacedOkAtW ext) :
    VerNe.Chain3.OverDecArmPlacedStmtTR VerNe.Chain3.OverDecRecvField := by
  intro ext s0 s g v fl rest hfl hok hfresh hsuf hlen hregs hx0 _hx22
  have hfl_eq : ∃ c : ChainG, fl = .base (.recv c) := by
    cases fl with
    | base bf =>
      cases bf <;> try contradiction
      exact ⟨_, rfl⟩
    | _ => contradiction
  rcases hfl_eq with ⟨c, rfl⟩
  have hpay_eq : (GenFieldQ.base (.recv c)).payload = c.payload := rfl
  have hc_ok : c.Ok := hok.1
  have hsuf_pay : (c.payload ++ rest) <:+ g.enc := by
    rw [← hpay_eq]; exact suffix_payload_of_suffix_enc_recv hsuf
  have hlen_pay : (c.payload ++ rest).length < 2 ^ 62 :=
    payload_append_length_lt62_of_suffix hsuf_pay hlen
  change VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x22e0#64 s at hregs
  change s.readReg64 .x0 = 2#64 at hx0
  rw [hpay_eq, overDecHeap_eq_recv_split g v hsuf_pay]
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, hcl, hsaved⟩
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  have hstep := overDecRecv_pre_step_80_placed (ext := Rust.withPanics ext)
    hpc hrun hsp hsp_align htr hsaved hx0
  refine SepWPp_bind_sepWP_frame_lscl_recv_pl hcl hstep rfl
    fun s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1, hsaved1⟩ => ?_
  rw [← sepConj_assoc]
  refine SepWPp_weaken_frame_recv_pl (default_cells_bf0_entail_chain3GAt g.q) rfl ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length)
  have hx0_1_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by simp [hx0_1]
  have hcall := VerNe.Chain3.chainMerge5_placed_on_518 (hChain5 ext)
  refine SepWPp_call_frame_lscl_oom_recv_pl
    (x := (⟨g.q + 0xbf0#64, c, g.q + 0xbe8#64, g.q + 0x920#64, curPtr, rest⟩ :
      ChainMergeGenGhost))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62)
    (T := VerNe.Chain3.chain3GAt A0 (g.q + 0xbf0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) curPtr (c.payload ++ rest) ∗
      stackAt g.q VerNe.Chain3.chainMerge3StackX)
    (F := overDecRecvFrameRest g v (c.payload ++ rest).length)
    hcl1 htr1 hcall hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [VerNe.Chain3.chainMerge5PlacedSpecW, VerNe.Chain3.chainMerge3PlacedSpecW,
          withLsCl, VerNe.Chain3.chainMerge3RawSpecW]; rw [hsp1])
    ⟨hx0_1_w8, hx1_1, hx2_1, hc_ok, hlen_pay⟩
    (by dsimp only [curPtr]; ac_rfl)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hcl2 => ?_)
  dsimp only [VerNe.Chain3.chainMerge5PlacedSpecW, VerNe.Chain3.chainMerge3PlacedSpecW,
    withLsCl, VerNe.Chain3.chainMerge3RawSpecW]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun _hcl2' => ?_
  refine SepWPp.pure_elim fun ⟨htr2_1, hx0_2⟩ => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  have hsaved2 : OverDecSavedRegs g s2 := overDecSavedRegs_of_calleeSaved hsaved1 hcs2
  have hregs2 : VerNe.Chain3.OverDecRegsPlaced ext s0 g 0x2310#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hsp2_align, htr2, hcl2, hsaved2⟩
  have hpost_eq :
      prostChainGAt A0 (g.q + 0xbf0#64) c ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAfter (g.q + 0x920#64) curPtr (c.payload ++ rest) rest ∗
        stackAt g.q VerNe.Chain3.chainMerge3StackX ∗
        overDecRecvFrameRest g v (c.payload ++ rest).length =
      overDecRecvPostMergeHeap g rest v c := by
    dsimp only [curPtr]
    exact overDecRecvPostMergeHeap_eq_unsplit g v hsuf_pay
  rw [hpost_eq]
  exact hsegB ext s0 s2 g v c rest hok hfresh hsuf hlen hregs2 hx0_2

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
