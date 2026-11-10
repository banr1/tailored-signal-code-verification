/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvOk
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChainPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Kit.DecodeVarint5Placed
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Tag 6 (`sender_chain`) and Tag 7 (`receiver_chains`) Decode Arms

Proves `[LibsignalPlacement]` decode-arm specifications on `lsProg_518 ext` for tag 6
(`overDecArmSender_placed_of_chain5`, `overDecArmSender_lscl_of_kit`) and tag 7
(`overDecArmRecv_placed_of_callees`, `overDecArmRecv_lscl_of_kit`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ ExtraGQ GenFieldQ prostSSGQAt)
open CryptoVerification.CodeLayout
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Tag 6 (`sender_chain`) on `lsProg_518 ext` -/

set_option maxHeartbeats 400000 in
private theorem overDecChain_segA_plain_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (q : BitVec 64) (u1 u2 u3 u4 u5 u6 u7 u8 u9 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 8724#64)
    (hrun : s.status = .Running) (hsp : s.sp = q) (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 2#64) (hx21 : s.readReg64 .x21 = q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64) (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx29 : s.readReg64 .x29 = q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 516) s
      (((q + 0x9c0#64) ↦₆₄ noneCap) ∗
        ((q + 0x9c8#64) ↦₆₄ u1) ∗ ((q + 0x9d0#64) ↦₆₄ u2) ∗ ((q + 0x9d8#64) ↦₆₄ u3) ∗
        ((q + 0x9e0#64) ↦₆₄ u4) ∗ ((q + 0x9e8#64) ↦₆₄ u5) ∗ ((q + 0x9f0#64) ↦₆₄ u6) ∗
        ((q + 0x9f8#64) ↦₆₄ u7) ∗ ((q + 0xa00#64) ↦₆₄ u8) ∗ ((q + 0xa08#64) ↦₆₄ u9))
      (fun s1 P_f =>
        (P_f ⊢
          ((q + 0x9c0#64) ↦₆₄ 0#64) ∗
          ((q + 0x9c8#64) ↦₆₄ 1#64) ∗ ((q + 0x9d0#64) ↦₆₄ 0#64) ∗ ((q + 0x9d8#64) ↦₆₄ 0#64) ∗
          ((q + 0x9e0#64) ↦₆₄ 1#64) ∗ ((q + 0x9e8#64) ↦₆₄ 0#64) ∗ ((q + 0x9f0#64) ↦₆₄ 0#64) ∗
          ((q + 0x9f8#64) ↦₆₄ 8#64) ∗ ((q + 0xa00#64) ↦₆₄ 0#64) ∗
          ((q + 0xa08#64) ↦₆₄ noneCap)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = q + 0x9c0#64 ∧
        s1.readReg64 .x2 = q + 0xbe8#64 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 8784#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  subst hsp
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx29' : s.readReg64 (Reg.gpr 29#5) = s.sp + 0xc70#64 := hx29
  have hnoneCap : noneCap = 0xffffffffffffffff#64 := rfl
  rw [hnoneCap]
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨?_,
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [hx0', arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [hx21', arm64_norm], by simp only [hx24', arm64_norm],
    by simp only [hx25', arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [hx29', arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm]⟩
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 400000 in
private theorem overDecChain_segB_plain_placed [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (q r19 r20 r26 prevPtr : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 8784#64)
    (hrun : s.status = .Running) (hsp : s.sp = q)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = r19) (hx20 : s.readReg64 .x20 = r20)
    (hx21 : s.readReg64 .x21 = q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64) (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = r26) (hx27 : s.readReg64 .x27 = prevPtr)
    (hx28 : s.readReg64 .x28 = q + 0xa90#64) (hx29 : s.readReg64 .x29 = q + 0xc70#64) :
    SepWP (lsProg_518 ext)
      ((blkPl_518).base + 8544#64) s emp
      (fun sf P_f =>
        (P_f ⊢ emp) ∧ sf.sp = q ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = r19 ∧ sf.readReg64 .x20 = r20 ∧
        sf.readReg64 .x21 = q + 0x930#64 ∧ sf.readReg64 .x24 = 1#64 ∧
        sf.readReg64 .x25 = 0xffffffffffffffff#64 ∧ sf.readReg64 .x26 = r26 ∧
        sf.readReg64 .x27 = prevPtr ∧ sf.readReg64 .x28 = q + 0xa90#64 ∧
        sf.readReg64 .x29 = q + 0xc70#64 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
  refine ⟨Entails.refl _, hsp, rfl,
    by simp only [hx19', arm64_norm], by simp only [hx20', arm64_norm],
    by simp only [hx21', arm64_norm], by simp only [hx24', arm64_norm],
    by simp only [hx25', arm64_norm], by simp only [hx26', arm64_norm],
    by simp only [hx27', arm64_norm], by simp only [hx28', arm64_norm],
    by simp only [hx29', arm64_norm], by simp only [arm64_norm]⟩

private theorem SepWPp_bind_sepWP_frame_sender_pl {prog : Program} {mid ret : BitVec 64} {s : State}
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

private theorem SepWPp_ret_sepWP_frame_sender_pl {prog : Program} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hpost : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      prog.CodeLoaded sf.mem → Q_regs sf → Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_step', hmf, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, .inl ⟨hpc, hrun, P_step_post ∗ F, ?_,
    hpost sf hpc hrun (hsteps.codeLoaded hL) hregs⟩⟩
  rw [sepConj_assoc]
  exact Satisfies.mono (sepConj_mono_left hent) hmf

private theorem SepWPp_weaken_frame_sender_pl {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

private theorem allowPanic_oom_of_trace_eq_sender_pl {s0 s sf : State} {F : SepProp}
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

private theorem SepWPp_call_frame_plain_oom_sender_pl {α : Type} {prog : Program}
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
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ |
      ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost,
      allowPanic_oom_of_trace_eq_sender_pl htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

private abbrev toChain3G (g : OverDecG) : VerNe.Chain3.OverDecG :=
  ⟨g.q, g.r19, g.r20, g.r26, g.prevCap, g.prevPtr, g.encCap, g.encPtr, g.enc, g.sv⟩

set_option maxHeartbeats 400000 in
/-- Tag 6 (`sender_chain`, `+0x2214 → +0x2160`) on `lsProg_518 ext` from `message::merge<Chain>`. -/
theorem overDecArmSender_plain_core [LibsignalPlacement] (ext : String → Option (State → State))
    (hC5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 516) VerNe.Chain3.chainMerge3RawSpecW)
    (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hcok : c.Ok) (hnone : v.base.sender = none)
    (hsuf : ((GenFieldQ.base (.sender c)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegsPlaced ext s0 g 0x2214#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (overDecHeap g ((GenFieldQ.base (.sender c)).payload ++ rest) v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest ⟨v.base.apply (.sender c), v.ext⟩))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  obtain ⟨pfx, hpfx, hpay_len⟩ := VerNe.Chain3.overDecChain_payload_suffix hsuf hlen
  have hheap_eq : overDecHeap g ((GenFieldQ.base (.sender c)).payload ++ rest) v =
      VerNe.Chain3.overDecHeap (toChain3G g)
        ((GenFieldQ.base (.sender c)).payload ++ rest) v := rfl
  rw [hheap_eq, VerNe.Chain3.overDecChain_heap_pre (toChain3G g) v pfx _ rest hpfx hnone,
    VerNe.Chain3.overDecChain_mem96 g.q]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun u9 => SepWPp.exists_elim fun u8 => SepWPp.exists_elim fun u7 =>
    SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 => ?_
  have hstepA := overDecChain_segA_plain_placed ext s g.q u1 u2 u3 u4 u5 u6 u7 u8 u9
    hpc hrun hsp hal hx0 hx21 hx24 hx25 hx29
  refine SepWPp_bind_sepWP_frame_sender_pl hstepA (by sep_focus)
    fun s1 hpc1 hrun1 _hcl1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  refine SepWPp_weaken_frame_sender_pl (VerNe.Chain3.overDecChain_bridge g.q)
    (by sep_focus) ?_
  have hsp1q : s1.sp = g.q := hsp1.trans hsp
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, hal]
  have hx0_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by rw [hx0_1]; rfl
  refine SepWPp_call_frame_plain_oom_sender_pl
    (x := (⟨g.q + 0x9c0#64, c, g.q + 0xbe8#64, g.q + 0x920#64,
      g.encPtr + BitVec.ofNat 64 pfx.length, rest⟩ : ChainMergeGenGhost))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0x9c0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62)
    (T := VerNe.Chain3.chain3GAt A0 (g.q + 0x9c0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
        (c.payload ++ rest) ∗
      stackAt g.q VerNe.Chain3.chainMerge3StackX)
    (htr1.trans htr) hC5 hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [VerNe.Chain3.chainMerge3RawSpecW]; rw [hsp1q])
    ⟨hx0_w8, hx1_1, hx2_1, hcok, hpay_len⟩
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 _hcl2 => ?_)
  dsimp only [VerNe.Chain3.chainMerge3RawSpecW]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hx0_2⟩ => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1q
  have htr2 : s2.trace = s0.trace := htr2_1.trans (htr1.trans htr)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs, hvregs_cs⟩
  have hstepB := overDecChain_segB_plain_placed ext s2 g.q g.r19 g.r20 g.r26 g.prevPtr
    hpc2 hrun2 hsp2 hx0_2
    ((hx19_cs.trans hx19_1).trans hx19) ((hx20_cs.trans hx20_1).trans hx20)
    ((hx21_cs.trans hx21_1).trans hx21) ((hx24_cs.trans hx24_1).trans hx24)
    ((hx25_cs.trans hx25_1).trans hx25) ((hx26_cs.trans hx26_1).trans hx26)
    ((hx27_cs.trans hx27_1).trans hx27) ((hx28_cs.trans hx28_1).trans hx28)
    ((hx29_cs.trans hx29_1).trans hx29)
  refine SepWPp_ret_sepWP_frame_sender_pl hstepB (by rw [emp_sepConj])
    fun sf hpcf hrunf hclf hregsf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f,
    hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr2, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f,
    ((hvregs_f.trans hvregs_cs).trans hvregs_1).trans hvregs⟩, ?_⟩
  have hpost_eq : overDecHeap g rest ⟨v.base.apply (.sender c), v.ext⟩ =
      VerNe.Chain3.overDecHeap (toChain3G g) rest ⟨v.base.apply (.sender c), v.ext⟩ := rfl
  rw [hpost_eq, ← VerNe.Chain3.overDecChain_heap_post (toChain3G g) v c pfx _ rest hpfx,
    hsp1q, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

/-- Placed tag 6 (`sender_chain`) decode arm (`OverDecArmPlacedStmtTR OverDecSenderField`)
parameterized by `message::merge<Chain>` at `lsmpl.base 516`. -/
theorem overDecArmSender_placed_of_chain5 [LibsignalPlacement]
    (hChain5 : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
      VerNe.Chain3.chainMerge3RawSpecW) :
    OverDecArmPlacedStmtTR OverDecSenderField := by
  intro ext s0 s g v fl rest hP hok hfresh hsuf hlen hregs hx0 _hx22
  cases fl
  case base f =>
    cases f
    case sender c =>
      have hok' : c.Ok ∧ c.priv.length = 32 ∧ c.ck.isSome = true ∧ c.keys = [] := hok
      have hfresh' : v.ext = ExtraGQ.empty ∧ v.base.sender = none := hfresh
      have hregs' : OverDecRegsPlaced ext s0 g 0x2214#64 s := hregs
      have hx0' : s.readReg64 .x0 = 2#64 := hx0
      exact overDecArmSender_plain_core ext (hChain5 ext) s0 s g v c rest
        hok'.1 hfresh'.2 hsuf hlen hregs' hx0'
    all_goals exact False.elim hP
  all_goals exact False.elim hP

/-- Placed tag 7 (`receiver_chains`) decode arm (`OverDecArmPlacedStmtTR OverDecRecvField`)
parameterized by `RawVec<Chain>::grow_one` (`lsmpl.base 43`) and `message::merge<Chain>` (`lsmpl.base 516`). -/
theorem overDecArmRecv_placed_of_callees [LibsignalPlacement]
    (hGrow : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (Proofs.libsignal.Stage1X.growOneChainSpecX A0))
    (hChain5 : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
      VerNe.Chain3.chainMerge3RawSpecW) :
    OverDecArmPlacedStmtTR OverDecRecvField :=
  overDecArm_recv_placed (overDecRecv_segB_placed_of_grow hGrow) hChain5

/-! ## `LibsignalCodeLoaded` Callee Kits and Tag 6 / Tag 7 Arms -/

private theorem spqr_decodeVarint2SpecX_eq_chain3 (A : RustAlloc) :
    SpqrH.decodeVarint2SpecX A = VerNe.Chain3.decodeVarint2SpecX A := by
  unfold SpqrH.decodeVarint2SpecX VerNe.Chain3.decodeVarint2SpecX
  congr 1

theorem chain3CalleesPlacedW_of_alloc_bm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hAlloc : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 (Rust.withPanics ext))
    (hBm : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 514)
      (VerNe.Chain3.bytesMerge3PlacedSpec A0)) :
    VerNe.Chain3.Chain3CalleesPlacedW ext where
  dv := by
    have h := decodeVarint5_placed_ok_cl
      (callerProg := lsProg_516 (Rust.withPanics ext)) hAlloc
    rwa [spqr_decodeVarint2SpecX_eq_chain3] at h
  bm := hBm
  grow := Proofs.libsignal.Stage1X.growOneChain_placed_ok_cl
    (callerProg := lsProg_516 (Rust.withPanics ext))
    (Proofs.libsignal.Stage1X.growOneChain_placed_ok_x hAlloc)

theorem chainMerge5_placed_ok_of_alloc_bm [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hAlloc : Proofs.libsignal.Stage1X.AllocContractsPlaced A0 (Rust.withPanics ext))
    (hBm : subroutine_ok (lsProg_516 (Rust.withPanics ext)) (lsmpl.base 514)
      (VerNe.Chain3.bytesMerge3PlacedSpec A0)) :
    VerNe.Chain3.Chain5PlacedOkAtW ext :=
  VerNe.Chain3.chain3_placed_ok_of_callees ext (chain3CalleesPlacedW_of_alloc_bm hAlloc hBm)

/-- `LibsignalCodeLoaded` tag 6 (`sender_chain`) decode arm from `Chain3CalleePlacedKit`. -/
theorem overDecArmSender_lscl_of_kit [LibsignalPlacement]
    (kit : VerNe.Chain3.Chain3CalleePlacedKit) :
    VerNe.Chain3.OverDecArmPlacedStmtTR VerNe.Chain3.OverDecSenderField :=
  VerNe.Chain3.overDecArmSender_cli_placed_of_kit kit

/-- `LibsignalCodeLoaded` tag 7 (`receiver_chains`) decode arm from `Chain3CalleePlacedKit`. -/
theorem overDecArmRecv_lscl_of_kit [LibsignalPlacement]
    (kit : VerNe.Chain3.Chain3CalleePlacedKit)
    (hAlloc : ∀ ext, Proofs.libsignal.Stage1X.AllocContractsPlaced A0 (Rust.withPanics ext)) :
    VerNe.Chain3.OverDecArmPlacedStmtTR VerNe.Chain3.OverDecRecvField :=
  overDecArm_recv_lscl (fun ext => overDecRecv_segB_lscl_ok ext (hAlloc ext))
    (VerNe.Chain3.chainMerge5_placed_ok kit)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
