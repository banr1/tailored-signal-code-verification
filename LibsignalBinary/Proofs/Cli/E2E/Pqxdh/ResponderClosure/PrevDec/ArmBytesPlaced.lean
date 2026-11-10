/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytes
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsCroPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeWDefsPlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommon
import ProofLib.SepLogic.WPp

/-!
# Placed Bytes Arms (Tags 2, 3, 4, 13, 15) of Inlined `SessionStructure::decode`

Proves `[LibsignalPlacement]` decode-arm specifications on `lsProg_518 ext` for tags 2, 3, 4, 13,
and 15 (`+0x22cc`, `+0x22b8`, `+0x2290`, `+0x21d4`, `+0x2200 → +0x2160`), invoking
`bytes::merge [local#5]` at `lsmpl.base 514`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection CryptoVerification.CodeLayout SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeGeneral (GenField SSG)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem allowPanic_oom_of_trace_eq_bytes_pl {s0 s sf : State} {F : SepProp}
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

private theorem SepWPp_weaken_frame_bytes_pl {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (hnext : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have hm' : s.mem ⊨ (P₂ ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hm
  exact hnext R hm' hL

private theorem SepWPp_ret_sepWP_frame_bytes_pl {prog : Program} {ret : BitVec 64} {s : State}
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

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_22d8_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8920#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 8544#64) s emp (OverDecCbzPost s g) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  exact ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx19, arm64_norm, wp_norm], by simp only [hx20, arm64_norm, wp_norm],
    by simp only [hx21, arm64_norm, wp_norm], by simp only [hx24, arm64_norm, wp_norm],
    by simp only [hx25, arm64_norm, wp_norm], by simp only [hx26, arm64_norm, wp_norm],
    by simp only [hx27, arm64_norm, wp_norm], by simp only [hx28, arm64_norm, wp_norm],
    by simp only [hx29, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_22c4_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8900#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 8544#64) s emp (OverDecCbzPost s g) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  exact ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx19, arm64_norm, wp_norm], by simp only [hx20, arm64_norm, wp_norm],
    by simp only [hx21, arm64_norm, wp_norm], by simp only [hx24, arm64_norm, wp_norm],
    by simp only [hx25, arm64_norm, wp_norm], by simp only [hx26, arm64_norm, wp_norm],
    by simp only [hx27, arm64_norm, wp_norm], by simp only [hx28, arm64_norm, wp_norm],
    by simp only [hx29, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_229c_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8860#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 8544#64) s emp (OverDecCbzPost s g) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  exact ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx19, arm64_norm, wp_norm], by simp only [hx20, arm64_norm, wp_norm],
    by simp only [hx21, arm64_norm, wp_norm], by simp only [hx24, arm64_norm, wp_norm],
    by simp only [hx25, arm64_norm, wp_norm], by simp only [hx26, arm64_norm, wp_norm],
    by simp only [hx27, arm64_norm, wp_norm], by simp only [hx28, arm64_norm, wp_norm],
    by simp only [hx29, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_21e0_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8672#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 8544#64) s emp (OverDecCbzPost s g) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  exact ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx19, arm64_norm, wp_norm], by simp only [hx20, arm64_norm, wp_norm],
    by simp only [hx21, arm64_norm, wp_norm], by simp only [hx24, arm64_norm, wp_norm],
    by simp only [hx25, arm64_norm, wp_norm], by simp only [hx26, arm64_norm, wp_norm],
    by simp only [hx27, arm64_norm, wp_norm], by simp only [hx28, arm64_norm, wp_norm],
    by simp only [hx29, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
private theorem overDec_cbz_220c_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8716#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 8544#64) s emp (OverDecCbzPost s g) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  exact ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx19, arm64_norm, wp_norm], by simp only [hx20, arm64_norm, wp_norm],
    by simp only [hx21, arm64_norm, wp_norm], by simp only [hx24, arm64_norm, wp_norm],
    by simp only [hx25, arm64_norm, wp_norm], by simp only [hx26, arm64_norm, wp_norm],
    by simp only [hx27, arm64_norm, wp_norm], by simp only [hx28, arm64_norm, wp_norm],
    by simp only [hx29, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

theorem overDec_cbz_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (retOff : BitVec 64) (s : State) (g : OverDecG)
    (hret : retOff = 0x22d8#64 ∨ retOff = 0x22c4#64 ∨ retOff = 0x229c#64 ∨
            retOff = 0x21e0#64 ∨ retOff = 0x220c#64)
    (hpc : s.pc = (blkPl_518).base + retOff)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 0#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 8544#64) s emp (OverDecCbzPost s g) := by
  rcases hret with rfl | rfl | rfl | rfl | rfl
  · exact overDec_cbz_22d8_placed_wp ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  · exact overDec_cbz_22c4_placed_wp ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  · exact overDec_cbz_229c_placed_wp ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  · exact overDec_cbz_21e0_placed_wp ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  · exact overDec_cbz_220c_placed_wp ext s g hpc hrun hsp hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29

/-! ## Tag 2 (`local_identity_public`, `+0x22cc → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag2_pre_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State)) (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8908#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = g.q ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0x930#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧ s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧ s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 8920#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx0', arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [hx19', arm64_norm, wp_norm], by simp only [hx20', arm64_norm, wp_norm],
    by simp only [hx21', arm64_norm, wp_norm], by simp only [hx24', arm64_norm, wp_norm],
    by simp only [hx25', arm64_norm, wp_norm], by simp only [hx26', arm64_norm, wp_norm],
    by simp only [hx27', arm64_norm, wp_norm], by simp only [hx28', arm64_norm, wp_norm],
    by simp only [hx29', arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

/-! ## Tag 3 (`remote_identity_public`, `+0x22b8 → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag3_pre_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State)) (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8888#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = g.q ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0x930#64 + 0x18#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧ s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧ s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 8900#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx0', arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [hx19', arm64_norm, wp_norm], by simp only [hx20', arm64_norm, wp_norm],
    by simp only [hx21', arm64_norm, wp_norm], by simp only [hx24', arm64_norm, wp_norm],
    by simp only [hx25', arm64_norm, wp_norm], by simp only [hx26', arm64_norm, wp_norm],
    by simp only [hx27', arm64_norm, wp_norm], by simp only [hx28', arm64_norm, wp_norm],
    by simp only [hx29', arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

/-! ## Tag 4 (`root_key`, `+0x2290 → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag4_pre_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State)) (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8848#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = g.q ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0x930#64 + 0x30#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧ s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧ s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 8860#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx0', arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [hx19', arm64_norm, wp_norm], by simp only [hx20', arm64_norm, wp_norm],
    by simp only [hx21', arm64_norm, wp_norm], by simp only [hx24', arm64_norm, wp_norm],
    by simp only [hx25', arm64_norm, wp_norm], by simp only [hx26', arm64_norm, wp_norm],
    by simp only [hx27', arm64_norm, wp_norm], by simp only [hx28', arm64_norm, wp_norm],
    by simp only [hx29', arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

/-! ## Tag 13 (`alice_base_key`, `+0x21d4 → +0x2160`) -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag13_pre_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State)) (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8660#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = g.q ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0x930#64 + 0x60#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧ s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧ s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 8672#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx0', arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [hx19', arm64_norm, wp_norm], by simp only [hx20', arm64_norm, wp_norm],
    by simp only [hx21', arm64_norm, wp_norm], by simp only [hx24', arm64_norm, wp_norm],
    by simp only [hx25', arm64_norm, wp_norm], by simp only [hx26', arm64_norm, wp_norm],
    by simp only [hx27', arm64_norm, wp_norm], by simp only [hx28', arm64_norm, wp_norm],
    by simp only [hx29', arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

/-! ## Tag 15 (`pq_ratchet_state`, `+0x2200 → +0x2160`) and Combined Theorems -/

set_option maxHeartbeats 400000 in
private theorem overDec_arm_tag15_pre_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State)) (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 8704#64)
    (hrun : s.status = .Running) (hsp : s.sp = g.q) (hx0 : s.readReg64 .x0 = 2#64)
    (hx19 : s.readReg64 .x19 = g.r19) (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64) (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64) (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr) (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 514) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = g.q ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0x930#64 + 0x78#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .x19 = g.r19 ∧ s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧ s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 8716#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 2#64 := hx0
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.refl _, by simp only [hsp, arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [hx0', arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [hx19', arm64_norm, wp_norm], by simp only [hx20', arm64_norm, wp_norm],
    by simp only [hx21', arm64_norm, wp_norm], by simp only [hx24', arm64_norm, wp_norm],
    by simp only [hx25', arm64_norm, wp_norm], by simp only [hx26', arm64_norm, wp_norm],
    by simp only [hx27', arm64_norm, wp_norm], by simp only [hx28', arm64_norm, wp_norm],
    by simp only [hx29', arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm], by simp only [arm64_norm, wp_norm]⟩

section Cro

open CryptoVerification.LibsignalPublicApi

private theorem SepWPp_bind_sepWP_frame_cro_bytes_pl [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
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
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (hcro.of_keepsFrozen hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem SepWPp_call_frame_bytesMerge3W_cro_pl [LibsignalPlacement]
    {A : RustAlloc} {prog : Program}
    {target ret lrVal : BitVec 64} {s0 s : State} {x : BytesMergeGhost}
    {T P F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hok : subroutine_ok prog target (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A)))
    (hpc : s.pc = target) (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 .x30 = lrVal)
    (hpre_eq : (bytesMerge3RawSpecW A).pre x s =
      ⌜(s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
        s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62⌝ ∗ T)
    (hφ : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 x.wt.toNat ∧
      s.readReg64 .x1 = x.valPtr ∧ s.readReg64 .x2 = x.bufRef ∧ x.bs.length < 2 ^ 62)
    (hP : P = T ∗ F)
    (hnext : ∀ sm : State, sm.pc = lrVal → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      prog.CodeLoaded sm.mem →
      SepWPp prog ret sm ((bytesMerge3RawSpecW A).post x s sm ∗ F) Q (PanicOomProp s0)) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A)).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ (⌜LibsignalCodeRoLoaded _ _⌝), satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hφ, ?_⟩
    rw [hP, sepConj_assoc] at hm
    exact hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hok x (F ∗ R) hpc hrun hm' hsp_al hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp_al
    dsimp only [withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    have hpcm' : sm.pc = lrVal := hpcm.trans hlr
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm' hrunm hspm hsp_alm hcsm hLm R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeRoLoaded, bytesMerge3RawSpecW] at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hpost, allowPanic_oom_of_trace_eq_bytes_pl htr⟩)⟩
  · dsimp only [withLsCodeRoLoaded] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [withLsCodeRoLoaded] at hpost
    exact (not_satisfies_false_sepConj hpost).elim

theorem overDec_bytesMerge6_call_cro_placed_ext [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hBM6W : subroutine_ok (lsProg_518 ext) (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A)))
    (retOff valPtr : BitVec 64)
    (oldBs b rest : List (BitVec 8))
    (restSS : SepProp)
    (s0 s1 : State) (g : OverDecG) (v v' : SSGQ) (fl : GenFieldQ)
    (hcro1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hret : retOff = 0x22d8#64 ∨ retOff = 0x22c4#64 ∨ retOff = 0x229c#64 ∨
            retOff = 0x21e0#64 ∨ retOff = 0x220c#64)
    (hpay : fl.payload = encodeVarint (BitVec.ofNat 64 b.length) ++ b)
    (hb : b.length < 2 ^ 64)
    (hsuf : (fl.enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hsplit : prostSSGQAt A (g.q + 0x930#64) v = vecU8 A valPtr oldBs ∗ restSS)
    (hunsplit : vecU8 A valPtr b ∗ restSS = prostSSGQAt A (g.q + 0x930#64) v')
    (hpc1 : s1.pc = lsmpl.base 514)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = g.q)
    (hal1 : (s1.sp &&& 15#64 == 0#64) = true)
    (htr1 : s1.trace = s0.trace)
    (hx0_1 : s1.readReg64 .x0 = 2#64)
    (hx1_1 : s1.readReg64 .x1 = valPtr)
    (hx2_1 : s1.readReg64 .x2 = g.q + 0xbe8#64)
    (hx19_1 : s1.readReg64 .x19 = g.r19)
    (hx20_1 : s1.readReg64 .x20 = g.r20)
    (hx21_1 : s1.readReg64 .x21 = g.q + 0x930#64)
    (hx24_1 : s1.readReg64 .x24 = 1#64)
    (hx25_1 : s1.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26_1 : s1.readReg64 .x26 = g.r26)
    (hx27_1 : s1.readReg64 .x27 = g.prevPtr)
    (hx28_1 : s1.readReg64 .x28 = g.q + 0xa90#64)
    (hx29_1 : s1.readReg64 .x29 = g.q + 0xc70#64)
    (hx30_1 : s1.readReg64 .x30 = (blkPl_518).base + retOff)
    (hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs g.sv) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s1
      (overDecHeapExt A g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest v'))
      (PanicOomProp s0) := by
  refine sepWPp_lift_cro_regs hcro1 ?_
  obtain ⟨pfx, hpfx, hpay_len⟩ := overDec_payload_suffix_and_len hsuf hlen
  have hmerge : mergeBytes .lengthDelimited (fl.payload ++ rest) = some (b, rest) := by
    rw [hpay]; exact overDec_mergeBytes_eq b rest hb
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned] using hal1
  have hcur_split :
      Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc (fl.payload ++ rest) =
        (g.encPtr ↦ₛ pfx) ∗
          Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
            (fl.payload ++ rest) := by
    conv_lhs => arg 3; rw [hpfx]
    exact sliceCursorAfter_split_sub (g.q + 0x920#64) g.encPtr pfx (fl.payload ++ rest)
  unfold overDecHeapExt
  rw [hcur_split, hsplit, stackAt_overDec_to_bytesMerge3 g.q]
  unfold vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun cap0 => SepWPp.exists_elim fun ptr0 => ?_
  let xbm : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, valPtr, cap0, ptr0, oldBs, g.q + 0xbe8#64, g.q + 0x920#64,
     g.encPtr + BitVec.ofNat 64 pfx.length, fl.payload ++ rest⟩
  have hx0_w8 : (s1.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 xbm.wt.toNat := by rw [hx0_1]; rfl
  have hφ : (s1.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 xbm.wt.toNat ∧
      s1.readReg64 .x1 = xbm.valPtr ∧ s1.readReg64 .x2 = xbm.bufRef ∧ xbm.bs.length < 2 ^ 62 :=
    ⟨hx0_w8, hx1_1, hx2_1, hpay_len⟩
  refine SepWPp_call_frame_bytesMerge3W_cro_pl (x := xbm)
    (T := vecU8At A valPtr cap0 ptr0 oldBs ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      Prost.sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length) (fl.payload ++ rest) ∗
      A.pool ∗ stackAt g.q bytesMerge3Stack)
    hcro1 htr1 hBM6W hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [bytesMerge3RawSpecW]; rw [hsp1])
    hφ
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 _hL2 => ?_)
  dsimp only [bytesMerge3RawSpecW, xbm]
  rw [hmerge]
  dsimp only
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp_weaken_frame_bytes_pl
    (P₁ := ⌜s2.readReg64 .x0 = 0#64⌝) (P₂ := ⌜s2.readReg64 .x0 = 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun hx0_2 => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs,
    hx29_cs, hvregs_cs⟩
  have hstep_cbz := overDec_cbz_placed_wp ext retOff s2 g hret
    hpc2 hrun2 hsp2 hx0_2 (hx19_cs.trans hx19_1) (hx20_cs.trans hx20_1) (hx21_cs.trans hx21_1)
    (hx24_cs.trans hx24_1) (hx25_cs.trans hx25_1) (hx26_cs.trans hx26_1) (hx27_cs.trans hx27_1)
    (hx28_cs.trans hx28_1) (hx29_cs.trans hx29_1)
  refine SepWPp_ret_sepWP_frame_bytes_pl hstep_cbz
    (by rw [emp_sepConj]) fun sf hpcf hrunf hLf hregsf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp1]
  refine ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr2, hLf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f,
    hvregs_f.trans (hvregs_cs.trans hvregs_1)⟩, ?_⟩
  have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64, vecU8At A valPtr cap' ptr' b) =
      vecU8 A valPtr b := rfl
  have hcur_unsplit :
      (g.encPtr ↦ₛ pfx) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
          (fl.payload ++ rest) rest =
      Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest := by
    rw [sliceCursorAfter_unsplit_sub (g.q + 0x920#64) g.encPtr pfx fl.payload rest, ← hpfx]
  refine Entails.of_eq ?_
  rw [emp_sepConj, hvec, ← hcur_unsplit, ← hunsplit]
  ac_rfl

theorem overDecArm_bytes_cro_placed_ext_of_bm6w [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hBM6W : subroutine_ok (lsProg_518 ext) (lsmpl.base 514)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpecW A)))
    (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8))
    (hP : OverDecBytesField fl) (hok : fl.Ok)
    (hsuf : (fl.enc ++ rest) <:+ g.enc) (hlen : g.enc.length < 2 ^ 62)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hregs : OverDecRegsPlaced ext s0 g (overDecArmOff fl) s)
    (hx0 : s.readReg64 .x0 = overDecWt fl) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (overDecHeapExt A g (fl.payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest (v.apply fl)))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  cases fl with
  | base f =>
    cases f with
    | lik b =>
      dsimp only [overDecArmOff] at hpc
      have hx0' : s.readReg64 .x0 = 2#64 := hx0
      refine SepWPp_bind_sepWP_frame_cro_bytes_pl hcro
        (overDec_arm_tag2_pre_placed_wp ext s g hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
        (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
      rw [emp_sepConj]
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
        hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
      exact overDec_bytesMerge6_call_cro_placed_ext ext hBM6W 0x22d8#64 (g.q + 0x930#64)
        v.base.lik b rest (prostSSGQRest2 A (g.q + 0x930#64) v)
        s0 s1 g v (v.apply (.base (.lik b))) (.base (.lik b)) hcro1
        (Or.inl rfl) rfl (by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega) hsuf hlen
        (prostSSGQAt_eq_lik_sep_rest2 A (g.q + 0x930#64) v)
        (prostSSGQAt_eq_lik_sep_rest2 A (g.q + 0x930#64) (v.apply (.base (.lik b)))).symm
        hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
        (hvregs_1.trans hvregs)
    | rik b =>
      dsimp only [overDecArmOff] at hpc
      have hx0' : s.readReg64 .x0 = 2#64 := hx0
      refine SepWPp_bind_sepWP_frame_cro_bytes_pl hcro
        (overDec_arm_tag3_pre_placed_wp ext s g hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
        (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
      rw [emp_sepConj]
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
        hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
      exact overDec_bytesMerge6_call_cro_placed_ext ext hBM6W 0x22c4#64 (g.q + 0x930#64 + 0x18#64)
        v.base.rik b rest (prostSSGQRest3 A (g.q + 0x930#64) v)
        s0 s1 g v (v.apply (.base (.rik b))) (.base (.rik b)) hcro1
        (Or.inr (Or.inl rfl)) rfl (by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega) hsuf hlen
        (prostSSGQAt_eq_rik_sep_rest3 A (g.q + 0x930#64) v)
        (prostSSGQAt_eq_rik_sep_rest3 A (g.q + 0x930#64) (v.apply (.base (.rik b)))).symm
        hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
        (hvregs_1.trans hvregs)
    | root b =>
      dsimp only [overDecArmOff] at hpc
      have hx0' : s.readReg64 .x0 = 2#64 := hx0
      refine SepWPp_bind_sepWP_frame_cro_bytes_pl hcro
        (overDec_arm_tag4_pre_placed_wp ext s g hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
        (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
      rw [emp_sepConj]
      rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
        hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
      exact overDec_bytesMerge6_call_cro_placed_ext ext hBM6W 0x229c#64 (g.q + 0x930#64 + 0x30#64)
        v.base.root b rest (prostSSGQRest4 A (g.q + 0x930#64) v)
        s0 s1 g v (v.apply (.base (.root b))) (.base (.root b)) hcro1
        (Or.inr (Or.inr (Or.inl rfl))) rfl (by dsimp only [GenFieldQ.Ok, GenField.Ok] at hok; omega) hsuf hlen
        (prostSSGQAt_eq_root_sep_rest4 A (g.q + 0x930#64) v)
        (prostSSGQAt_eq_root_sep_rest4 A (g.q + 0x930#64) (v.apply (.base (.root b)))).symm
        hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
        hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
        (hvregs_1.trans hvregs)
    | version _ | prevCounter _ | sender _ | recv _ | pending _ => cases hP
  | abk b =>
    dsimp only [overDecArmOff] at hpc
    have hx0' : s.readReg64 .x0 = 2#64 := hx0
    refine SepWPp_bind_sepWP_frame_cro_bytes_pl hcro
      (overDec_arm_tag13_pre_placed_wp ext s g hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
      (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
    rw [emp_sepConj]
    rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
      hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
    exact overDec_bytesMerge6_call_cro_placed_ext ext hBM6W 0x21e0#64 (g.q + 0x930#64 + 0x60#64)
      v.ext.abk b rest (prostSSGQRest13 A (g.q + 0x930#64) v)
      s0 s1 g v (v.apply (.abk b)) (.abk b) hcro1
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl (by dsimp only [GenFieldQ.Ok] at hok; omega) hsuf hlen
      (prostSSGQAt_eq_abk_sep_rest13 A (g.q + 0x930#64) v)
      (prostSSGQAt_eq_abk_sep_rest13 A (g.q + 0x930#64) (v.apply (.abk b))).symm
      hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
      hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
      (hvregs_1.trans hvregs)
  | pq b =>
    dsimp only [overDecArmOff] at hpc
    have hx0' : s.readReg64 .x0 = 2#64 := hx0
    refine SepWPp_bind_sepWP_frame_cro_bytes_pl hcro
      (overDec_arm_tag15_pre_placed_wp ext s g hpc hrun hsp hx0' hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29)
      (by rw [emp_sepConj]) fun s1 hpc1 hrun1 _hL1 hcro1 hregs1 => ?_
    rw [emp_sepConj]
    rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
      hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
    exact overDec_bytesMerge6_call_cro_placed_ext ext hBM6W 0x220c#64 (g.q + 0x930#64 + 0x78#64)
      v.ext.pq b rest (prostSSGQRest15 A (g.q + 0x930#64) v)
      s0 s1 g v (v.apply (.pq b)) (.pq b) hcro1
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rfl (by dsimp only [GenFieldQ.Ok] at hok; omega) hsuf hlen
      (prostSSGQAt_eq_pq_sep_rest15 A (g.q + 0x930#64) v)
      (prostSSGQAt_eq_pq_sep_rest15 A (g.q + 0x930#64) (v.apply (.pq b))).symm
      hpc1 hrun1 hsp1 (by rwa [hsp1, ← hsp]) (htr1.trans htr)
      hx0_1 hx1_1 hx2_1 hx19_1 hx20_1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hx30_1
      (hvregs_1.trans hvregs)
  | pendingId _ _ | pendingSpk _ _ _ | remReg _ | locReg _ | kyber _ _ => cases hP

end Cro

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
