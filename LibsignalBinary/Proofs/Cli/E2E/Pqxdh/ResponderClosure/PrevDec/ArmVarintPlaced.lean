/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarint
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsCroPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.BytesMerge6Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeatedCommon
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.SepLogic.WPp

/-!
# Relocatable Varint Arms (Tags 1, 5, 10, 11) of Inlined `SessionStructure::decode`

Relocatable (`[LibsignalPlacement]`) verification of the varint field arms (tags 1, 5, 10, 11) of
inlined `SessionStructure::decode` on Block `518` (`lsProg_518 ext`), calling `decode_varint` at
Block `515` (`lsmpl.base 515`).
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
open CryptoVerification.E2E.Record.L1GX (kyberAt)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt ssgqOf genFieldsQ)
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  State.readReg32 truncate_32_setWidth_64 setWidth_32_setWidth_64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  trace_setPC_pre trace_setMem_setPC_pre calleeSavedVRegs_setPC_pre calleeSavedVRegs_setMem_setPC_pre
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem allowPanic_oom_of_trace_eq_varint_pl {s0 s sf : State} {F : SepProp}
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

private theorem SepWPp_bind_sepWP_frame_varint_pl {prog : Program} {mid ret : BitVec 64} {s : State}
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

private theorem SepWPp_ret_sepWP_frame_varint_pl {prog : Program} {ret : BitVec 64} {s : State}
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


private theorem decodeVarint2SpecX_post_encodeVarint_eq (A : RustAlloc)
    (bufRef slot ptr : BitVec 64) (val : BitVec 32) (rest : List (BitVec 8)) (s1 s2 : State) :
    (SpqrH.decodeVarint2SpecX A).post
      ⟨bufRef, slot, ptr, encodeVarint (val.setWidth 64) ++ rest⟩ s1 s2 =
      ⌜s2.readReg64 .x0 = 0#64 ∧ s2.readReg64 .x1 = val.setWidth 64⌝ ∗
      ⌜s2.trace = s1.trace⌝ ∗
      ((bufRef ↦₆₄ slot) ∗
        sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
        A.pool ∗ stackAt s1.sp decodeVarint2StackX) := by
  dsimp only [SpqrH.decodeVarint2SpecX]
  rw [decodeVarint_encodeVarint (val.setWidth 64) rest]
  dsimp only
  ac_rfl

private theorem overDecVarint_call_decodeVarint5_pl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State}
    {bufRef slot ptr : BitVec 64} {val : BitVec 32} {rest : List (BitVec 8)}
    {F : SepProp} {Q : State → SepProp → Prop}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (SpqrH.decodeVarint2SpecX A))
    (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 515) (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hlen : (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63)
    (hnext : ∀ s2 : State, s2.pc = s.readReg64 .lr → s2.status = .Running →
      s2.sp = s.sp → s2.spAligned = true → CalleeSavedPreserved s s2 →
      (lsProg_518 ext).CodeLoaded s2.mem →
      s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = val.setWidth 64 →
      s2.trace = s0.trace →
      SepWPp (lsProg_518 ext) ret s2
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          A.pool ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
        Q (PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ret s
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
      Q (PanicOomProp s0) := by
  intro R hm hL
  let x : DecodeVarintSlowGhost :=
    ⟨bufRef, slot, ptr, encodeVarint (val.setWidth 64) ++ rest⟩
  have hm' : s.mem ⊨ (SpqrH.decodeVarint2SpecX A).pre x s ∗ (F ∗ R) := by
    dsimp only [SpqrH.decodeVarint2SpecX, x]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hDv5 x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [decodeVarint2SpecX_post_encodeVarint_eq] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0m, hx1m⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [← sepConj_assoc] at hpost
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hsteps.codeLoaded hL)
        hx0m hx1m (htrm.trans htr) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ (F ∗ R) at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_eq_varint_pl htr⟩)⟩
  · exact (not_satisfies_false_sepConj hpost).elim

def OverDecSavedRegsPl (g : OverDecG) (s : State) : Prop :=
  s.readReg64 .x19 = g.r19 ∧ s.readReg64 .x20 = g.r20 ∧ s.readReg64 .x26 = g.r26 ∧
  s.readReg64 .x21 = g.q + 0x930#64 ∧ s.readReg64 .x24 = 1#64 ∧
  s.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s.readReg64 .x27 = g.prevPtr ∧
  s.readReg64 .x28 = g.q + 0xa90#64 ∧ s.readReg64 .x29 = g.q + 0xc70#64 ∧
  calleeSavedVRegs s = calleeSavedVRegs g.sv

private theorem overDecSavedRegsPl_of_calleeSaved {g : OverDecG} {s1 s2 : State}
    (hs1 : OverDecSavedRegsPl g s1) (hcs : CalleeSavedPreserved s1 s2) :
    OverDecSavedRegsPl g s2 := by
  rcases hs1 with ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  rcases hcs with ⟨c19, c20, c21, _, _, c24, c25, c26, c27, c28, c29, cv⟩
  exact ⟨c19.trans h19, c20.trans h20, c26.trans h26, c21.trans h21, c24.trans h24,
    c25.trans h25, c27.trans h27, c28.trans h28, c29.trans h29, cv.trans hv⟩


set_option maxHeartbeats 600000 in
theorem overDecArm_varint_of_pre_post_placed_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (SpqrH.decodeVarint2SpecX A))
    {s0 s : State} {g : OverDecG} {v v' : SSGQ} {rest : List (BitVec 8)}
    {armOff retOff spOff : BitVec 64} {oldVal val : BitVec 32}
    {frameRest : SepProp}
    (hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegsPlaced ext s0 g armOff s)
    (hsplit : overDecHeapExt A g (encodeVarint (val.setWidth 64) ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ oldVal) ∗
      frameRest)
    (hunsplit :
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ val) ∗
      frameRest =
      overDecHeapExt A g rest v')
    (hpre_step : SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + retOff ∧
        OverDecSavedRegsPl g s1))
    (hpost_step : ∀ s2 : State,
      s2.pc = (blkPl_518).base + retOff →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 0x2160#64) s2
        ((g.q + spOff) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + spOff) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf)) :
    SepWPp (lsProg_518 ext)
      ((blkPl_518).base + 0x2160#64) s
      (overDecHeapExt A g (encodeVarint (val.setWidth 64) ++ rest) v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest v'))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL, hsaved⟩
  have hlen_pay : (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63 :=
    payload_append_length_lt_of_suffix hsuf_pay hlen
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  rw [hsplit]
  refine SepWPp_bind_sepWP_frame_varint_pl hpre_step
    rfl
    fun s1 hpc1 hrun1 _hL1 ⟨hsp1, htr1, hx0_1, hlr1, hsaved1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length)
  have hframe_eq :
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        (sliceCursorAt (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) ∗
          A.pool ∗
          stackAt g.q decodeVarint2StackX ∗
          ((g.q + spOff) ↦₃₂ oldVal) ∗
          frameRest) =
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool ∗
        stackAt s1.sp decodeVarint2StackX) ∗
        (((g.q + spOff) ↦₃₂ oldVal) ∗ frameRest) := by
    rw [hsp1]
    simp only [sepConj_assoc]
  rw [hframe_eq]
  refine overDecVarint_call_decodeVarint5_pl hDv5 htr1 hpc1 hrun1 hsp1_al hx0_1 hlen_pay
    fun s2 hpc2_lr hrun2 hsp2_1 _hsp2_al hcs2 _hL2 hx0_2 hx1_2 htr2 => ?_
  have hpc2 : s2.pc = (blkPl_518).base + retOff := hpc2_lr.trans hlr1
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have hsaved2 : OverDecSavedRegsPl g s2 := overDecSavedRegsPl_of_calleeSaved hsaved1 hcs2
  rw [hsp1]
  refine SepWPp_ret_sepWP_frame_varint_pl
    (hpost_step s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2 hsaved2)
    (F := ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      frameRest)
    (by dsimp only [curPtr]; ac_rfl)
    fun sf hpcf hrunf hLf ⟨hspf, htrf, hsavedf⟩ => ?_
  have hspf_align : (sf.sp &&& 15#64 == 0#64) = true := by rw [hspf]; exact hq_align
  refine ⟨⟨hpcf, hrunf, hspf, hspf_align, htrf, hLf, hsavedf⟩, ?_⟩
  apply Entails.of_eq
  rw [← hunsplit]
  dsimp only [curPtr]
  ac_rfl


/-! ## Pre-Call and Post-Call `SepWP` Lemmas -/

set_option maxHeartbeats 400000 in
theorem overDecVarint_pre_tag1_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegsPlaced ext s0 g 0x21bc#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 0x21c8#64 ∧
        OverDecSavedRegsPl g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq rfl,
    by simp only [hsp, arm64_norm, wp_norm],
    by simp only [htr, arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
theorem overDecVarint_post_tag1_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 : State} {g : OverDecG} {oldVal val : BitVec 32} :
    ∀ s2 : State,
      s2.pc = (blkPl_518).base + 0x21c8#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 0x2160#64) s2
        ((g.q + 0xa78#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + 0xa78#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp2]),
    by simp only [arm64_norm, wp_norm],
    by simp only [htr2, arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩


set_option maxHeartbeats 400000 in
theorem overDecVarint_pre_tag5_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegsPlaced ext s0 g 0x21e8#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 0x21f4#64 ∧
        OverDecSavedRegsPl g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq rfl,
    by simp only [hsp, arm64_norm, wp_norm],
    by simp only [htr, arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
theorem overDecVarint_post_tag5_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 : State} {g : OverDecG} {oldVal val : BitVec 32} :
    ∀ s2 : State,
      s2.pc = (blkPl_518).base + 0x21f4#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 0x2160#64) s2
        ((g.q + 0xa7c#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + 0xa7c#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp2]),
    by simp only [arm64_norm, wp_norm],
    by simp only [htr2, arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩


set_option maxHeartbeats 400000 in
theorem overDecVarint_pre_tag10_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegsPlaced ext s0 g 0x23a8#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 0x23b4#64 ∧
        OverDecSavedRegsPl g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq rfl,
    by simp only [hsp, arm64_norm, wp_norm],
    by simp only [htr, arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
theorem overDecVarint_post_tag10_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 : State} {g : OverDecG} {oldVal val : BitVec 32} :
    ∀ s2 : State,
      s2.pc = (blkPl_518).base + 0x23b4#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 0x2160#64) s2
        ((g.q + 0xa80#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + 0xa80#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp2]),
    by simp only [arm64_norm, wp_norm],
    by simp only [htr2, arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩


set_option maxHeartbeats 400000 in
theorem overDecVarint_pre_tag11_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegsPlaced ext s0 g 0x2390#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 0x239c#64 ∧
        OverDecSavedRegsPl g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq rfl,
    by simp only [hsp, arm64_norm, wp_norm],
    by simp only [htr, arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩

set_option maxHeartbeats 400000 in
theorem overDecVarint_post_tag11_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 : State} {g : OverDecG} {oldVal val : BitVec 32} :
    ∀ s2 : State,
      s2.pc = (blkPl_518).base + 0x239c#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 0x2160#64) s2
        ((g.q + 0xa84#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + 0xa84#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  wp_steps
  refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm]) ?_
  refine ⟨Entails.of_eq (by rw [hsp2]),
    by simp only [arm64_norm, wp_norm],
    by simp only [htr2, arm64_norm, wp_norm],
    by simp only [h19, arm64_norm, wp_norm],
    by simp only [h20, arm64_norm, wp_norm],
    by simp only [h26, arm64_norm, wp_norm],
    by simp only [h21, arm64_norm, wp_norm],
    by simp only [h24, arm64_norm, wp_norm],
    by simp only [h25, arm64_norm, wp_norm],
    by simp only [h27, arm64_norm, wp_norm],
    by simp only [h28, arm64_norm, wp_norm],
    by simp only [h29, arm64_norm, wp_norm],
    by simp only [hv, arm64_norm, wp_norm]⟩


/-! ## Main Relocatable Varint Arm Theorems -/

set_option maxHeartbeats 600000 in
theorem overDecArm_varint_placed_ext_of_dv5 [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (SpqrH.decodeVarint2SpecX A)) :
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
      OverDecVarintField fl → fl.Ok → fl.Fresh v →
      (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
      OverDecRegsPlaced ext s0 g (overDecArmOff fl) s →
      s.readReg64 .x0 = overDecWt fl →
      s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
        (overDecHeapExt A g (fl.payload ++ rest) v)
        (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
          (P_f ⊢ overDecHeapExt A g rest (v.apply fl)))
        (PanicOomProp s0) := by
  intro s0 s g v fl rest hP _hOk _hFresh hsuf hlen hregs hx0 _hx22
  rcases fl with (_ | _)
  · rename_i fb
    rcases fb with (val | _ | _ | _ | val | _ | _ | _)
    · -- Tag 1: .base (.version val)
      have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
        suffix_payload_of_suffix_enc hsuf
      refine overDecArm_varint_of_pre_post_placed_ext hDv5 hsuf_pay hlen hregs
        (spOff := 0xa78#64) (oldVal := v.base.version) (val := val)
        (frameRest :=
          ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
          ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
          ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
          overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length)
        (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
        (by
          have hhead : prostSSGQHead A (g.q + 0x930#64) v =
              prostSSGQHead A (g.q + 0x930#64) (v.apply (.base (.version val))) := rfl
          have hrest : overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length =
              overDecVarintRestExt A g (v.apply (.base (.version val)))
                (encodeVarint (val.setWidth 64) ++ rest).length := by
            unfold overDecVarintRestExt; rw [hhead]
          rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.base (.version val))) hsuf_pay]
          dsimp only [SSGQ.apply, SSG.apply]
          try ac_rfl)
        (overDecVarint_pre_tag1_placed hregs hx0)
        overDecVarint_post_tag1_placed
    · cases hP
    · cases hP
    · cases hP
    · -- Tag 5: .base (.prevCounter val)
      have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
        suffix_payload_of_suffix_enc hsuf
      refine overDecArm_varint_of_pre_post_placed_ext hDv5 hsuf_pay hlen hregs
        (spOff := 0xa7c#64) (oldVal := v.base.prevCounter) (val := val)
        (frameRest :=
          ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
          ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
          ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
          overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length)
        (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
        (by
          have hhead : prostSSGQHead A (g.q + 0x930#64) v =
              prostSSGQHead A (g.q + 0x930#64) (v.apply (.base (.prevCounter val))) := rfl
          have hrest : overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length =
              overDecVarintRestExt A g (v.apply (.base (.prevCounter val)))
                (encodeVarint (val.setWidth 64) ++ rest).length := by
            unfold overDecVarintRestExt; rw [hhead]
          rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.base (.prevCounter val))) hsuf_pay]
          dsimp only [SSGQ.apply, SSG.apply]
          try ac_rfl)
        (overDecVarint_pre_tag5_placed hregs hx0)
        overDecVarint_post_tag5_placed
    · cases hP
    · cases hP
    · cases hP
  · cases hP
  · cases hP
  · -- Tag 10: .remReg val
    rename_i val
    have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
      suffix_payload_of_suffix_enc hsuf
    refine overDecArm_varint_of_pre_post_placed_ext hDv5 hsuf_pay hlen hregs
      (spOff := 0xa80#64) (oldVal := v.ext.remReg) (val := val)
      (frameRest :=
        ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
        overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length)
      (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
      (by
        have hhead : prostSSGQHead A (g.q + 0x930#64) v =
            prostSSGQHead A (g.q + 0x930#64) (v.apply (.remReg val)) := rfl
        have hrest : overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length =
            overDecVarintRestExt A g (v.apply (.remReg val))
              (encodeVarint (val.setWidth 64) ++ rest).length := by
          unfold overDecVarintRestExt; rw [hhead]
        rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.remReg val)) hsuf_pay]
        dsimp only [SSGQ.apply]
        try ac_rfl)
      (overDecVarint_pre_tag10_placed hregs hx0)
      overDecVarint_post_tag10_placed
  · -- Tag 11: .locReg val
    rename_i val
    have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
      suffix_payload_of_suffix_enc hsuf
    refine overDecArm_varint_of_pre_post_placed_ext hDv5 hsuf_pay hlen hregs
      (spOff := 0xa84#64) (oldVal := v.ext.locReg) (val := val)
      (frameRest :=
        ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
        overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length)
      (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
      (by
        have hhead : prostSSGQHead A (g.q + 0x930#64) v =
            prostSSGQHead A (g.q + 0x930#64) (v.apply (.locReg val)) := rfl
        have hrest : overDecVarintRestExt A g v (encodeVarint (val.setWidth 64) ++ rest).length =
            overDecVarintRestExt A g (v.apply (.locReg val))
              (encodeVarint (val.setWidth 64) ++ rest).length := by
          unfold overDecVarintRestExt; rw [hhead]
        rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.locReg val)) hsuf_pay]
        dsimp only [SSGQ.apply]
        try ac_rfl)
      (overDecVarint_pre_tag11_placed hregs hx0)
      overDecVarint_post_tag11_placed
  · cases hP
  · cases hP
  · cases hP

theorem overDecArm_varint_placed_of_dv5 [LibsignalPlacement]
    (hDv5 : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (SpqrH.decodeVarint2SpecX A0)) :
    OverDecArmPlacedStmtTR OverDecVarintField :=
  fun ext => overDecArm_varint_placed_ext_of_dv5 (hDv5 ext)

alias overDecArm_varint_cli_placed_of_dv5 := overDecArm_varint_placed_of_dv5

section Cro

open CryptoVerification.LibsignalPublicApi

private theorem SepWPp_bind_sepWP_frame_cro_varint_pl [LibsignalPlacement]
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

private theorem overDecVarint_call_decodeVarint5_lscl_pl [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State}
    {bufRef slot ptr : BitVec 64} {val : BitVec 32} {rest : List (BitVec 8)}
    {F : SepProp} {Q : State → SepProp → Prop}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (SpqrH.decodeVarint2SpecX A)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hpc : s.pc = lsmpl.base 515) (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = bufRef)
    (hlen : (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63)
    (hnext : ∀ s2 : State, s2.pc = s.readReg64 .lr → s2.status = .Running →
      s2.sp = s.sp → s2.spAligned = true → CalleeSavedPreserved s s2 →
      (lsProg_518 ext).CodeLoaded s2.mem →
      s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = val.setWidth 64 →
      s2.trace = s0.trace →
      SepWPp (lsProg_518 ext) ret s2
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          A.pool ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
        Q (PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ret s
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
      Q (PanicOomProp s0) := by
  intro R hm hL
  let x : DecodeVarintSlowGhost :=
    ⟨bufRef, slot, ptr, encodeVarint (val.setWidth 64) ++ rest⟩
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl (SpqrH.decodeVarint2SpecX A)).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded, SpqrH.decodeVarint2SpecX, x]
    rw [sepConj_assoc, sepConj_left_comm _ (⌜LibsignalCodeLoaded _ _⌝), satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hDv5 x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [decodeVarint2SpecX_post_encodeVarint_eq] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0m, hx1m⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    rw [← sepConj_assoc] at hpost
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hsteps.codeLoaded hL)
        hx0m hx1m (htrm.trans htr) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · change sm.mem ⊨ (⌜allocFailedIn s sm ∧ s.trace <+: sm.trace⌝ ∗ anyHeap) ∗ (F ∗ R) at hpost
    rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_eq_varint_pl htr⟩)⟩
  · exact (not_satisfies_false_sepConj hpost).elim

set_option maxHeartbeats 600000 in
private theorem overDecArm_varint_cro_of_pre_post_placed_ext [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (SpqrH.decodeVarint2SpecX A)))
    {s0 s : State} {g : OverDecG} {v v' : SSGQ} {rest : List (BitVec 8)}
    {armOff retOff spOff : BitVec 64} {oldVal val : BitVec 32}
    {frameRest : SepProp}
    (hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hregs : OverDecRegsPlaced ext s0 g armOff s)
    (hsplit : overDecHeapExt A g (encodeVarint (val.setWidth 64) ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ oldVal) ∗
      frameRest)
    (hunsplit :
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ val) ∗
      frameRest =
      overDecHeapExt A g rest v')
    (hpre_step : SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + retOff ∧
        OverDecSavedRegsPl g s1))
    (hpost_step : ∀ s2 : State,
      s2.pc = (blkPl_518).base + retOff →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 8544#64) s2
        ((g.q + spOff) ↦₃₂ oldVal)
        (fun sf P_f =>
          (P_f ⊢ ((g.q + spOff) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf)) :
    SepWPp (lsProg_518 ext)
      ((blkPl_518).base + 8544#64) s
      (overDecHeapExt A g (encodeVarint (val.setWidth 64) ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapExt A g rest v'))
      (PanicOomProp s0) := by
  refine sepWPp_lift_cro_regs hcro ?_
  rcases hregs with ⟨_hpc, _hrun, hsp, hsp_align, _htr, _hL, _hsaved⟩
  have hlen_pay : (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63 :=
    payload_append_length_lt_of_suffix hsuf_pay hlen
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  rw [hsplit]
  refine SepWPp_bind_sepWP_frame_cro_varint_pl hcro hpre_step
    rfl
    fun s1 hpc1 hrun1 _hL1 hcro1 ⟨hsp1, htr1, hx0_1, hlr1, hsaved1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length)
  have hframe_eq :
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        (sliceCursorAt (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) ∗
          A.pool ∗
          stackAt g.q decodeVarint2StackX ∗
          ((g.q + spOff) ↦₃₂ oldVal) ∗
          frameRest) =
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool ∗
        stackAt s1.sp decodeVarint2StackX) ∗
        (((g.q + spOff) ↦₃₂ oldVal) ∗ frameRest) := by
    rw [hsp1]
    simp only [sepConj_assoc]
  rw [hframe_eq]
  refine overDecVarint_call_decodeVarint5_lscl_pl hDv5 hcro1.1 htr1 hpc1 hrun1 hsp1_al hx0_1 hlen_pay
    fun s2 hpc2_lr hrun2 hsp2_1 _hsp2_al hcs2 _hL2 hx0_2 hx1_2 htr2 => ?_
  have hpc2 : s2.pc = (blkPl_518).base + retOff := hpc2_lr.trans hlr1
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have hsaved2 : OverDecSavedRegsPl g s2 := overDecSavedRegsPl_of_calleeSaved hsaved1 hcs2
  rw [hsp1]
  refine SepWPp_ret_sepWP_frame_varint_pl
    (hpost_step s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2 hsaved2)
    (F := ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool ∗
      stackAt g.q decodeVarint2StackX ∗
      frameRest)
    (by dsimp only [curPtr]; ac_rfl)
    fun sf hpcf hrunf hLf ⟨hspf, htrf, hsavedf⟩ => ?_
  have hspf_align : (sf.sp &&& 15#64 == 0#64) = true := by rw [hspf]; exact hq_align
  refine ⟨⟨hpcf, hrunf, hspf, hspf_align, htrf, hLf, hsavedf⟩, ?_⟩
  apply Entails.of_eq
  rw [← hunsplit]
  dsimp only [curPtr]
  ac_rfl

set_option maxHeartbeats 600000 in
/-- Fixed-`ext` `LibsignalCodeRoLoaded` varint arms (`OverDecArmCroPlacedAtTR ext OverDecVarintField`) discharged from `HookSat` on `ext`. -/
theorem overDecArm_varint_cro_placed_of_hooks [LibsignalPlacement]
    {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A0))
    (hpanic_alloc : ext lsHandleAllocErrorSym = some Rust.panicked) :
    OverDecArmCroPlacedAtTR ext OverDecVarintField := by
  have hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (SpqrH.decodeVarint2SpecX A0)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
      (SpqrH.bm6_decodeVarint5_placed_of_hooks hshim halloc hpanic_alloc)
  intro s0 s g v fl rest hP _hOk _hFresh hsuf hlen ⟨hcro, hregs⟩ hx0 _hx22
  rcases fl with (_ | _)
  · rename_i fb
    rcases fb with (val | _ | _ | _ | val | _ | _ | _)
    · have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
        suffix_payload_of_suffix_enc hsuf
      refine overDecArm_varint_cro_of_pre_post_placed_ext hDv5 hsuf_pay hlen hcro hregs
        (spOff := 0xa78#64) (oldVal := v.base.version) (val := val)
        (frameRest :=
          ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
          ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
          ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
          overDecVarintRestExt A0 g v (encodeVarint (val.setWidth 64) ++ rest).length)
        (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
        (by
          have hhead : prostSSGQHead A0 (g.q + 0x930#64) v =
              prostSSGQHead A0 (g.q + 0x930#64) (v.apply (.base (.version val))) := rfl
          have hrest : overDecVarintRestExt A0 g v (encodeVarint (val.setWidth 64) ++ rest).length =
              overDecVarintRestExt A0 g (v.apply (.base (.version val)))
                (encodeVarint (val.setWidth 64) ++ rest).length := by
            unfold overDecVarintRestExt; rw [hhead]
          rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.base (.version val))) hsuf_pay]
          dsimp only [SSGQ.apply, SSG.apply]
          try ac_rfl)
        (overDecVarint_pre_tag1_placed hregs hx0)
        overDecVarint_post_tag1_placed
    · cases hP
    · cases hP
    · cases hP
    · have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
        suffix_payload_of_suffix_enc hsuf
      refine overDecArm_varint_cro_of_pre_post_placed_ext hDv5 hsuf_pay hlen hcro hregs
        (spOff := 0xa7c#64) (oldVal := v.base.prevCounter) (val := val)
        (frameRest :=
          ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
          ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
          ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
          overDecVarintRestExt A0 g v (encodeVarint (val.setWidth 64) ++ rest).length)
        (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
        (by
          have hhead : prostSSGQHead A0 (g.q + 0x930#64) v =
              prostSSGQHead A0 (g.q + 0x930#64) (v.apply (.base (.prevCounter val))) := rfl
          have hrest : overDecVarintRestExt A0 g v (encodeVarint (val.setWidth 64) ++ rest).length =
              overDecVarintRestExt A0 g (v.apply (.base (.prevCounter val)))
                (encodeVarint (val.setWidth 64) ++ rest).length := by
            unfold overDecVarintRestExt; rw [hhead]
          rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.base (.prevCounter val))) hsuf_pay]
          dsimp only [SSGQ.apply, SSG.apply]
          try ac_rfl)
        (overDecVarint_pre_tag5_placed hregs hx0)
        overDecVarint_post_tag5_placed
    · cases hP
    · cases hP
    · cases hP
  · cases hP
  · cases hP
  · rename_i val
    have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
      suffix_payload_of_suffix_enc hsuf
    refine overDecArm_varint_cro_of_pre_post_placed_ext hDv5 hsuf_pay hlen hcro hregs
      (spOff := 0xa80#64) (oldVal := v.ext.remReg) (val := val)
      (frameRest :=
        ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
        overDecVarintRestExt A0 g v (encodeVarint (val.setWidth 64) ++ rest).length)
      (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
      (by
        have hhead : prostSSGQHead A0 (g.q + 0x930#64) v =
            prostSSGQHead A0 (g.q + 0x930#64) (v.apply (.remReg val)) := rfl
        have hrest : overDecVarintRestExt A0 g v (encodeVarint (val.setWidth 64) ++ rest).length =
            overDecVarintRestExt A0 g (v.apply (.remReg val))
              (encodeVarint (val.setWidth 64) ++ rest).length := by
          unfold overDecVarintRestExt; rw [hhead]
        rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.remReg val)) hsuf_pay]
        dsimp only [SSGQ.apply]
        try ac_rfl)
      (overDecVarint_pre_tag10_placed hregs hx0)
      overDecVarint_post_tag10_placed
  · rename_i val
    have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
      suffix_payload_of_suffix_enc hsuf
    refine overDecArm_varint_cro_of_pre_post_placed_ext hDv5 hsuf_pay hlen hcro hregs
      (spOff := 0xa84#64) (oldVal := v.ext.locReg) (val := val)
      (frameRest :=
        ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
        overDecVarintRestExt A0 g v (encodeVarint (val.setWidth 64) ++ rest).length)
      (by rw [overDecHeap_eq_varint_split_ext g v hsuf_pay]; try ac_rfl)
      (by
        have hhead : prostSSGQHead A0 (g.q + 0x930#64) v =
            prostSSGQHead A0 (g.q + 0x930#64) (v.apply (.locReg val)) := rfl
        have hrest : overDecVarintRestExt A0 g v (encodeVarint (val.setWidth 64) ++ rest).length =
            overDecVarintRestExt A0 g (v.apply (.locReg val))
              (encodeVarint (val.setWidth 64) ++ rest).length := by
          unfold overDecVarintRestExt; rw [hhead]
        rw [hrest, ← overDecHeap_eq_varint_unsplit_ext g (v.apply (.locReg val)) hsuf_pay]
        dsimp only [SSGQ.apply]
        try ac_rfl)
      (overDecVarint_pre_tag11_placed hregs hx0)
      overDecVarint_post_tag11_placed
  · cases hP
  · cases hP
  · cases hP

end Cro

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
