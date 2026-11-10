/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Relocatable Loop Head (`+0x2160 → +0x216c / +0x2620`) of Inlined `SessionStructure::decode`

Relocatable (`[LibsignalPlacement]`) verification of the 3-instruction loop head at
`(blkPl_518).base + 0x2160` (`overDecHeadCons_placed` when `rest ≠ []` and `overDecHeadNil_placed`
when `rest = []`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ prostSSGQAt)
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem SepWPp_bind_sepWP_frame_cl {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : prog.CodeLoaded s.mem)
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
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun (hsteps.codeLoaded hcl) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem rest_len_ofNat64_ne_zero_pl {rest enc : List (BitVec 8)}
    (hne : rest ≠ []) (hsuf : rest <:+ enc) (hlen : enc.length < 2 ^ 62) :
    BitVec.ofNat 64 rest.length ≠ 0#64 := by
  have hpos : 0 < rest.length := List.length_pos_iff.mpr hne
  rcases hsuf with ⟨t, ht⟩
  have hle : rest.length ≤ enc.length := by rw [← ht, List.length_append]; omega
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64)] at hnat
  omega

set_option maxHeartbeats 400000 in
private theorem head_cons_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (hlen_nz : BitVec.ofNat 64 rest.length ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x2160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
       Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest) ∧
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
  dsimp only [Prost.sliceCursorAfter] at ⊢
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
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem head_nil_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (blkPl_518).base + 0x2160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x2620#64) s
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
       Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc [])
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc []) ∧
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
  dsimp only [Prost.sliceCursorAfter, List.length_nil, BitVec.ofNat_eq_ofNat] at ⊢
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
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-- Relocatable `[LibsignalPlacement]` loop head (`+0x2160 → +0x216c`) when `rest ≠ []`. -/
theorem overDecHeadCons_placed [LibsignalPlacement] : OverDecHeadConsPlacedStmt := by
  intro ext s0 s g v rest hne hsuf hlen hregs
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hlen_nz := rest_len_ofNat64_ne_zero_pl hne hsuf hlen
  have hstep := head_cons_placed_wp ext s g rest hlen_nz
    hpc hrun hsp hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  unfold overDecHeap overDecHeapExt
  refine SepWPp_bind_sepWP_frame_cl hcl hstep (by sep_focus)
    fun sf hpcf hrunf hclf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  exact Entails.of_eq (by ac_rfl)

/-- Relocatable `[LibsignalPlacement]` loop head (`+0x2160 → +0x2620`) when `rest = []`. -/
theorem overDecHeadNil_placed [LibsignalPlacement] : OverDecHeadNilPlacedStmt := by
  intro ext s0 s g v _hlen hregs
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hstep := head_nil_placed_wp ext s g
    hpc hrun hsp hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  unfold overDecHeap overDecHeapExt
  refine SepWPp_bind_sepWP_frame_cl hcl hstep (by sep_focus)
    fun sf hpcf hrunf hclf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
