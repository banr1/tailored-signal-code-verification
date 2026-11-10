/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Top
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.EntryPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.HeadPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.KeyPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesTRPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvOkPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ComposePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ComposeCroPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Chain3CroCPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Placed Top-Level Inlined `SessionStructure::decode`

Wires the `[LibsignalPlacement]` Block-`518` entry, loop-head, key, varint, bytes, tag-6
(`sender_chain`), and tag-7 (`receiver_chains`) contracts into `OverPrevDecodePlacedStmt` and the
fixed-`ext` `LibsignalCodeRoLoaded` theorem `overPrevDecode_cro_placed_of_hooks`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Std Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.E2E.Record (A0)
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ ExtraGQ GenFieldQ prostSSGQAt)
open CryptoVerification.CodeLayout
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed
open CryptoVerification.LibsignalPublicApi
open Proofs.libsignal

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] State.readReg32
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Fixed-`ext` `LibsignalCodeRoLoaded` Tag-6 (`sender_chain`), Tag-7 (`receiver_chains`), & Top-Level `SessionStructure::decode` -/

private theorem allowPanic_oom_of_trace_eq_top_pl {s0 s sf : State} {F : SepProp}
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

private theorem SepWPp_weaken_frame_top_pl {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

private theorem SepWPp_bind_sepWP_frame_top_pl {prog : Program} {mid ret : BitVec 64} {s : State}
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

private theorem SepWPp_bind_sepWP_frame_cro_top_pl [LibsignalPlacement]
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

private theorem SepWPp_ret_sepWP_frame_top_pl {prog : Program} {ret : BitVec 64} {s : State}
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

private theorem SepWPp_call_frame_cro_oom_top_pl [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hcall : subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem → StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ (StoreKit.withLsCodeRoLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [StoreKit.withLsCodeRoLoaded]
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcro, hm⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) h1
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R) hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ |
      ⟨code, _, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  rotate_right; · dsimp only [StoreKit.withLsCodeRoLoaded] at _hoom_post; rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm hLm
        (hcro.of_keepsFrozen hsteps.keepsFrozen) R hpost hLm
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hpost
    rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost,
      allowPanic_oom_of_trace_eq_top_pl htr⟩)⟩
  · dsimp only [StoreKit.withLsCodeRoLoaded] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

private theorem stackAt_sub_eq_top_pl (sp : BitVec 64) (M N : Nat) (hMN : N ≤ M := by decide)
    (hbound : M < 2 ^ 64 := by decide) :
    stackAt sp M = stackAt sp N ∗ memRegion (sp - BitVec.ofNat 64 M) (M - N) := by
  have h1 : M = N + (M - N) := (Nat.add_sub_of_le hMN).symm
  have h2 := ProofLib.stackAt_split_bottom sp N (M - N) (by omega)
  rw [← h1] at h2
  rw [h2, sepConj_comm]

private abbrev toChain3GTop (g : OverDecG) : VerNe.Chain3.OverDecG :=
  ⟨g.q, g.r19, g.r20, g.r26, g.prevCap, g.prevPtr, g.encCap, g.encPtr, g.enc, g.sv⟩

private theorem SepWPp_bind_sepWP_withPanics_frame_cro_top_pl [LibsignalPlacement]
    {ext : String → Option (State → State)} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP (lsProg_518 (Rust.withPanics ext)) mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      (lsProg_518 ext).CodeLoaded sm.mem → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp (lsProg_518 ext) ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp (lsProg_518 ext) ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have h1 : IsLsBlockProg (lsProg_518 (Rust.withPanics ext)) 518 (Rust.withPanics ext) := inferInstance
  have h2 : IsLsBlockProg (lsProg_518 ext) 518 ext := inferInstance
  have hL' : (lsProg_518 (Rust.withPanics ext)).CodeLoaded s.mem :=
    h1.eq_blockProgram ▸ hcro.1 518 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  obtain ⟨sm, hsteps_wp, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL'
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hext : ∀ pc, (lsProg_518 (Rust.withPanics ext)).externAt? pc = (lsProg_518 ext).externAt? pc :=
    ls_externAt?_withPanics_eq (prog1 := lsProg_518 (Rust.withPanics ext)) (prog2 := lsProg_518 ext)
  have hsvc : (lsProg_518 (Rust.withPanics ext)).svc = (lsProg_518 ext).svc := by
    rw [h1.eq_blockProgram, h2.eq_blockProgram]; rfl
  have hsteps : Steps (lsProg_518 ext) s sm := Steps.of_sameHooks hext hsvc hsteps_wp
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : (lsProg_518 ext).CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (hcro.of_keepsFrozen hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem SepWPp_ret_sepWP_withPanics_frame_top_pl [LibsignalPlacement]
    {ext : String → Option (State → State)} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP (lsProg_518 (Rust.withPanics ext)) ret s P_step
      (fun sf P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hpost : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      (lsProg_518 ext).CodeLoaded sf.mem → Q_regs sf → Q sf (P_step_post ∗ F)) :
    SepWPp (lsProg_518 ext) ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  have h1 : IsLsBlockProg (lsProg_518 (Rust.withPanics ext)) 518 (Rust.withPanics ext) := inferInstance
  have h2 : IsLsBlockProg (lsProg_518 ext) 518 ext := inferInstance
  have hL' : (lsProg_518 (Rust.withPanics ext)).CodeLoaded s.mem :=
    h1.eq_blockProgram ▸ hcro.1 518 (by decide) (by decide) (Rust.withPanics ext) (fun _ => none) Syscall.standard
  obtain ⟨sf, hsteps_wp, ⟨hpc, hrun, P_step', hmf, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL'
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hext : ∀ pc, (lsProg_518 (Rust.withPanics ext)).externAt? pc = (lsProg_518 ext).externAt? pc :=
    ls_externAt?_withPanics_eq (prog1 := lsProg_518 (Rust.withPanics ext)) (prog2 := lsProg_518 ext)
  have hsvc : (lsProg_518 (Rust.withPanics ext)).svc = (lsProg_518 ext).svc := by
    rw [h1.eq_blockProgram, h2.eq_blockProgram]; rfl
  have hsteps : Steps (lsProg_518 ext) s sf := Steps.of_sameHooks hext hsvc hsteps_wp
  refine ⟨sf, hsteps, .inl ⟨hpc, hrun, P_step_post ∗ F, ?_,
    hpost sf hpc hrun (hsteps.codeLoaded hL) hregs⟩⟩
  rw [sepConj_assoc]
  exact Satisfies.mono (sepConj_mono_left hent) hmf

set_option maxHeartbeats 400000 in
/-- Tag 6 (`sender_chain`), `+0x2214 → +0x2160`, on `lsProg_518 ext` under `LibsignalCodeRoLoaded`. -/
theorem overDecArmSender_cro_core [LibsignalPlacement] (ext : String → Option (State → State))
    (hC5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
      (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW))
    (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (hcok : c.Ok) (hnone : v.base.sender = none)
    (hsuf : ((GenFieldQ.base (.sender c)).enc ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hregs : OverDecRegsCroPlaced ext s0 g 0x2214#64 s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (overDecHeap g ((GenFieldQ.base (.sender c)).payload ++ rest) v)
      (fun sf P_f => OverDecRegsCroPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest ⟨v.base.apply (.sender c), v.ext⟩))
      (PanicOomProp s0) := by
  rcases hregs with ⟨hcro, hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  refine sepWPp_lift_cro_regs hcro ?_
  obtain ⟨pfx, hpfx, hpay_len⟩ := VerNe.Chain3.overDecChain_payload_suffix hsuf hlen
  have hheap_eq : overDecHeap g ((GenFieldQ.base (.sender c)).payload ++ rest) v =
      VerNe.Chain3.overDecHeap (toChain3GTop g)
        ((GenFieldQ.base (.sender c)).payload ++ rest) v := rfl
  rw [hheap_eq, VerNe.Chain3.overDecChain_heap_pre (toChain3GTop g) v pfx _ rest hpfx hnone,
    VerNe.Chain3.overDecChain_mem96 g.q]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun u9 => SepWPp.exists_elim fun u8 => SepWPp.exists_elim fun u7 =>
    SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u5 => SepWPp.exists_elim fun u4 =>
    SepWPp.exists_elim fun u3 => SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 => ?_
  have hstepA :=
    VerNe.Chain3.overDecChain_segA_placed ext s g.q u1 u2 u3 u4 u5 u6 u7 u8 u9
      hpc hrun hsp hal hx0 hx21 hx24 hx25 hx29
  refine SepWPp_bind_sepWP_withPanics_frame_cro_top_pl hcro hstepA (by sep_focus)
    fun s1 hpc1 hrun1 _hcl1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1,
    hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs_1⟩
  refine SepWPp_weaken_frame_top_pl (VerNe.Chain3.overDecChain_bridge g.q)
    (by sep_focus) ?_
  have hsp1q : s1.sp = g.q := hsp1.trans hsp
  have hsp1_al : s1.spAligned = true := by simp only [State.spAligned, hsp1, hal]
  have hx0_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by rw [hx0_1]; rfl
  refine SepWPp_call_frame_cro_oom_top_pl
    (x := (⟨g.q + 0x9c0#64, c, g.q + 0xbe8#64, g.q + 0x920#64,
      g.encPtr + BitVec.ofNat 64 pfx.length, rest⟩ : ChainMergeGenGhost))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0x9c0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62)
    (T := VerNe.Chain3.chain3GAt A0 (g.q + 0x9c0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) (g.encPtr + BitVec.ofNat 64 pfx.length)
        (c.payload ++ rest) ∗
      stackAt g.q VerNe.Chain3.chainMerge3StackX)
    hcro1 (htr1.trans htr) hC5 hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [VerNe.Chain3.chainMerge3RawSpecW]; rw [hsp1q])
    ⟨hx0_w8, hx1_1, hx2_1, hcok, hpay_len⟩
    (by sep_focus)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 _hcl2 hcro2 => ?_)
  dsimp only [VerNe.Chain3.chainMerge3RawSpecW]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hx0_2⟩ => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1q
  have htr2 : s2.trace = s0.trace := htr2_1.trans (htr1.trans htr)
  rcases hcs2 with ⟨hx19_cs, hx20_cs, hx21_cs, _, _, hx24_cs, hx25_cs, hx26_cs, hx27_cs,
    hx28_cs, hx29_cs, hvregs_cs⟩
  have hstepB :=
    VerNe.Chain3.overDecChain_segB_placed ext s2 g.q g.r19 g.r20 g.r26 g.prevPtr
      hpc2 hrun2 hsp2 hx0_2
      ((hx19_cs.trans hx19_1).trans hx19) ((hx20_cs.trans hx20_1).trans hx20)
      ((hx21_cs.trans hx21_1).trans hx21) ((hx24_cs.trans hx24_1).trans hx24)
      ((hx25_cs.trans hx25_1).trans hx25) ((hx26_cs.trans hx26_1).trans hx26)
      ((hx27_cs.trans hx27_1).trans hx27) ((hx28_cs.trans hx28_1).trans hx28)
      ((hx29_cs.trans hx29_1).trans hx29)
  refine SepWPp_ret_sepWP_withPanics_frame_top_pl hcro2 hstepB (by rw [emp_sepConj])
    fun sf hpcf hrunf hclf hregsf => ?_
  rcases hregsf with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f,
    hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr2, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f,
    ((hvregs_f.trans hvregs_cs).trans hvregs_1).trans hvregs⟩, ?_⟩
  have hpost_eq : overDecHeap g rest ⟨v.base.apply (.sender c), v.ext⟩ =
      VerNe.Chain3.overDecHeap (toChain3GTop g) rest ⟨v.base.apply (.sender c), v.ext⟩ := rfl
  rw [hpost_eq, ← VerNe.Chain3.overDecChain_heap_post (toChain3GTop g) v c pfx _ rest hpfx,
    hsp1q, emp_sepConj]
  exact Entails.of_eq (by ac_rfl)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` Tag-6 (`sender_chain`) arm
(`OverDecArmCroPlacedAtTR ext OverDecSenderField`), parameterized by `hC5` at Block `516`. -/
theorem overDecArmSender_cro_placed_of_chain5 [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hC5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
      (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW)) :
    OverDecArmCroPlacedAtTR ext OverDecSenderField := by
  intro s0 s g v fl rest hP hok hfresh hsuf hlen hregs hx0 _hx22
  cases fl
  case base f =>
    cases f
    case sender c =>
      have hok' : c.Ok ∧ c.priv.length = 32 ∧ c.ck.isSome = true ∧ c.keys = [] := hok
      have hfresh' : v.ext = ExtraGQ.empty ∧ v.base.sender = none := hfresh
      have hregs' : OverDecRegsCroPlaced ext s0 g 0x2214#64 s := hregs
      have hx0' : s.readReg64 .x0 = 2#64 := hx0
      exact overDecArmSender_cro_core ext hC5 s0 s g v c rest
        hok'.1 hfresh'.2 hsuf hlen hregs' hx0'
    all_goals exact False.elim hP
  all_goals exact False.elim hP

theorem overDecArmSender_cro_placed_of_hooks [LibsignalPlacement] {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A0))
    (hrealloc : HookSat ext lsRustReallocSym (rustReallocSpec A0))
    (hdealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A0))
    (hmc : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    OverDecArmCroPlacedAtTR ext OverDecSenderField :=
  overDecArmSender_cro_placed_of_chain5
    (chainMerge5_cro_of_block_hooks (callerProg := lsProg_518 ext)
      hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)

private def recv2114HeapTopPlaced (A : RustAlloc) (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ)
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
private theorem step_from_2114_to_2160_full_top_pl [LibsignalPlacement] (A : RustAlloc)
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
      (recv2114HeapTopPlaced A g rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c)
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
  have hsplit : recv2114HeapTopPlaced A g rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c =
      (∃∗ d0 : BitVec 128, ∃∗ d1 : BitVec 128, ∃∗ d2 : BitVec 128,
       ∃∗ d3 : BitVec 128, ∃∗ d4 : BitVec 128, ∃∗ d5 : BitVec 128,
       ∃∗ dw6 : BitVec 64,
        ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ BitVec.ofNat 64 v.base.recv.length) ∗
        RawByteMove.chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        RawByteMove.chunks104_6QWAt dst d0 d1 d2 d3 d4 d5 dw6) ∗ F_2114 := by
    unfold recv2114HeapTopPlaced F_2114
    rw [show ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64 = dst from rfl,
        memRegion104_eq_exists_chunks104_6QWAt_rc dst]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply congrArg sepExists; funext _)
    ac_rfl
  rw [hsplit]
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  have hstep := step_2114_to_2160_top_placed ext s g ptr'
    (BitVec.ofNat 64 v.base.recv.length) (BitVec.ofNat 64 v.base.recv.length)
    q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
    hpc hrun hsp hal hx19 hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 hx29
  refine SepWPp_bind_sepWP_frame_top_pl hstep rfl
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

set_option maxHeartbeats 400000 in
/-- Segment B (`(blkPl_518).base + 0x2310 → +0x2160`) of the tag-7 (`receiver_chains`) arm under
`LibsignalCodeRoLoaded`, parameterized by `hGrow` at `lsmpl.base 43`. -/
theorem overDecRecv_segB_cro_placed_of_grow [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (StoreKit.withLsCodeRoLoaded lsmpl (Stage1X.growOneChainSpecX A0)))
    (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (_hOk : (GenFieldQ.base (.recv c)).Ok)
    (hFresh : (GenFieldQ.base (.recv c)).Fresh v)
    (_hsuf : ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc)
    (_hlen : g.enc.length < 2 ^ 62)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hregs : OverDecRegsPlaced ext s0 g 0x2310#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecRecvPostMergeHeapPlaced g rest v c)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeap g rest (v.apply (.base (.recv c)))))
      (PanicOomProp s0) := by
  have hfresh : v.base.recv.length < maxReceiverChains := hFresh.2
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  unfold overDecRecvPostMergeHeapPlaced
  rw [prostSSGQAt_eq_recv_sep_rest A0 (g.q + 0x930#64) v,
      memRegion344_a90_split_rc g.q]
  refine SepWPp_weaken_frame_top_pl (vecAt_recv_open_q_ext A0 g.q v.base.recv)
    (by sep_focus) ?_
  apply SepWPp_exists_left_rc; intro cap
  apply SepWPp_exists_left_rc; intro ptr
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨hlen_le, hcap_lt, hptr⟩
  refine SepWPp_weaken_frame_top_pl (prostChainGAt_move_chunks104_rc A0 (g.q + 0xbf0#64) c)
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i q0 q1 q2 q3 q4 q5 w6 H_c
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; intro hmov_c
  refine SepWPp_weaken_frame_top_pl
    (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_rc (g.q + 0xa90#64)))
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  by_cases hfull : v.base.recv.length = cap.toNat
  · refine SepWPp_weaken_frame_top_pl (vecBuf_recv_full_open_rc_ext A0 cap ptr v.base.recv hfull)
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
    have hstep1 := step_2310_to_growOne_of_eq_top_placed ext s g cap
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_cro_top_pl hcro hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 _hCLs1 hcro1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx0s1, hlrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : s1.spAligned = true := by
      simp only [State.spAligned]
      rwa [hsps1, ← hsp]
    rw [stackAt_sub_eq_top_pl g.q overDecStackX Stage1X.growOneChainStackX]
    refine SepWPp_weaken_frame_top_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_call_frame_cro_oom_top_pl
      (x := (g.q + 0x978#64, cap, ptr, bs))
      hcro1 (htrs1.trans htr) hGrow hpcs1 hruns1 hals1 hlrs1
      (growOne_plain_pre_eq_q g.q cap ptr bs s1 hsps1)
      ⟨hbs_len, hx0s1, hptr, hmax_lt⟩
      (by sep_focus)
      (by intro sf; rfl)
      (by intro _ _; rfl)
      ?_
    intro sm hpcm hrunm hspm halm hcsm _hCLm _hcrom
    obtain ⟨hx19m, hx20m, hx21m, hx22m, _, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    rw [hx19s1] at hx19m; rw [hx20s1] at hx20m; rw [hx21s1] at hx21m; rw [hx22s1] at hx22m
    rw [hx24s1] at hx24m; rw [hx25s1] at hx25m; rw [hx26s1] at hx26m; rw [hx27s1] at hx27m
    rw [hx28s1] at hx28m; rw [hx29s1] at hfpm; rw [hsps1] at hspm
    refine SepWPp_weaken_frame_top_pl
      (growOne_plain_post_elim_sp_q g.q cap ptr v.base.recv bs s1 sm hsps1 hfull hfresh hbs_len)
      rfl ?_
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro htrm
    have htrm' : sm.trace = s0.trace := htrm.trans (htrs1.trans htr)
    apply SepWPp_exists_left_rc; intro cap'
    apply SepWPp_exists_left_rc; intro p'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    refine SepWPp_weaken_frame_top_pl (hmov_arr p') (by sep_focus) ?_
    have hstep2 := step_234c_to_2114_top_placed ext sm g cap
      hpcm hrunm hspm hx19m hx20m hx21m hx22m hx24m hx25m hx26m hx27m hx28m hfpm
    refine SepWPp_bind_sepWP_frame_top_pl hstep2 (emp_sepConj _).symm
      fun s2 hpcs2 hruns2 hCLs2 hpost2 => ?_
    rcases hpost2 with ⟨hsps2, htrs2, hx19s2, hx20s2, hx21s2, hx22s2,
      hx24s2, hx25s2, hx26s2, hx27s2, hx28s2, hx29s2, hvregss2⟩
    have hals2 : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsps2, ← hsp]
    rw [← hlen_cap] at hx22s2 ⊢
    have hregs2 : OverDecRegsPlaced ext s0 g 0x2114#64 s2 :=
      ⟨hpcs2, hruns2, hsps2, hals2, htrs2.trans htrm', hCLs2,
       hx19s2, hx20s2, hx26s2, hx21s2, hx24s2, hx25s2, hx27s2, hx28s2, hx29s2,
       ((hvregss2.trans hvregsm).trans hvregss1).trans hvregs⟩
    refine SepWPp_weaken_frame_top_pl
      (P₂ := recv2114HeapTopPlaced A0 g rest v cap' p' q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq ?_) (sepConj_emp _).symm ?_
    · unfold recv2114HeapTopPlaced overPrevElemRest
      rw [stackAt_sub_eq_top_pl g.q overDecStackX Stage1X.growOneChainStackX]
      simp only [emp_sepConj]
      ac_rfl
    · rw [sepConj_emp]
      exact step_from_2114_to_2160_full_top_pl A0 ext s0 s2 g v c rest cap' p' q0 q1 q2 q3 q4 q5 w6 H_c
        hlt_cap' hcap_lt' hp' hmov_c hregs2 hx22s2
  · have hlt : v.base.recv.length < cap.toNat := by omega
    have hne : BitVec.ofNat 64 v.base.recv.length ≠ cap := len_ne_cap_of_lt_rc hlt
    rw [vecBuf_recv_not_full_open_rc_ext A0 cap ptr v.base.recv hlt hcap_lt]
    have hstep1 := step_2310_to_2114_of_ne_top_placed ext s g cap (BitVec.ofNat 64 v.base.recv.length)
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hne hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_top_pl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hCLs1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsps1, ← hsp]
    have hregs1 : OverDecRegsPlaced ext s0 g 0x2114#64 s1 :=
      ⟨hpcs1, hruns1, hsps1, hals1, htrs1.trans htr, hCLs1,
       hx19s1, hx20s1, hx26s1, hx21s1, hx24s1, hx25s1, hx27s1, hx28s1, hx29s1,
       hvregss1.trans hvregs⟩
    refine SepWPp_weaken_frame_top_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_weaken_frame_top_pl
      (P₂ := recv2114HeapTopPlaced A0 g rest v cap ptr q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq (by unfold recv2114HeapTopPlaced overPrevElemRest; ac_rfl))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact step_from_2114_to_2160_full_top_pl A0 ext s0 s1 g v c rest cap ptr q0 q1 q2 q3 q4 q5 w6 H_c
      hlt hcap_lt hptr hmov_c hregs1 hx22s1

set_option maxHeartbeats 400000 in
/-- Fixed-`ext` `LibsignalCodeRoLoaded` tag-7 (`receiver_chains`) arm
(`OverDecArmCroPlacedAtTR ext OverDecRecvField`), parameterized by `hGrow` (`lsmpl.base 43`) and
`hChain5` (`lsmpl.base 516`). -/
theorem overDecArmRecv_cro_placed_of_callees [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hGrow : subroutine_ok (lsProg_518 ext) (lsmpl.base 43)
      (StoreKit.withLsCodeRoLoaded lsmpl (Stage1X.growOneChainSpecX A0)))
    (hChain5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
      (StoreKit.withLsCodeRoLoaded lsmpl VerNe.Chain3.chainMerge3RawSpecW)) :
    OverDecArmCroPlacedAtTR ext OverDecRecvField := by
  intro s0 s g v fl rest hfl hok hfresh hsuf hlen ⟨hcro, hregs⟩ hx0 _hx22
  refine sepWPp_lift_cro_regs hcro ?_
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
      VerNe.Chain3.overDecHeap (toChain3GTop g) (c.payload ++ rest) v := rfl
  rw [hpay_eq, hheap_eq, overDecHeap_eq_recv_split (toChain3GTop g) v hsuf_pay]
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hCL, hsaved⟩
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  have hstep := overDecRecv_pre_step_80_placed (ext := ext) (g := toChain3GTop g)
    hpc hrun hsp hsp_align htr hsaved hx0
  refine SepWPp_bind_sepWP_frame_cro_top_pl hcro hstep rfl
    fun s1 hpc1 hrun1 _hCL1 hcro1 ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hlr1, hsaved1⟩ => ?_
  dsimp only [toChain3GTop] at hsp1 hx1_1 hx2_1
  rw [← sepConj_assoc]
  refine SepWPp_weaken_frame_top_pl (default_cells_bf0_entail_chain3GAt g.q) rfl ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length)
  have hx0_1_w8 : (s1.readReg64 .x0).setWidth 8 = 2#8 := by simp [hx0_1]
  refine SepWPp_call_frame_cro_oom_top_pl
    (x := (⟨g.q + 0xbf0#64, c, g.q + 0xbe8#64, g.q + 0x920#64, curPtr, rest⟩ :
      ChainMergeGenGhost))
    (φ := (s1.readReg64 .x0).setWidth 8 = 2#8 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
      s1.readReg64 .x2 = g.q + 0xbe8#64 ∧ c.Ok ∧ (c.payload ++ rest).length < 2 ^ 62)
    (T := VerNe.Chain3.chain3GAt A0 (g.q + 0xbf0#64) ChainG.empty ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64) curPtr (c.payload ++ rest) ∗
      stackAt g.q VerNe.Chain3.chainMerge3StackX)
    (F := overDecRecvFrameRest (toChain3GTop g) v (c.payload ++ rest).length)
    hcro1 htr1 hChain5 hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [VerNe.Chain3.chainMerge3RawSpecW]; rw [hsp1])
    ⟨hx0_1_w8, hx1_1, hx2_1, hc_ok, hlen_pay⟩
    (by dsimp only [curPtr, toChain3GTop]; ac_rfl)
    (hnext := fun s2 hpc2 hrun2 hsp2_1 _hsp2_al hcs2 hCL2 hcro2 => ?_)
  dsimp only [VerNe.Chain3.chainMerge3RawSpecW]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨htr2_1, hx0_2⟩ => ?_
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
  have hsaved2 : OverDecSavedRegs (toChain3GTop g) s2 := overDecSavedRegs_of_calleeSaved hsaved1 hcs2
  dsimp only [OverDecSavedRegs, toChain3GTop] at hsaved2
  have hregs2 : OverDecRegsPlaced ext s0 g 0x2310#64 s2 :=
    ⟨hpc2, hrun2, hsp2, hsp2_align, htr2, hCL2, hsaved2⟩
  have hpost_eq :
      prostChainGAt A0 (g.q + 0xbf0#64) c ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAfter (g.q + 0x920#64) curPtr (c.payload ++ rest) rest ∗
        stackAt g.q VerNe.Chain3.chainMerge3StackX ∗
        overDecRecvFrameRest (toChain3GTop g) v (c.payload ++ rest).length =
      overDecRecvPostMergeHeapPlaced g rest v c := by
    dsimp only [curPtr]
    exact overDecRecvPostMergeHeap_eq_unsplit (toChain3GTop g) v hsuf_pay
  rw [hpost_eq]
  exact overDecRecv_segB_cro_placed_of_grow hGrow s0 s2 g v c rest hok hfresh hsuf hlen hcro2 hregs2 hx0_2

private theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCl [LibsignalPlacement]
    {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCl lsmpl spec)) :
    subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
      dsimp only [withLsCl]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

theorem overDecArmRecv_cro_placed_of_hooks [LibsignalPlacement] {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A0))
    (hrealloc : HookSat ext lsRustReallocSym (rustReallocSpec A0))
    (hdealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A0))
    (hmc : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    OverDecArmCroPlacedAtTR ext OverDecRecvField :=
  overDecArmRecv_cro_placed_of_callees
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCl
      (growOneChain_placed_ok_cl_of_hooks (callerProg := lsProg_518 ext)
        hshim halloc hrealloc hpanic_raw))
    (chainMerge5_cro_of_block_hooks (callerProg := lsProg_518 ext)
      hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)

/-- Top-level fixed-`ext` `[LibsignalPlacement]` `SessionStructure::decode` (`OverPrevDecodeCroPlacedAt ext`)
under `LibsignalCodeRoLoaded`, discharged directly from the standard allocator, `memcpy`, and panic hooks. -/
theorem overPrevDecode_cro_placed_of_hooks [LibsignalPlacement] {ext : LibsignalHooks}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext lsRustAllocSym (rustAllocSpec A0))
    (hrealloc : HookSat ext lsRustReallocSym (rustReallocSpec A0))
    (hdealloc : HookSat ext lsRustDeallocSym (rustDeallocSpec A0))
    (hmc : HookSat ext lsMemcpySym framelessMemcpySpec)
    (hpanic_alloc : ext lsHandleAllocErrorSym = some Rust.panicked)
    (hpanic_raw : ext lsHandleErrorSym = some Rust.panicked) :
    OverPrevDecodeCroPlacedAt ext :=
  overPrevDecode_cro_of_key_arms
    (overDecEntry_cro_of_placed overDecEntry_placed ext)
    (overDecHeadCons_cro_of_placed overDecHeadCons_placed ext)
    (overDecHeadNil_cro_of_placed overDecHeadNil_placed ext)
    (overDecKey_cro_placed_of_hooks hshim halloc hpanic_alloc)
    (overDecArm_varint_cro_placed_of_hooks hshim halloc hpanic_alloc)
    (overDecArm_bytes_cro_placed_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)
    (overDecArmSender_cro_placed_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)
    (overDecArmRecv_cro_placed_of_hooks hshim halloc hrealloc hdealloc hmc hpanic_alloc hpanic_raw)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
