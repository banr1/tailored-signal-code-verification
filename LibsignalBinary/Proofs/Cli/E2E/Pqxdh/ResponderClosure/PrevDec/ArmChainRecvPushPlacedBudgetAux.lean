/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlaced
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Tag-7 (`receiver_chains`) Push Segment Helpers

Allocation envelope `OverDecRecvSegBEnv`, budget-threaded decode-loop heap predicates, `SepWPp`
framing combinators, and Block-`518` basic-block steppers for Segment B (`+0x2310 → +0x2160`) of
the tag-7 (`receiver_chains`) decode arm.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (arrayAt)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (chunks104_6QWAt)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG GenField prostChainGAt)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ SSGQ prostSSGQAt)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecG OverDecRegsPlaced
  SepWPp_exists_left_rc
  chunks104_6QWAt_read_a90_eq_rc chunks104_6QWAt_read_bf0_eq_rc
  chunks104_6QWAt_write_a90_eq_rc chunks104_6QWAt_write_eq_rc
  memRegion104_eq_exists_chunks104_6QWAt_rc memRegion344_a90_join_rc
  overDecHeapExt overDecRecvPostMergeHeapExt
  overDecStackX overPrevElemRestExt prostSSGQAt_fold_apply_recv_ext prostSSGQRest
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  GrowOne104Env growOne104Events
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)

abbrev Chain3OverDecG :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.OverDecG
abbrev Chain3OverDecRegsPlaced :=
  @CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.OverDecRegsPlaced
abbrev chain3OverPrevElemRestExt :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overPrevElemRestExt
abbrev chain3OverDecStackX :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecStackX
abbrev chain3OverDecHeapExt :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecHeapExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] State.readReg32
attribute [local arm64_norm, local wp_norm]
  Arm64.calleeSavedVRegs_advancePC Arm64.calleeSavedVRegs_setPC Arm64.calleeSavedVRegs_setMem
  Arm64.calleeSavedVRegs_setPState Arm64.calleeSavedVRegs_writeReg64 Arm64.calleeSavedVRegs_writeReg32
  Arm64.calleeSavedVRegs_writeReg isCalleeSavedVReg

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Exact Binary Allocation Envelope (`OverDecRecvSegBEnv`) -/

/-- Exact allocation envelope for Tag-7 (`receiver_chains`) Segment B (`+0x2310 → +0x2160`): `[]` when `recvLen < cap.toNat`, or `growOne104Events (BitVec.ofNat 64 recvLen)` when `recvLen = cap.toNat`. -/
def OverDecRecvSegBEnv (recvLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = growOne104Events (BitVec.ofNat 64 recvLen)

theorem overDecRecvSegBEnv_nil (recvLen : Nat) :
    OverDecRecvSegBEnv recvLen [] :=
  Or.inl rfl

theorem overDecRecvSegBEnv_grow (recvLen : Nat) {cap : BitVec 64}
    (hfull : recvLen = cap.toNat) :
    OverDecRecvSegBEnv recvLen (growOne104Events cap) := by
  unfold OverDecRecvSegBEnv
  simp [hfull, BitVec.ofNat_toNat]

theorem fitsEnv_growOne_of_segB {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {recvLen : Nat} {cap : BitVec 64}
    (hfull : recvLen = cap.toNat)
    (hfit : FitsEnv M lim st (OverDecRecvSegBEnv recvLen)) :
    FitsEnv M lim st (GrowOne104Env cap) := by
  intro evs hevs
  rw [hevs]
  exact hfit _ (overDecRecvSegBEnv_grow recvLen hfull)

/-! ## Budget-Threaded Decode Loop Heaps and `atState` Bridges -/

/-- Budget-threaded heap at `+0x2310` immediately after `bl merge<Chain>` over `PrevDec.OverDecG`. -/
def overDecRecvPostMergeHeapPlBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (v : SSGQ) (c : ChainG) : SepProp :=
  overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    prostSSGQAt A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    prostChainGAt A.repAlloc (g.q + 0xbf0#64) c ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st s

/-- Budget-threaded decode-loop invariant heap over `PrevDec.OverDecG`. -/
def overDecHeapPlBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (v : SSGQ) : SepProp :=
  overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    prostSSGQAt A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st s

theorem overDecHeapPlBudget_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (v : SSGQ) :
    overDecHeapPlBudget A lim st s g rest v =
      overDecHeapExt (A.atState lim st s) g rest v :=
  rfl

/-- Budget-threaded heap at `+0x2310` immediately after `bl merge<Chain>` over
`VerNe.Chain3.OverDecG`. -/
def overDecRecvPostMergeHeapBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : Chain3OverDecG)
    (rest : List (BitVec 8)) (v : SSGQ) (c : ChainG) : SepProp :=
  chain3OverPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    prostSSGQAt A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    prostChainGAt A.repAlloc (g.q + 0xbf0#64) c ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    stackAt g.q chain3OverDecStackX ∗ A.pool lim st s

theorem overDecRecvPostMergeHeapBudget_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : Chain3OverDecG)
    (rest : List (BitVec 8)) (v : SSGQ) (c : ChainG) :
    overDecRecvPostMergeHeapBudget A lim st s g rest v c =
      overDecRecvPostMergeHeapExt (A.atState lim st s) g rest v c :=
  rfl

/-- Budget-threaded decode-loop invariant heap over `VerNe.Chain3.OverDecG`. -/
def overDecHeapBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : Chain3OverDecG)
    (rest : List (BitVec 8)) (v : SSGQ) : SepProp :=
  chain3OverPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    prostSSGQAt A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q chain3OverDecStackX ∗ A.pool lim st s

theorem overDecHeapBudget_eq_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : Chain3OverDecG)
    (rest : List (BitVec 8)) (v : SSGQ) :
    overDecHeapBudget A lim st s g rest v =
      chain3OverDecHeapExt (A.atState lim st s) g rest v :=
  rfl

/-! ## `SepWPp` Framing and No-Panic Call Combinators -/

theorem SepWPp_weaken_frame_pl {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

theorem SepWPp_mono_post_pl {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q₁ Q₂ Qp : State → SepProp → Prop}
    (himp : ∀ sf P_f, Q₁ sf P_f → Q₂ sf P_f)
    (h : SepWPp prog ret s P Q₁ Qp) :
    SepWPp prog ret s P Q₂ Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f, hmf, himp sf P_f hQ⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

theorem SepWPp_bind_sepWP_frame_pl {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ := hnext sm hpc hrun hLm hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem libsignalCodeLoaded_preserve_pl {mpl : Obj.MultiPlacement} {prog : Program} {s sm : State}
    (hcl : LibsignalCodeLoaded mpl s.mem) (hsteps : Steps prog s sm) :
    LibsignalCodeLoaded mpl sm.mem :=
  fun i hi hmut X O svc => hsteps.codeLoaded (hcl i hi hmut X O svc)

theorem SepWPp_bind_sepWP_frame_lscl_pl [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun (libsignalCodeLoaded_preserve_pl hcl hsteps)
      hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem SepWPp_call_frame_plain_noPanic_pl {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      prog.CodeLoaded sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hstep : SepWP prog ret_pc s P
      (fun sm P_m => (P_m ⊢ spec.post x s sm ∗ F) ∧ sm.sp = s.sp ∧ CalleeSavedPreserved s sm) := by
    refine SepWP.call_subroutine_frame hcall hpc hrun hsp hlr
      (fun R' hm' => ?_)
      (fun R' sf _ hp => by rw [hpan_false] at hp; exact not_satisfies_false_sepConj hp)
      (fun R' code sf _ he => by rw [hexit_false] at he; exact not_satisfies_false_sepConj he)
      (fun sf hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm ⟨Entails.refl _, hspm, hcsm⟩)
      (fun R' sf _ ho => by rw [hoom_false] at ho; exact False.elim (not_satisfies_false_sepConj ho))
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm'⟩
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hspm, hcsm⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hpost : sm.mem ⊨ (spec.post x s sm ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hent) hmm
  have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm hspm hsp_alm hcsm hLm R hpost hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem SepWPp_call_frame_lscl_noPanic_pl [LibsignalPlacement]
    {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T) ∗ ⌜LibsignalCodeLoaded lsmpl s.mem⌝)
    (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  have hstep : SepWP prog ret_pc s P
      (fun sm P_m => (P_m ⊢ spec.post x s sm ∗ F) ∧ sm.sp = s.sp ∧ CalleeSavedPreserved s sm) := by
    refine SepWP.call_subroutine_frame hcall hpc hrun hsp hlr
      (fun R' hm' => ?_)
      (fun R' sf _ hp => by rw [hpan_false] at hp; exact not_satisfies_false_sepConj hp)
      (fun R' code sf _ he => by rw [hexit_false] at he; exact not_satisfies_false_sepConj he)
      (fun sf hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm ⟨Entails.refl _, hspm, hcsm⟩)
      (fun R' sf _ ho => by rw [hoom_false] at ho; exact False.elim (not_satisfies_false_sepConj ho))
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R'))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcl, hm'⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h1
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hspm, hcsm⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hpost : sm.mem ⊨ (spec.post x s sm ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hent) hmm
  have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm hspm hsp_alm hcsm
      (libsignalCodeLoaded_preserve_pl hcl hsteps)
      R hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem stackAt_sub_eq_pl (sp : BitVec 64) (M N : Nat) (hMN : N ≤ M := by decide)
    (hbound : M < 2 ^ 64 := by decide) :
    stackAt sp M = stackAt sp N ∗ memRegion (sp - BitVec.ofNat 64 M) (M - N) := by
  have h1 : M = N + (M - N) := (Nat.add_sub_of_le hMN).symm
  have h2 := ProofLib.stackAt_split_bottom sp N (M - N) (by omega)
  rw [← h1] at h2
  rw [h2, sepConj_comm]

/-! ## Block-`518` Basic-Block Steppers -/

set_option maxHeartbeats 800000 in
theorem step_2114_to_2160_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
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
       chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
       chunks104_6QWAt (ptr' + len * 104#64) d0 d1 d2 d3 d4 d5 dw6 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x980#64) ↦₆₄ ptr') ∗
          ((g.q + 0x988#64) ↦₆₄ (len + 1#64)) ∗
          chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
          chunks104_6QWAt (ptr' + len * 104#64) q0 q1 q2 q3 q4 q5 w6 ∗
          A.pool lim st s1) ∧
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
  wp_steps_sync_518 ext ((blkPl_518).base + 0x2160#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩
  rw [chunks104_6QWAt_read_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_eq_rc (ptr' + len * 104#64) q0 q1 q2 q3 q4 q5 w6]
  sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem step_2310_to_2114_of_ne_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
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
       chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
       chunks104_6QWAt (g.q + 0xa90#64) d0 d1 d2 d3 d4 d5 dw6 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x978#64) ↦₆₄ cap) ∗
          ((g.q + 0x988#64) ↦₆₄ len) ∗
          chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
          chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
          A.pool lim st s1) ∧
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
  wp_steps_sync_518 ext ((blkPl_518).base + 0x2114#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩
  rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6]
  sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem step_2310_to_growOne_of_eq_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
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
       chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
       chunks104_6QWAt (g.q + 0xa90#64) d0 d1 d2 d3 d4 d5 dw6 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0x978#64) ↦₆₄ cap) ∗
          ((g.q + 0x988#64) ↦₆₄ cap) ∗
          chunks104_6QWAt (g.q + 0xbf0#64) q0 q1 q2 q3 q4 q5 w6 ∗
          chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
          A.pool lim st s1) ∧
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
  wp_steps_sync_518 ext (lsmpl.base 43)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq ?_,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩
  rw [chunks104_6QWAt_read_bf0_eq_rc g.q q0 q1 q2 q3 q4 q5 w6,
      chunks104_6QWAt_write_a90_eq_rc g.q q0 q1 q2 q3 q4 q5 w6]
  sep_ac_rfl

set_option maxHeartbeats 800000 in
theorem step_234c_to_2114_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
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
      ((blkPl_518).base + 0x2114#64) s (A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st s1) ∧
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
  wp_steps_sync_518 ext ((blkPl_518).base + 0x2114#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  exact ⟨Entails.of_eq (sepConj_emp _),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

/-! ## Shared Tail (`+0x2114 → +0x2160`) -/

def recv2114HeapPlacedBudget {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (rest : List (BitVec 8)) (v : SSGQ)
    (cap' ptr' : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) (H_c : SepProp) :
    SepProp :=
  overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    ((g.q + 0x978#64) ↦₆₄ cap') ∗
    ((g.q + 0x980#64) ↦₆₄ ptr') ∗
    ((g.q + 0x988#64) ↦₆₄ BitVec.ofNat 64 v.base.recv.length) ∗
    A.live ptr' (cap'.toNat * 104) 8 ∗
    arrayAt (fun c' a => prostChainGAt A.repAlloc a c') 104 ptr' v.base.recv ∗
    memRegion (ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64) 104 ∗
    memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
      ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
    prostSSGQRest A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
    H_c ∗
    memRegion (g.q + 0xaf8#64) 240 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st s

set_option maxHeartbeats 800000 in
theorem step_from_2114_to_2160_full_pl_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (cap' ptr' : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) (H_c : SepProp)
    {Qp : State → SepProp → Prop}
    (hlt : v.base.recv.length < cap'.toNat)
    (hcap_lt : cap'.toNat * 104 < 2 ^ 63)
    (hptr : ptr' ≠ 0#64)
    (hmov_c : ∀ b : BitVec 64,
      (chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H_c) ⊢ prostChainGAt A.repAlloc b c)
    (hregs : OverDecRegsPlaced ext s0 g 0x2114#64 s)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 v.base.recv.length) :
    SepWPp (lsProg_518 ext)
        ((blkPl_518).base + 0x2160#64) s
      (recv2114HeapPlacedBudget A lim st s g rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapPlBudget A lim st sf g rest (v.apply (.base (.recv c)))))
      Qp := by
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  set dst : BitVec 64 := ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64
  let F_2114 : SepProp :=
    overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    ((g.q + 0x978#64) ↦₆₄ cap') ∗
    A.live ptr' (cap'.toNat * 104) 8 ∗
    arrayAt (fun c' a => prostChainGAt A.repAlloc a c') 104 ptr' v.base.recv ∗
    memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
      ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
    prostSSGQRest A.repAlloc (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    H_c ∗
    memRegion (g.q + 0xaf8#64) 240 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX
  have hsplit : recv2114HeapPlacedBudget A lim st s g rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c =
      (∃∗ d0 : BitVec 128, ∃∗ d1 : BitVec 128, ∃∗ d2 : BitVec 128,
       ∃∗ d3 : BitVec 128, ∃∗ d4 : BitVec 128, ∃∗ d5 : BitVec 128,
       ∃∗ dw6 : BitVec 64,
        ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ BitVec.ofNat 64 v.base.recv.length) ∗
        chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        chunks104_6QWAt dst d0 d1 d2 d3 d4 d5 dw6 ∗
        A.pool lim st s) ∗ F_2114 := by
    unfold recv2114HeapPlacedBudget F_2114
    rw [show ptr' + BitVec.ofNat 64 v.base.recv.length * 104#64 = dst from rfl,
        memRegion104_eq_exists_chunks104_6QWAt_rc dst]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply congrArg sepExists; funext _)
    sep_ac_rfl
  rw [hsplit]
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  have hstep := step_2114_to_2160_placed_budget A lim st ext s g ptr'
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
  have hss := prostSSGQAt_fold_apply_recv_ext A.repAlloc g.q cap' ptr' v c hlt hcap_lt hptr
  simp only [A.repAlloc_live_norm] at hss
  have ha90 := memRegion344_a90_join_rc g.q q0 q1 q2 q3 q4 q5 w6
  let F_keep : SepProp :=
    overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
    memRegion (g.q + 0xa88#64) 8 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st sf
  have h1 :
      (((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        chunks104_6QWAt dst q0 q1 q2 q3 q4 q5 w6 ∗
        A.pool lim st sf) ∗ F_2114 ⊢
      (((g.q + 0x978#64) ↦₆₄ cap') ∗ ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A.repAlloc a c') 104 ptr' v.base.recv ∗
        prostChainGAt A.repAlloc dst c ∗
        memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
        prostSSGQRest A.repAlloc (g.q + 0x930#64) v) ∗
      (chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
        memRegion (g.q + 0xaf8#64) 240) ∗
      F_keep := by
    refine Entails.trans (Q := (chunks104_6QWAt dst q0 q1 q2 q3 q4 q5 w6 ∗ H_c) ∗
      (((g.q + 0x978#64) ↦₆₄ cap') ∗ ((g.q + 0x980#64) ↦₆₄ ptr') ∗
        ((g.q + 0x988#64) ↦₆₄ (BitVec.ofNat 64 v.base.recv.length + 1#64)) ∗
        A.live ptr' (cap'.toNat * 104) 8 ∗
        arrayAt (fun c' a => prostChainGAt A.repAlloc a c') 104 ptr' v.base.recv ∗
        memRegion (ptr' + BitVec.ofNat 64 ((v.base.recv.length + 1) * 104))
          ((cap'.toNat - (v.base.recv.length + 1)) * 104) ∗
        prostSSGQRest A.repAlloc (g.q + 0x930#64) v ∗
        (chunks104_6QWAt (g.q + 0xa90#64) q0 q1 q2 q3 q4 q5 w6 ∗
          memRegion (g.q + 0xaf8#64) 240) ∗
        F_keep))
      (Entails.of_eq (by unfold F_2114 F_keep; sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left hc_dst) (Entails.of_eq (by sep_ac_rfl))
  refine Entails.trans h1 ?_
  refine Entails.trans (sepConj_mono hss (sepConj_mono ha90 (Entails.refl F_keep))) ?_
  exact Entails.of_eq (by unfold overDecHeapPlBudget F_keep; sep_ac_rfl)

abbrev toPrevDecG (g : Chain3OverDecG) : OverDecG :=
  ⟨g.q, g.r19, g.r20, g.r26, g.prevCap, g.prevPtr, g.encCap, g.encPtr, g.enc, g.sv⟩

theorem step_from_2114_to_2160_full_lscl_pl_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s0 s : State) (g : Chain3OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8))
    (cap' ptr' : BitVec 64) (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) (H_c : SepProp)
    {Qp : State → SepProp → Prop}
    (hlt : v.base.recv.length < cap'.toNat)
    (hcap_lt : cap'.toNat * 104 < 2 ^ 63)
    (hptr : ptr' ≠ 0#64)
    (hmov_c : ∀ b : BitVec 64,
      (chunks104_6QWAt b q0 q1 q2 q3 q4 q5 w6 ∗ H_c) ⊢ prostChainGAt A.repAlloc b c)
    (hregs : Chain3OverDecRegsPlaced ext s0 g 0x2114#64 s)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 v.base.recv.length) :
    SepWPp (lsProg_518 (Rust.withPanics ext))
        ((blkPl_518).base + 0x2160#64) s
      (recv2114HeapPlacedBudget A lim st s (toPrevDecG g) rest v cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c)
      (fun sf P_f => Chain3OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim st sf g rest (v.apply (.base (.recv c)))))
      Qp := by
  intro R hm hL
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hregs_pl : OverDecRegsPlaced (Rust.withPanics ext) s0 (toPrevDecG g) 0x2114#64 s :=
    ⟨hpc, hrun, hsp, hal, htr, hL, hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  obtain ⟨sf, hsteps, ⟨hpc', hrun', P_f, hmf, hregsf, hentf⟩ | hpan⟩ :=
    step_from_2114_to_2160_full_pl_budget A lim st (Rust.withPanics ext) s0 s (toPrevDecG g) v c rest
      cap' ptr' q0 q1 q2 q3 q4 q5 w6 H_c hlt hcap_lt hptr hmov_c hregs_pl hx22 R hm hL
  · rcases hregsf with ⟨hpc_f, hrun_f, hsp_f, hal_f, htr_f, _hLf,
      hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
    exact ⟨sf, hsteps, Or.inl ⟨hpc', hrun', P_f, hmf,
      ⟨⟨hpc_f, hrun_f, hsp_f, hal_f, htr_f, libsignalCodeLoaded_preserve_pl hcl hsteps,
        hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩,
       hentf⟩⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux
