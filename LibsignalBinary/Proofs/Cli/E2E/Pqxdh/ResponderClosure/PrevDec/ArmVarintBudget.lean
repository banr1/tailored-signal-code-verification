/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import ProofLib.Hoare.Safety
import ProofLib.Hoare.SubroutineOk
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Varint Arms (Tags 1, 5, 10, 11)

Total-correctness (`RustCliAllocBudget M`) verification of the varint field arms (tags 1, 5, 10, 11)
of inlined `SessionStructure::decode` on Block `518` (`lsProg_518 ext`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement lsmpl withLsCl withLsCodeLoaded
)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalProtoCodec (
  decodeVarint encodeVarint decodeVarint_encodeVarint
)
open CryptoVerification.LibsignalTripleRatchet.Prost (
  DecodeVarintSlowGhost sliceCursorAfter sliceCursorAt
)
open CryptoVerification.E2E.Record.DeserializeGeneral (SSG)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ SSGQ)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecG OverDecRegsCroPlaced OverDecRegsPlaced OverDecSavedRegsPl OverDecVarintField
  overDecArmOff overDecHeapExt overDecHeap_eq_varint_split_ext overDecHeap_eq_varint_unsplit_ext
  overDecVarintRestExt overDecWt payload_append_length_lt_of_suffix prostSSGQHead
  suffix_payload_of_suffix_enc
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (decodeVarint2StackX)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (
  DecodeVarintSliceEnv decodeVarintSliceEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverDecArmCroPlacedAt OverDecArmCroPlacedAtTR OverDecArmPlacedStmt OverDecArmPlacedStmtTR
  OverDecFieldEnv overDecFieldEnv_nil overDecHeapBudget overDecHeapBudget_eq_atState
  sepWPp_lift_cro_regs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5Budget (
  DecodeVarint2Env decodeVarint2SpecX
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5PlacedBudget (
  DecodeVarint5PlacedOkExtX decodeVarint5_placed_ok_ext_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)

private theorem truncate_32_setWidth_64 (v : BitVec 32) :
    (v.setWidth 64).truncate 32 = v := by bv_robdd

private theorem setWidth_32_setWidth_64 (v : BitVec 32) :
    (v.setWidth 64).setWidth 32 = v := by bv_robdd

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  State.readReg32 truncate_32_setWidth_64 setWidth_32_setWidth_64
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setPC_pre' (s : State) (pc : BitVec 64) :
    ({ s with pc := pc } : State).sp = s.sp := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_setPC_pre' (s : State) (m : Memory) (pc : BitVec 64) :
    ({ s with mem := m, pc := pc } : State).sp = s.sp := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setPC_pre' (s : State) (pc : BitVec 64) (r : Reg) :
    ({ s with pc := pc } : State).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_setPC_pre' (s : State) (m : Memory) (pc : BitVec 64) (r : Reg) :
    ({ s with mem := m, pc := pc } : State).readReg64 r = s.readReg64 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setPC_pre' (s : State) (pc : BitVec 64) (r : Reg) :
    ({ s with pc := pc } : State).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg32_setMem_setPC_pre' (s : State) (m : Memory) (pc : BitVec 64) (r : Reg) :
    ({ s with mem := m, pc := pc } : State).readReg32 r = s.readReg32 r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setPC_pre' (s : State) (pc : BitVec 64) (w : Width) (r : Reg) :
    ({ s with pc := pc } : State).readReg w r = s.readReg w r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem readReg_setMem_setPC_pre' (s : State) (m : Memory) (pc : BitVec 64)
    (w : Width) (r : Reg) :
    ({ s with mem := m, pc := pc } : State).readReg w r = s.readReg w r := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setPC_pre' (s : State) (pc : BitVec 64) :
    ({ s with pc := pc } : State).trace = s.trace := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_setPC_pre' (s : State) (m : Memory) (pc : BitVec 64) :
    ({ s with mem := m, pc := pc } : State).trace = s.trace := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setPC_pre' (s : State) (pc : BitVec 64) :
    calleeSavedVRegs ({ s with pc := pc } : State) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_setPC_pre' (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ({ s with mem := m, pc := pc } : State) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem status_setPC_pre' (s : State) (pc : BitVec 64) :
    ({ s with pc := pc } : State).status = s.status := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_setPC_pre' (s : State) (m : Memory) (pc : BitVec 64) :
    ({ s with mem := m, pc := pc } : State).status = s.status := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setPC_pre' (s : State) (pc : BitVec 64) :
    ({ s with pc := pc } : State).tpidrEl0 = s.tpidrEl0 := rfl

@[local arm64_norm ↓, local wp_norm ↓]
private theorem tpidrEl0_setMem_setPC_pre' (s : State) (m : Memory) (pc : BitVec 64) :
    ({ s with mem := m, pc := pc } : State).tpidrEl0 = s.tpidrEl0 := rfl

/-! ## Envelope and `SepWPp` Frame Combinators -/

private theorem decodeVarint2Env_encodeVarint_iff (val : BitVec 32) (rest : List (BitVec 8))
    (evs : List AllocEvent) :
    DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest) evs ↔ evs = [] := by
  unfold DecodeVarint2Env DecodeVarintSliceEnv decodeVarintSliceEvents
  simp [decodeVarint_encodeVarint (val.setWidth 64) rest]

private theorem fitsEnv_decodeVarint2_of_overDecField {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {fl : GenFieldQ} {val : BitVec 32} {rest : List (BitVec 8)}
    (hFit : FitsEnv M lim st (OverDecFieldEnv fl)) :
    FitsEnv M lim st (DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest)) := by
  intro evs hevs
  rw [decodeVarint2Env_encodeVarint_iff] at hevs
  subst hevs
  exact hFit [] (overDecFieldEnv_nil fl)

private theorem overDecSavedRegsPl_of_calleeSaved {g : OverDecG} {s1 s2 : State}
    (hs1 : OverDecSavedRegsPl g s1) (hcs : CalleeSavedPreserved s1 s2) :
    OverDecSavedRegsPl g s2 := by
  rcases hs1 with ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  rcases hcs with ⟨c19, c20, c21, _, _, c24, c25, c26, c27, c28, c29, cv⟩
  exact ⟨c19.trans h19, c20.trans h20, c26.trans h26, c21.trans h21, c24.trans h24,
    c25.trans h25, c27.trans h27, c28.trans h28, c29.trans h29, cv.trans hv⟩

private theorem SepWPp_bind_sepWP_frame_inv_vm {Inv : Memory → Prop}
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hInv : Inv s.mem)
    (hInv_kf : ∀ {m m' : Memory}, Inv m → m.KeepsFrozen m' → Inv m')
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => VmPreserved s sm ∧ (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, VmPreserved s sm → sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → Inv sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hvm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hvm hpc hrun hLm (hInv_kf hInv hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem SepWPp_ret_sepWP_frame_vm {prog : Program} {ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => VmPreserved s sf ∧ (P_step' ⊢ P_step_post) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hpost : ∀ sf : State, VmPreserved s sf → sf.pc = ret → sf.status = .Running →
      prog.CodeLoaded sf.mem → Q_regs sf → Q sf (P_step_post ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_step', hmf, hvm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, .inl ⟨hpc, hrun, P_step_post ∗ F, ?_,
    hpost sf hvm hpc hrun (hsteps.codeLoaded hL) hregs⟩⟩
  rw [sepConj_assoc]
  exact Satisfies.mono (sepConj_mono_left hent) hmf

private theorem subroutine_ok_lscl_of_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (h : DecodeVarint5PlacedOkExtX A lim ext) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hL
  have hpre' : s0.mem ⊨ (withLsCl lsmpl (decodeVarint2SpecX A lim)).pre x s0 ∗ R := by
    dsimp only [withLsCl, withLsCodeLoaded] at hpre ⊢
    exact hpre
  refine h.mono_outcome x R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨h1, h2, hpost⟩ | ⟨hpan, hpost⟩ | ⟨c, hc, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨h1, h2, ?_⟩
    dsimp only [withLsCl, withLsCodeLoaded] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

private theorem overDecVarint_call_decodeVarint5_plain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State}
    {bufRef slot ptr : BitVec 64} {val : BitVec 32} {rest : List (BitVec 8)}
    {F : SepProp} {Q : State → SepProp → Prop}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (decodeVarint2SpecX A lim))
    (hFit : FitsEnv M lim st (DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest)))
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
          A.pool lim st s2 ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_518 ext) ret s
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool lim st s ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
      Q (fun _ _ => False) := by
  intro R hm hL
  let x : DecodeVarintSlowGhost :=
    ⟨bufRef, slot, ptr, encodeVarint (val.setWidth 64) ++ rest⟩
  have hm' : s.mem ⊨ (decodeVarint2SpecX A lim).pre (x, st) s ∗ (F ∗ R) := by
    dsimp only [decodeVarint2SpecX, x]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hFit⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hDv5.no_fault_before_outcome (x, st) (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [decodeVarint2SpecX, x] at hpost
    rw [decodeVarint_encodeVarint (val.setWidth 64) rest] at hpost
    dsimp only at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0m, hx1m⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    have hpost_ex : sm.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sm) ∗
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          stackAt s.sp decodeVarint2StackX) ∗ (F ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost_ex
    obtain ⟨evs, hpost_ex⟩ := hpost_ex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ex
    rcases hpost_ex with ⟨hevs, hpost_ex⟩
    rw [decodeVarint2Env_encodeVarint_iff] at hevs
    subst hevs
    rw [M.stepEvents_nil] at hpost_ex
    have hpost_fin : sm.mem ⊨
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          A.pool lim st sm ∗ stackAt s.sp decodeVarint2StackX) ∗ F) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_ex
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hsteps.codeLoaded hL)
        hx0m hx1m (htrm.trans htr) R hpost_fin (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

private theorem overDecVarint_call_decodeVarint5_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {s0 s : State}
    {bufRef slot ptr : BitVec 64} {val : BitVec 32} {rest : List (BitVec 8)}
    {F : SepProp} {Q : State → SepProp → Prop}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hFit : FitsEnv M lim st (DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest)))
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
          A.pool lim st s2 ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
        Q (fun _ _ => False)) :
    SepWPp (lsProg_518 ext) ret s
      (((bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool lim st s ∗ stackAt s.sp decodeVarint2StackX) ∗ F)
      Q (fun _ _ => False) := by
  intro R hm hL
  let x : DecodeVarintSlowGhost :=
    ⟨bufRef, slot, ptr, encodeVarint (val.setWidth 64) ++ rest⟩
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)).pre (x, st) s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded, decodeVarint2SpecX, x]
    rw [sepConj_assoc, sepConj_left_comm _ (⌜LibsignalCodeLoaded _ _⌝), satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen, hFit⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  obtain ⟨sm, hsteps, hout, _⟩ :=
    hDv5.no_fault_before_outcome (x, st) (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · dsimp only [withLsCodeLoaded, decodeVarint2SpecX, x] at hpost
    rw [decodeVarint_encodeVarint (val.setWidth 64) rest] at hpost
    dsimp only at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hx0m, hx1m⟩, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htrm, hpost⟩
    have hpost_ex : sm.mem ⊨
        (∃∗ evs : List AllocEvent,
          ⌜DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest) evs⌝ ∗
          A.pool lim (M.stepEvents evs st) sm) ∗
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          stackAt s.sp decodeVarint2StackX) ∗ (F ∗ R)) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost_ex
    obtain ⟨evs, hpost_ex⟩ := hpost_ex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ex
    rcases hpost_ex with ⟨hevs, hpost_ex⟩
    rw [decodeVarint2Env_encodeVarint_iff] at hevs
    subst hevs
    rw [M.stepEvents_nil] at hpost_ex
    have hpost_fin : sm.mem ⊨
        (((bufRef ↦₆₄ slot) ∗
          sliceCursorAfter slot ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
          A.pool lim st sm ∗ stackAt s.sp decodeVarint2StackX) ∗ F) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost_ex
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm (hsteps.codeLoaded hL)
        hx0m hx1m (htrm.trans htr) R hpost_fin (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

/-! ## Pre-Call and Post-Call `VmPreserved` `SepWP` Lemmas -/

set_option maxHeartbeats 400000 in
theorem overDecVarint_pre_tag1_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    {s0 s : State} {g : OverDecG}
    (hregs : OverDecRegsPlaced ext s0 g 8636#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 8648#64 ∧
        OverDecSavedRegsPl g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  unfold lsProg_518
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm],
       Entails.of_eq rfl,
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
      s2.pc = (blkPl_518).base + 8648#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 8544#64) s2
        ((g.q + 0xa78#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          VmPreserved s2 sf ∧
          (P_f ⊢ ((g.q + 0xa78#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  unfold lsProg_518
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm],
       Entails.of_eq (by rw [hsp2]),
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
    (hregs : OverDecRegsPlaced ext s0 g 8680#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 8692#64 ∧
        OverDecSavedRegsPl g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  unfold lsProg_518
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm],
       Entails.of_eq rfl,
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
      s2.pc = (blkPl_518).base + 8692#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 8544#64) s2
        ((g.q + 0xa7c#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          VmPreserved s2 sf ∧
          (P_f ⊢ ((g.q + 0xa7c#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  unfold lsProg_518
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm],
       Entails.of_eq (by rw [hsp2]),
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
    (hregs : OverDecRegsPlaced ext s0 g 9128#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 9140#64 ∧
        OverDecSavedRegsPl g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  unfold lsProg_518
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm],
       Entails.of_eq rfl,
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
      s2.pc = (blkPl_518).base + 9140#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 8544#64) s2
        ((g.q + 0xa80#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          VmPreserved s2 sf ∧
          (P_f ⊢ ((g.q + 0xa80#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  unfold lsProg_518
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm],
       Entails.of_eq (by rw [hsp2]),
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
    (hregs : OverDecRegsPlaced ext s0 g 9104#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        VmPreserved s s1 ∧
        (P1 ⊢ ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 9116#64 ∧
        OverDecSavedRegsPl g s1) := by
  rcases hregs with ⟨hpc, hrun, hsp, hsp_align, htr, _hL,
    h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  have h29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := h29
  unfold lsProg_518
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun, arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm],
       Entails.of_eq rfl,
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
      s2.pc = (blkPl_518).base + 9116#64 →
      s2.status = .Running →
      s2.sp = g.q →
      (s2.sp &&& 15#64 == 0#64) = true →
      s2.trace = s0.trace →
      s2.readReg64 .x0 = 0#64 →
      s2.readReg64 .x1 = val.setWidth 64 →
      OverDecSavedRegsPl g s2 →
      SepWP (lsProg_518 ext)
        ((blkPl_518).base + 8544#64) s2
        ((g.q + 0xa84#64) ↦₃₂ oldVal)
        (fun sf P_f =>
          VmPreserved s2 sf ∧
          (P_f ⊢ ((g.q + 0xa84#64) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf) := by
  rintro s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2
    ⟨h19, h20, h26, h21, h24, h25, h27, h28, h29, hv⟩
  have hx0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
  have hx1' : s2.readReg64 (Reg.gpr 1#5) = val.setWidth 64 := hx1_2
  rw [← hsp2]
  unfold lsProg_518
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [arm64_norm, wp_norm]) (by simp only [hrun2, arm64_norm, wp_norm])
      ⟨by simp only [arm64_norm, wp_norm],
       Entails.of_eq (by rw [hsp2]),
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

/-! ## Shared Composition and Top-Level Varint Arm Theorems -/

set_option maxHeartbeats 600000 in
private theorem overDecArm_varint_inv_of_pre_post_placed_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Inv : Memory → Prop}
    {s0 s : State} {g : OverDecG} {v v' : SSGQ} {fl : GenFieldQ} {rest : List (BitVec 8)}
    {armOff retOff spOff : BitVec 64} {oldVal val : BitVec 32}
    {frameRest : SepProp}
    (hInv : Inv s.mem)
    (hInv_kf : ∀ {m m' : Memory}, Inv m → m.KeepsFrozen m' → Inv m')
    (hcall : ∀ {s1 : State} {ptr : BitVec 64} {F : SepProp} {Q : State → SepProp → Prop},
      Inv s1.mem →
      FitsEnv M lim st (DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest)) →
      s1.trace = s0.trace →
      s1.pc = lsmpl.base 515 → s1.status = .Running → s1.spAligned = true →
      s1.readReg64 .x0 = g.q + 0xbe8#64 →
      (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63 →
      (∀ s2 : State, s2.pc = s1.readReg64 .lr → s2.status = .Running →
        s2.sp = s1.sp → s2.spAligned = true → CalleeSavedPreserved s1 s2 →
        (lsProg_518 ext).CodeLoaded s2.mem →
        s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = val.setWidth 64 →
        s2.trace = s0.trace →
        SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s2
          ((((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
            sliceCursorAfter (g.q + 0x920#64) ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
            A.pool lim st s2 ∗ stackAt s1.sp decodeVarint2StackX) ∗ F)
          Q (fun _ _ => False)) →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s1
        ((((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          sliceCursorAt (g.q + 0x920#64) ptr (encodeVarint (val.setWidth 64) ++ rest) ∗
          A.pool lim st s1 ∗ stackAt s1.sp decodeVarint2StackX) ∗ F)
        Q (fun _ _ => False))
    (hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc)
    (hlen : g.enc.length < 2 ^ 62)
    (hFit : FitsEnv M lim st (OverDecFieldEnv fl))
    (hregs : OverDecRegsPlaced ext s0 g armOff s)
    (hsplit : overDecHeapBudget A lim st s g (encodeVarint (val.setWidth 64) ++ rest) v =
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAt (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) ∗
      A.pool lim st s ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ oldVal) ∗
      frameRest)
    (hunsplit : ∀ sf : State,
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length))
        (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool lim st sf ∗
      stackAt g.q decodeVarint2StackX ∗
      ((g.q + spOff) ↦₃₂ val) ∗
      frameRest =
      overDecHeapBudget A lim st sf g rest v')
    (hpre_step : SepWP (lsProg_518 ext)
      (lsmpl.base 515) s
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64))
      (fun s1 P1 =>
        VmPreserved s s1 ∧
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
          VmPreserved s2 sf ∧
          (P_f ⊢ ((g.q + spOff) ↦₃₂ val)) ∧
          sf.sp = g.q ∧ sf.trace = s0.trace ∧
          OverDecSavedRegsPl g sf)) :
    SepWPp (lsProg_518 ext)
      ((blkPl_518).base + 8544#64) s
      (overDecHeapBudget A lim st s g (encodeVarint (val.setWidth 64) ++ rest) v)
      (fun sf P_f => OverDecRegsPlaced ext s0 g 8544#64 sf ∧
        ∃ evs, OverDecFieldEnv fl evs ∧
          (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest v'))
      (fun _ _ => False) := by
  rcases hregs with ⟨_hpc, _hrun, hsp, hsp_align, _htr, _hL, _hsaved⟩
  have hlen_pay : (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63 :=
    payload_append_length_lt_of_suffix hsuf_pay hlen
  have hq_align : (g.q &&& 15#64 == 0#64) = true := by rwa [← hsp]
  have hFit_dv2 : FitsEnv M lim st (DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest)) :=
    fitsEnv_decodeVarint2_of_overDecField hFit
  rw [hsplit]
  refine SepWPp_bind_sepWP_frame_inv_vm hInv hInv_kf hpre_step rfl
    fun s1 hvm1 hpc1 hrun1 _hL1 hInv1 ⟨hsp1, htr1, hx0_1, hlr1, hsaved1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hq_align
  let curPtr := g.encPtr + BitVec.ofNat 64 (g.enc.length - (encodeVarint (val.setWidth 64) ++ rest).length)
  have hframe_eq :
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        (sliceCursorAt (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) ∗
          A.pool lim st s ∗
          stackAt g.q decodeVarint2StackX ∗
          ((g.q + spOff) ↦₃₂ oldVal) ∗
          frameRest) =
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) ∗
        A.pool lim st s1 ∗
        stackAt s1.sp decodeVarint2StackX) ∗
        (((g.q + spOff) ↦₃₂ oldVal) ∗ frameRest) := by
    rw [A.pool_transport lim st s s1 hvm1, hsp1]
    simp only [sepConj_assoc]
  rw [hframe_eq]
  refine hcall hInv1 hFit_dv2 htr1 hpc1 hrun1 hsp1_al hx0_1 hlen_pay
    fun s2 hpc2_lr hrun2 hsp2_1 _hsp2_al hcs2 _hL2 hx0_2 hx1_2 htr2 => ?_
  have hpc2 : s2.pc = (blkPl_518).base + retOff := hpc2_lr.trans hlr1
  have hsp2 : s2.sp = g.q := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hq_align
  have hsaved2 : OverDecSavedRegsPl g s2 := overDecSavedRegsPl_of_calleeSaved hsaved1 hcs2
  rw [hsp1]
  refine SepWPp_ret_sepWP_frame_vm
    (hpost_step s2 hpc2 hrun2 hsp2 hsp2_align htr2 hx0_2 hx1_2 hsaved2)
    (F := ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64) curPtr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
      A.pool lim st s2 ∗
      stackAt g.q decodeVarint2StackX ∗
      frameRest)
    (by dsimp only [curPtr]; sep_ac_rfl)
    fun sf hvm2 hpcf hrunf hLf ⟨hspf, htrf, hsavedf⟩ => ?_
  have hspf_align : (sf.sp &&& 15#64 == 0#64) = true := by rw [hspf]; exact hq_align
  refine ⟨⟨hpcf, hrunf, hspf, hspf_align, htrf, hLf, hsavedf⟩, [], overDecFieldEnv_nil fl, ?_⟩
  rw [M.stepEvents_nil]
  apply Entails.of_eq
  rw [← hunsplit sf, A.pool_transport lim st s2 sf hvm2]
  dsimp only [curPtr]
  sep_ac_rfl

set_option maxHeartbeats 600000 in
private theorem overDecArm_varint_inv_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m m' : Memory}, Inv m → m.KeepsFrozen m' → Inv m')
    (hcall : ∀ {st : M.σ} {s0 s1 : State} {g : OverDecG} {ptr : BitVec 64}
      {val : BitVec 32} {rest : List (BitVec 8)} {F : SepProp} {Q : State → SepProp → Prop},
      Inv s1.mem →
      FitsEnv M lim st (DecodeVarint2Env (encodeVarint (val.setWidth 64) ++ rest)) →
      s1.trace = s0.trace →
      s1.pc = lsmpl.base 515 → s1.status = .Running → s1.spAligned = true →
      s1.readReg64 .x0 = g.q + 0xbe8#64 →
      (encodeVarint (val.setWidth 64) ++ rest).length < 2 ^ 63 →
      (∀ s2 : State, s2.pc = s1.readReg64 .lr → s2.status = .Running →
        s2.sp = s1.sp → s2.spAligned = true → CalleeSavedPreserved s1 s2 →
        (lsProg_518 ext).CodeLoaded s2.mem →
        s2.readReg64 .x0 = 0#64 → s2.readReg64 .x1 = val.setWidth 64 →
        s2.trace = s0.trace →
        SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s2
          ((((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
            sliceCursorAfter (g.q + 0x920#64) ptr (encodeVarint (val.setWidth 64) ++ rest) rest ∗
            A.pool lim st s2 ∗ stackAt s1.sp decodeVarint2StackX) ∗ F)
          Q (fun _ _ => False)) →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s1
        ((((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          sliceCursorAt (g.q + 0x920#64) ptr (encodeVarint (val.setWidth 64) ++ rest) ∗
          A.pool lim st s1 ∗ stackAt s1.sp decodeVarint2StackX) ∗ F)
        Q (fun _ _ => False)) :
    ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
      Inv s.mem →
      OverDecVarintField fl → fl.Ok → fl.Fresh v →
      (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
      FitsEnv M lim st (OverDecFieldEnv fl) →
      OverDecRegsPlaced ext s0 g (overDecArmOff fl) s →
      s.readReg64 .x0 = overDecWt fl →
      s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
        (overDecHeapBudget A lim st s g (fl.payload ++ rest) v)
        (fun sf P_f => OverDecRegsPlaced ext s0 g 8544#64 sf ∧
          ∃ evs, OverDecFieldEnv fl evs ∧
            (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest (v.apply fl)))
        (fun _ _ => False) := by
  intro st s0 s g v fl rest hInv hP _hOk _hFresh hsuf hlen hFit hregs hx0 _hx22
  rcases fl with (_ | _)
  · rename_i fb
    rcases fb with (val | _ | _ | _ | val | _ | _ | _)
    · have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
        suffix_payload_of_suffix_enc hsuf
      refine overDecArm_varint_inv_of_pre_post_placed_ext hInv hInv_kf hcall hsuf_pay hlen hFit hregs
        (spOff := 0xa78#64) (oldVal := v.base.version) (val := val)
        (frameRest :=
          ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
          ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
          ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
          overDecVarintRestExt A.repAlloc g v (encodeVarint (val.setWidth 64) ++ rest).length)
        (by
          rw [overDecHeapBudget_eq_atState,
              overDecHeap_eq_varint_split_ext (A := A.atState lim st s) g v hsuf_pay]
          dsimp only [RustCliAllocBudget.atState_pool]
          sep_ac_rfl)
        (fun sf => by
          rw [overDecHeapBudget_eq_atState,
              ← overDecHeap_eq_varint_unsplit_ext (A := A.atState lim st sf) g
                (v.apply (.base (.version val))) hsuf_pay]
          dsimp only [SSGQ.apply, SSG.apply, RustCliAllocBudget.atState_pool]
          have hrest : overDecVarintRestExt A.repAlloc g v
              (encodeVarint (val.setWidth 64) ++ rest).length =
              overDecVarintRestExt (A.atState lim st sf) g (v.apply (.base (.version val)))
                (encodeVarint (val.setWidth 64) ++ rest).length := rfl
          rw [hrest]
          sep_ac_rfl)
        (overDecVarint_pre_tag1_placed hregs hx0)
        overDecVarint_post_tag1_placed
    · cases hP
    · cases hP
    · cases hP
    · have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
        suffix_payload_of_suffix_enc hsuf
      refine overDecArm_varint_inv_of_pre_post_placed_ext hInv hInv_kf hcall hsuf_pay hlen hFit hregs
        (spOff := 0xa7c#64) (oldVal := v.base.prevCounter) (val := val)
        (frameRest :=
          ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
          ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
          ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
          overDecVarintRestExt A.repAlloc g v (encodeVarint (val.setWidth 64) ++ rest).length)
        (by
          rw [overDecHeapBudget_eq_atState,
              overDecHeap_eq_varint_split_ext (A := A.atState lim st s) g v hsuf_pay]
          dsimp only [RustCliAllocBudget.atState_pool]
          sep_ac_rfl)
        (fun sf => by
          rw [overDecHeapBudget_eq_atState,
              ← overDecHeap_eq_varint_unsplit_ext (A := A.atState lim st sf) g
                (v.apply (.base (.prevCounter val))) hsuf_pay]
          dsimp only [SSGQ.apply, SSG.apply, RustCliAllocBudget.atState_pool]
          have hrest : overDecVarintRestExt A.repAlloc g v
              (encodeVarint (val.setWidth 64) ++ rest).length =
              overDecVarintRestExt (A.atState lim st sf) g (v.apply (.base (.prevCounter val)))
                (encodeVarint (val.setWidth 64) ++ rest).length := rfl
          rw [hrest]
          sep_ac_rfl)
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
    refine overDecArm_varint_inv_of_pre_post_placed_ext hInv hInv_kf hcall hsuf_pay hlen hFit hregs
      (spOff := 0xa80#64) (oldVal := v.ext.remReg) (val := val)
      (frameRest :=
        ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((g.q + 0xa84#64) ↦₃₂ v.ext.locReg) ∗
        overDecVarintRestExt A.repAlloc g v (encodeVarint (val.setWidth 64) ++ rest).length)
      (by
        rw [overDecHeapBudget_eq_atState,
            overDecHeap_eq_varint_split_ext (A := A.atState lim st s) g v hsuf_pay]
        dsimp only [RustCliAllocBudget.atState_pool]
        sep_ac_rfl)
      (fun sf => by
        rw [overDecHeapBudget_eq_atState,
            ← overDecHeap_eq_varint_unsplit_ext (A := A.atState lim st sf) g
              (v.apply (.remReg val)) hsuf_pay]
        dsimp only [SSGQ.apply, RustCliAllocBudget.atState_pool]
        have hrest : overDecVarintRestExt A.repAlloc g v
            (encodeVarint (val.setWidth 64) ++ rest).length =
            overDecVarintRestExt (A.atState lim st sf) g (v.apply (.remReg val))
              (encodeVarint (val.setWidth 64) ++ rest).length := rfl
        rw [hrest]
        sep_ac_rfl)
      (overDecVarint_pre_tag10_placed hregs hx0)
      overDecVarint_post_tag10_placed
  · rename_i val
    have hsuf_pay : (encodeVarint (val.setWidth 64) ++ rest) <:+ g.enc :=
      suffix_payload_of_suffix_enc hsuf
    refine overDecArm_varint_inv_of_pre_post_placed_ext hInv hInv_kf hcall hsuf_pay hlen hFit hregs
      (spOff := 0xa84#64) (oldVal := v.ext.locReg) (val := val)
      (frameRest :=
        ((g.q + 0xa78#64) ↦₃₂ v.base.version) ∗
        ((g.q + 0xa7c#64) ↦₃₂ v.base.prevCounter) ∗
        ((g.q + 0xa80#64) ↦₃₂ v.ext.remReg) ∗
        overDecVarintRestExt A.repAlloc g v (encodeVarint (val.setWidth 64) ++ rest).length)
      (by
        rw [overDecHeapBudget_eq_atState,
            overDecHeap_eq_varint_split_ext (A := A.atState lim st s) g v hsuf_pay]
        dsimp only [RustCliAllocBudget.atState_pool]
        sep_ac_rfl)
      (fun sf => by
        rw [overDecHeapBudget_eq_atState,
            ← overDecHeap_eq_varint_unsplit_ext (A := A.atState lim st sf) g
              (v.apply (.locReg val)) hsuf_pay]
        dsimp only [SSGQ.apply, RustCliAllocBudget.atState_pool]
        have hrest : overDecVarintRestExt A.repAlloc g v
            (encodeVarint (val.setWidth 64) ++ rest).length =
            overDecVarintRestExt (A.atState lim st sf) g (v.apply (.locReg val))
              (encodeVarint (val.setWidth 64) ++ rest).length := rfl
        rw [hrest]
        sep_ac_rfl)
      (overDecVarint_pre_tag11_placed hregs hx0)
      overDecVarint_post_tag11_placed
  · cases hP
  · cases hP
  · cases hP

/-- Plain (`OverDecRegsPlaced`, no `LibsignalCodeRoLoaded`) budget-threaded varint arms on `lsProg_518 ext`. -/
theorem overDecArm_varint_placed_ext_of_dv5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (decodeVarint2SpecX A lim)) :
    ∀ (st : M.σ) (s0 s : State) (g : OverDecG) (v : SSGQ) (fl : GenFieldQ) (rest : List (BitVec 8)),
      OverDecVarintField fl → fl.Ok → fl.Fresh v →
      (fl.enc ++ rest) <:+ g.enc → g.enc.length < 2 ^ 62 →
      FitsEnv M lim st (OverDecFieldEnv fl) →
      OverDecRegsPlaced ext s0 g (overDecArmOff fl) s →
      s.readReg64 .x0 = overDecWt fl →
      s.readReg64 .x22 = BitVec.ofNat 64 (fl.tag * 8 + (overDecWt fl).toNat) →
      SepWPp (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
        (overDecHeapBudget A lim st s g (fl.payload ++ rest) v)
        (fun sf P_f => OverDecRegsPlaced ext s0 g 8544#64 sf ∧
          ∃ evs, OverDecFieldEnv fl evs ∧
            (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest (v.apply fl)))
        (fun _ _ => False) := by
  intro st s0 s g v fl rest
  exact overDecArm_varint_inv_placed (Inv := fun _ => True)
    (fun _ _ => trivial)
    (fun _ => overDecVarint_call_decodeVarint5_plain hDv5)
    st s0 s g v fl rest trivial

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded varint arms from `withLsCodeLoaded`
`decodeVarint2SpecX` on `lsmpl.base 515`. -/
theorem overDecArm_varint_cro_placed_of_dv5_lscl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDv5 : subroutine_ok (lsProg_518 ext) (lsmpl.base 515)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim))) :
    OverDecArmCroPlacedAtTR A lim ext OverDecVarintField := by
  intro st s0 s g v fl rest hP hOk hFresh hsuf hlen hFit ⟨hcro, hregs⟩ hx0 hx22
  refine sepWPp_lift_cro_regs hcro ?_
  exact overDecArm_varint_inv_placed (Inv := LibsignalCodeLoaded lsmpl)
    (fun hcl hkf => hcl.of_keepsFrozen hkf)
    (fun hcl => overDecVarint_call_decodeVarint5_lscl hDv5 hcl)
    st s0 s g v fl rest hcro.1 hP hOk hFresh hsuf hlen hFit hregs hx0 hx22

theorem overDecArm_varint_cro_placed_of_dv5_cl [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hDv5 : DecodeVarint5PlacedOkExtX A lim ext) :
    OverDecArmCroPlacedAtTR A lim ext OverDecVarintField :=
  overDecArm_varint_cro_placed_of_dv5_lscl (subroutine_ok_lscl_of_cl hDv5)

theorem overDecArm_varint_placed_of_dv5 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hDv5 : ∀ ext, DecodeVarint5PlacedOkExtX A lim ext) :
    OverDecArmPlacedStmtTR A lim OverDecVarintField :=
  fun ext => overDecArm_varint_cro_placed_of_dv5_cl (hDv5 ext)

alias overDecArm_varint_cli_placed_of_dv5 := overDecArm_varint_placed_of_dv5

theorem overDecArm_varint_placed_of_dv5_plain [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hDv5 : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 515) (decodeVarint2SpecX A lim)) :
    OverDecArmPlacedStmtTR A lim OverDecVarintField := by
  intro ext st s0 s g v fl rest hP hOk hFresh hsuf hlen hFit ⟨hcro, hregs⟩ hx0 hx22
  exact sepWPp_lift_cro_regs hcro
    (overDecArm_varint_placed_ext_of_dv5 (hDv5 ext) st s0 s g v fl rest
      hP hOk hFresh hsuf hlen hFit hregs hx0 hx22)

/-- Fixed-`ext` `LibsignalCodeRoLoaded` budget-threaded varint arms discharged directly from
`AllocContractsPlaced M A lim ext`. -/
theorem overDecArm_varint_cro_placed_of_alloc [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hAlloc : AllocContractsPlaced M A lim ext) :
    OverDecArmCroPlacedAtTR A lim ext OverDecVarintField :=
  overDecArm_varint_cro_placed_of_dv5_cl (decodeVarint5_placed_ok_ext_x hAlloc)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarintBudget
