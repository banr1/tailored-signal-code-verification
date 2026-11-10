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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecv
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.EntryPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.HeadPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.ArmChainHeap
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Helpers for Top-Level `SessionStructure::decode`

Provides the Block-`516` budget-threaded `chainMerge3RawSpecW` contract, tag-6 and tag-7 allocation
envelope subsumption lemmas, no-panic `SepWPp` call framing combinators, and budget-synchronized
Block-`518` entry, loop-head, and chain-arm segments.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux

open Arm64 ProofLib SepProp
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)
open CryptoGames.LibsignalSession (maxReceiverChains)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc arrayAt vecAt vecBuf vecHeader vecOf vecU8 vecU8At)
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAfter sliceCursorAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  LibsignalCodeRoLoaded extract_withLsCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.E2E.Record.DeserializeGeneral (
  ChainG ChainMergeGenGhost GenField SSG prostChainGAt prostSSGAt
)
open Symbolic.Swarm.TRREF.B3DeserQ (ExtraGQ GenFieldQ SSGQ prostSSGQAt prostSSGQAt_empty)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3 (
  chain3GAt chainMerge3StackX
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecG OverDecRegsPlaced OverDecSavedRegs
  memRegion128_bf0_split_80_24_24 memRegion80_bf0_eq_cells10
  overDecHeapExt overDecRecvPostMergeHeapExt overDecScratchPre overDecStackX
  overPrevElemAtExt overPrevElemRestExt
  sliceCursorAfter_split_of_suffix_recv sliceCursorAfter_unsplit_of_suffix_recv
  stackAt_overDecStackX_eq_chainMerge3StackX
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsXBudget (
  ChainMergeGenEnv boundedRustEvs_growOne104Env fitsEnv_step_boundedRustEvs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudget (
  OverDecRecvSegBEnv overDecRecvPostMergeHeapPlBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverDecEntryPlacedStmt OverDecFieldEnv OverDecHeadConsPlacedStmt OverDecHeadNilPlacedStmt
  overDecHeapBudget overPrevElemAtBudget
)

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
  refine ProofLib.SepWP.done
    (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm])
    (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm])
    fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## 1. Block-`516` (`lsmpl.base 516`) Budget-Threaded `message::merge<Chain>` Contract -/

/-- Budget-threaded raw contract of handshake `prost::encoding::message::merge::<Chain, &mut &[u8]>`
(Block `516`, `lsmpl.base 516`) at `chainMerge3StackX` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def chainMerge3RawSpecW {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (ChainMergeGenGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜(s.readReg64 .x0).setWidth 8 = 2#8 ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.bufRef ∧
      x.c.Ok ∧ (x.c.payload ++ x.tail).length < 2 ^ 62 ∧
      FitsEnv M lim st (ChainMergeGenEnv x)⌝ ∗
      chain3GAt A.repAlloc x.a ChainG.empty ∗ (x.bufRef ↦₆₄ x.slot) ∗
      sliceCursorAt x.slot x.ptr (x.c.payload ++ x.tail) ∗
      A.pool lim st s ∗ stackAt s.sp chainMerge3StackX
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64 ∧ ChainMergeGenEnv x evs⌝ ∗
        prostChainGAt A.repAlloc x.a x.c ∗ (x.bufRef ↦₆₄ x.slot) ∗
        sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) x.tail ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainMerge3StackX

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for `message::merge<Chain>`
(Block `516`, `lsmpl.base 516`) on `lsProg_518 ext` under `withLsCodeRoLoaded lsmpl`. -/
def ChainMerge5CroPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 516)
    (withLsCodeRoLoaded lsmpl (chainMerge3RawSpecW A lim))

/-! ## 2. Tag-6 & Tag-7 Allocation-Envelope Subsumption Lemmas -/

theorem sender_enc_length (c : ChainG) :
    (GenFieldQ.base (.sender c)).enc.length = c.payload.length + 1 := by
  have hk : (encodeKey 6 WireType.lengthDelimited).length = 1 := by decide
  change (encodeKey 6 WireType.lengthDelimited ++ c.payload).length = c.payload.length + 1
  rw [List.length_append, hk]
  omega

theorem recv_enc_length (c : ChainG) :
    (GenFieldQ.base (.recv c)).enc.length = c.payload.length + 1 := by
  have hk : (encodeKey 7 WireType.lengthDelimited).length = 1 := by decide
  change (encodeKey 7 WireType.lengthDelimited ++ c.payload).length = c.payload.length + 1
  rw [List.length_append, hk]
  omega

theorem overDecFieldEnv_of_sender_chainMergeGen {x : ChainMergeGenGhost} {evs : List AllocEvent}
    (hevs : ChainMergeGenEnv x evs) :
    OverDecFieldEnv (.base (.sender x.c)) evs := by
  have hlen := sender_enc_length x.c
  unfold OverDecFieldEnv
  unfold ChainMergeGenEnv at hevs
  exact BoundedRustEvs.mono (by omega) (by omega) hevs

theorem fitsEnv_chainMergeGen_of_sender {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : ChainMergeGenGhost}
    (hFit : FitsEnv M lim st (OverDecFieldEnv (.base (.sender x.c)))) :
    FitsEnv M lim st (ChainMergeGenEnv x) :=
  fun evs hevs => hFit evs (overDecFieldEnv_of_sender_chainMergeGen hevs)

theorem boundedRustEvs_overDecRecvSegB {recvLen : Nat} {evs : List AllocEvent}
    (hfresh : recvLen < maxReceiverChains)
    (hevs : OverDecRecvSegBEnv recvLen evs) :
    BoundedRustEvs 1 832 evs := by
  rcases hevs with rfl | heq
  · exact BoundedRustEvs.nil 1 832
  · have h5 : maxReceiverChains = 5 := rfl
    let cap : BitVec 64 := BitVec.ofNat 64 recvLen
    have hcap : cap.toNat = recvLen := by
      dsimp [cap]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hle832 : max (2 * cap.toNat) 4 * 104 ≤ 832 := by omega
    have hmax : max (2 * cap.toNat) 4 * 104 ≤ MallocngMaxAllocSize := by
      unfold MallocngMaxAllocSize; omega
    exact BoundedRustEvs.mono (Nat.le_refl 1) hle832 (boundedRustEvs_growOne104Env hmax heq)

theorem fitsEnv_chainMergeGen_of_recv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : ChainMergeGenGhost}
    (hFit : FitsEnv M lim st (OverDecFieldEnv (.base (.recv x.c)))) :
    FitsEnv M lim st (ChainMergeGenEnv x) := by
  have hlen := recv_enc_length x.c
  intro evs hevs
  unfold ChainMergeGenEnv at hevs
  exact hFit evs (BoundedRustEvs.mono (by omega) (by omega) hevs)

theorem fitsEnv_segB_of_recv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {x : ChainMergeGenGhost} {recvLen : Nat} {evs₁ : List AllocEvent}
    (hfresh : recvLen < maxReceiverChains)
    (hevs₁ : ChainMergeGenEnv x evs₁)
    (hFit : FitsEnv M lim st (OverDecFieldEnv (.base (.recv x.c)))) :
    FitsEnv M lim (M.stepEvents evs₁ st) (OverDecRecvSegBEnv recvLen) := by
  have hlen := recv_enc_length x.c
  unfold OverDecFieldEnv at hFit
  unfold ChainMergeGenEnv at hevs₁
  have hstep : FitsEnv M lim (M.stepEvents evs₁ st) (BoundedRustEvs 1 832) :=
    fitsEnv_step_boundedRustEvs hevs₁ (by omega) (by omega) (by omega) hFit
  exact fun evs₂ hevs₂ => hstep evs₂ (boundedRustEvs_overDecRecvSegB hfresh hevs₂)

theorem overDecFieldEnv_of_recv_chain_segB {x : ChainMergeGenGhost} {recvLen : Nat}
    {evs₁ evs₂ : List AllocEvent}
    (hfresh : recvLen < maxReceiverChains)
    (hevs₁ : ChainMergeGenEnv x evs₁)
    (hevs₂ : OverDecRecvSegBEnv recvLen evs₂) :
    OverDecFieldEnv (.base (.recv x.c)) (evs₁ ++ evs₂) := by
  have hlen := recv_enc_length x.c
  unfold OverDecFieldEnv
  unfold ChainMergeGenEnv at hevs₁
  have hb₂ := boundedRustEvs_overDecRecvSegB hfresh hevs₂
  exact BoundedRustEvs.mono (by omega) (Nat.max_le.mpr ⟨by omega, by omega⟩)
    (BoundedRustEvs.append hevs₁ hb₂)

/-! ## 3. Polymorphic `SepWPp` Framing & No-Panic Call Combinators -/

theorem SepWPp_weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (h : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

theorem SepWPp_bind_sepWP_frame {prog : Program} {mid ret : BitVec 64} {s : State}
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

theorem SepWPp_bind_sepWP_frame_cro [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State}
    {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      prog.CodeLoaded sm.mem → LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
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
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun hLm (hcro.of_keepsFrozen hsteps.keepsFrozen) hregs R hmm' hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem SepWPp_ret_sepWP_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hstep : SepWP prog ret s P_step
      (fun sf P_step' => (P_step' ⊢ P_step_post sf) ∧ Q_regs sf))
    (hP : P = P_step ∗ F)
    (hpost : ∀ sf : State, sf.pc = ret → sf.status = .Running →
      prog.CodeLoaded sf.mem → Q_regs sf → Q sf (P_step_post sf ∗ F)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_step', hmf, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  refine ⟨sf, hsteps, .inl ⟨hpc, hrun, P_step_post sf ∗ F, ?_,
    hpost sf hpc hrun (hsteps.codeLoaded hL) hregs⟩⟩
  rw [sepConj_assoc]
  exact Satisfies.mono (sepConj_mono_left hent) hmf

theorem SepWPp_call_frame_cro_noPanic [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      prog.CodeLoaded sm.mem → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q (fun _ _ => False)) :
    SepWPp prog ret s P Q (fun _ _ => False) := by
  have hstep : SepWP prog ret_pc s P
      (fun sm P_m => (P_m ⊢ spec.post x s sm ∗ F) ∧ sm.sp = s.sp ∧ CalleeSavedPreserved s sm) := by
    refine SepWP.call_subroutine_frame hcall hpc hrun hsp hlr
      (fun R' hm' => ?_)
      (fun R' sf _ hp => by
        dsimp only [withLsCodeRoLoaded] at hp
        rw [hpan_false] at hp
        exact not_satisfies_false_sepConj hp)
      (fun R' code sf _ he => by
        dsimp only [withLsCodeRoLoaded] at he
        rw [hexit_false] at he
        exact not_satisfies_false_sepConj he)
      (fun sf hpcm hrunm hspm hcsm => SepWP.done hpcm hrunm ⟨Entails.refl _, hspm, hcsm⟩)
      (fun R' sf _ ho => by
        dsimp only [withLsCodeRoLoaded] at ho
        rw [hoom_false] at ho
        exact False.elim (not_satisfies_false_sepConj ho))
    dsimp only [withLsCodeRoLoaded]
    rw [hspec]
    have h1 : s.mem ⊨ ⌜φ⌝ ∗ (⌜LibsignalCodeRoLoaded lsmpl s.mem⌝ ∗ (T ∗ (F ∗ R'))) := by
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
      exact ⟨hφ, hcro, hm'⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) h1
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hspm, hcsm⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  have hpost : sm.mem ⊨ (spec.post x s sm ∗ F) ∗ R :=
    Satisfies.mono (sepConj_mono_left hent) hmm
  have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
  have hLm : prog.CodeLoaded sm.mem := hsteps.codeLoaded hL
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpcm hrunm hspm hsp_alm hcsm hLm
      (hcro.of_keepsFrozen hsteps.keepsFrozen) R hpost hLm
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

abbrev toChain3GTop (g : OverDecG) :
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.OverDecG :=
  ⟨g.q, g.r19, g.r20, g.r26, g.prevCap, g.prevPtr, g.encCap, g.encPtr, g.enc, g.sv⟩

/-! ## 4. Budget-Synchronized Entry (`+0x1ee8 → +0x216c`) & Loop Head (`+0x2160`) -/

private theorem enc_len_ofNat64_ne_zero {enc : List (BitVec 8)}
    (hne : enc ≠ []) (hlen : enc.length < 2 ^ 62) :
    BitVec.ofNat 64 enc.length ≠ 0#64 := by
  have hpos : 0 < enc.length := List.length_pos_iff.mpr hne
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero,
      Nat.mod_eq_of_lt (by omega : enc.length < 2 ^ 64)] at hnat
  omega

private theorem overPrevElemAt_entails_of_ne_nil {A : RustAlloc}
    {prevCap prevPtr encCap encPtr : BitVec 64} {enc : List (BitVec 8)}
    (hne : enc ≠ []) :
    overPrevElemAtExt A prevCap prevPtr encCap encPtr enc ⊢
      overPrevElemRestExt A prevCap prevPtr encCap encPtr enc ∗ (encPtr ↦ₛ enc) := by
  by_cases hcap : encCap = 0
  · have hpos : 0 < enc.length := List.length_pos_iff.mpr hne
    unfold overPrevElemAtExt vecU8At
    refine Entails.trans (Entails.of_eq (Q :=
      ⌜enc.length ≤ encCap.toNat ∧ encCap.toNat < 2 ^ 63 ∧ encPtr ≠ 0⌝ ∗
        (⌜1 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
          A.live prevPtr (prevCap.toNat * 24) 8 ∗
          vecHeader prevPtr encCap encPtr (BitVec.ofNat 64 enc.length) ∗
          (if encCap = 0 then emp else
            A.live encPtr encCap.toNat 1 ∗ (encPtr ↦ₛ enc) ∗
              memRegion (encPtr + BitVec.ofNat 64 enc.length) (encCap.toNat - enc.length)) ∗
          memRegion (prevPtr + 24#64) ((prevCap.toNat - 1) * 24))) (by sep_ac_rfl)) ?_
    refine Entails.pure_left fun hφ => False.elim ?_
    have hzero : encCap.toNat = 0 := by subst hcap; rfl
    omega
  · unfold overPrevElemAtExt overPrevElemRestExt vecU8At
    simp only [hcap, ↓reduceIte]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem SepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {F : SepProp} {Q Qp : State → SepProp → Prop}
    (h : ∀ x : α, SepWPp prog ret s (P x ∗ F) Q Qp) :
    SepWPp prog ret s ((∃∗ x : α, P x) ∗ F) Q Qp := by
  intro R hm hL
  rw [sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨x, hm⟩
  exact h x R hm hL

private theorem memRegion_succ8_entry (a : BitVec 64) (n : Nat) (hn : n < 2000) :
    memRegion a (n + 8) = (∃∗ w : BitVec 64, a ↦₆₄ w) ∗ memRegion (a + 8#64) n := by
  rw [Nat.add_comm n 8, memRegion_split a 8 n (by omega), ProofLib.memRegion_eight]

private def entryScratchCells (q : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
     w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : BitVec 64) : SepProp :=
  ((q + 0x920#64) ↦₆₄ w0) ∗ ((q + 0x928#64) ↦₆₄ w1) ∗
  ((q + 0x930#64) ↦₆₄ w2) ∗ ((q + 0x938#64) ↦₆₄ w3) ∗ ((q + 0x940#64) ↦₆₄ w4) ∗
  ((q + 0x948#64) ↦₆₄ w5) ∗ ((q + 0x950#64) ↦₆₄ w6) ∗ ((q + 0x958#64) ↦₆₄ w7) ∗
  ((q + 0x960#64) ↦₆₄ w8) ∗ ((q + 0x968#64) ↦₆₄ w9) ∗ ((q + 0x970#64) ↦₆₄ w10) ∗
  ((q + 0x978#64) ↦₆₄ w11) ∗ ((q + 0x980#64) ↦₆₄ w12) ∗ ((q + 0x988#64) ↦₆₄ w13) ∗
  ((q + 0x990#64) ↦₆₄ w14) ∗ ((q + 0x998#64) ↦₆₄ w15) ∗ ((q + 0x9a0#64) ↦₆₄ w16) ∗
  ((q + 0x9a8#64) ↦₆₄ w17) ∗ ((q + 0x9b0#64) ↦₆₄ w18) ∗ ((q + 0x9b8#64) ↦₆₄ w19) ∗
  ((q + 0x9c0#64) ↦₆₄ w20) ∗ ((q + 0xa28#64) ↦₆₄ w21) ∗ ((q + 0xa58#64) ↦₆₄ w22) ∗
  ((q + 0xa78#64) ↦₆₄ w23) ∗ ((q + 0xa80#64) ↦₆₄ w24) ∗ ((q + 0xbe8#64) ↦₆₄ w25)

private def entryScratchKeep (q : BitVec 64) : SepProp :=
  memRegion (q + 0x9c8#64) 96 ∗ memRegion (q + 0xa30#64) 40 ∗
  memRegion (q + 0xa60#64) 24 ∗ memRegion (q + 0xa88#64) 8 ∗
  memRegion (q + 0xa90#64) 344 ∗ memRegion (q + 0xbf0#64) 128

set_option maxHeartbeats 400000 in
private theorem overDecScratchPre_split (q : BitVec 64) :
    overDecScratchPre q =
      (∃∗ w25 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ w22 : BitVec 64,
       ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
       ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
       ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
       ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
       ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        entryScratchCells q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
          w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25) ∗
      entryScratchKeep q := by
  unfold overDecScratchPre entryScratchKeep
  rw [memRegion_split (q + 0x990#64) 56 200 (by decide),
      memRegion_split (q + 0x990#64 + 56#64) 96 104 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64) 8 96 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64) 40 56 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64) 8 48 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 24 (by decide),
      memRegion_split (q + 0x990#64 + 56#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64) 16 8 (by decide),
      memRegion_split (q + 0xbe8#64) 8 128 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 1
    simp (discharger := decide) only [memRegion_succ8_entry, ProofLib.memRegion_zero, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
  conv_lhs =>
    arg 2; arg 1; arg 1
    simp (discharger := decide) only [memRegion_succ8_entry, ProofLib.memRegion_zero, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
  rw [ProofLib.memRegion_eight (q + 0xa28#64),
      ProofLib.memRegion_eight (q + 0xa58#64),
      ProofLib.memRegion_eight (q + 0xbe8#64)]
  conv_lhs =>
    arg 2; arg 1; arg 2; arg 2; arg 2; arg 2; arg 2; arg 2; arg 1
    simp (discharger := decide) only [memRegion_succ8_entry, ProofLib.memRegion_zero, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
  unfold entryScratchCells
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat' (apply congrArg sepExists; funext _)
  sep_ac_rfl

private def ssRawCells_entry (q : BitVec 64) : SepProp :=
  (((q + 0x930#64) ↦₆₄ 0#64) ∗ ((q + 0x938#64) ↦₆₄ 1#64) ∗ ((q + 0x940#64) ↦₆₄ 0#64)) ∗
  (((q + 0x948#64) ↦₆₄ 0#64) ∗ ((q + 0x950#64) ↦₆₄ 1#64) ∗ ((q + 0x958#64) ↦₆₄ 0#64)) ∗
  (((q + 0x960#64) ↦₆₄ 0#64) ∗ ((q + 0x968#64) ↦₆₄ 1#64) ∗ ((q + 0x970#64) ↦₆₄ 0#64)) ∗
  (((q + 0x978#64) ↦₆₄ 0#64) ∗ ((q + 0x980#64) ↦₆₄ 8#64) ∗ ((q + 0x988#64) ↦₆₄ 0#64)) ∗
  (((q + 0x990#64) ↦₆₄ 0#64) ∗ ((q + 0x998#64) ↦₆₄ 1#64) ∗ ((q + 0x9a0#64) ↦₆₄ 0#64)) ∗
  (((q + 0x9a8#64) ↦₆₄ 0#64) ∗ ((q + 0x9b0#64) ↦₆₄ 1#64) ∗ ((q + 0x9b8#64) ↦₆₄ 0#64)) ∗
  ((q + 0x9c0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa28#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa58#64) ↦₆₄ 0xffffffffffffffff#64) ∗
  ((q + 0xa78#64) ↦₆₄ 0#64) ∗
  ((q + 0xa80#64) ↦₆₄ 0#64)

private theorem empty_vecU8_intro (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢ vecU8 A v [] := by
  dsimp only [vecU8, vecU8At, vecHeader]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [↓reduceIte, sepConj_emp, sepConj_assoc]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64 := by
    decide
  have heq : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by sep_ac_rfl
  rw [heq]
  exact Entails.pure_right hp (Entails.refl _)

private theorem empty_vecChainG_intro (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecOf A 104 8 (fun c a => prostChainGAt A a c) v [] := by
  dsimp only [vecOf, vecAt, vecHeader, vecBuf]
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 8#64)
  have hite : (if (0#64 : BitVec 64) = 0 then emp else A.live (8#64) ((0#64 : BitVec 64).toNat * 104) 8 ∗
    arrayAt (fun c a => prostChainGAt A a c) 104 8#64 [] ∗
    memRegion (8#64 + BitVec.ofNat 64 (([] : List ChainG).length * 104))
      (((0#64 : BitVec 64).toNat - ([] : List ChainG).length) * 104)) = emp := rfl
  rw [hite]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, sepConj_assoc, sepConj_emp]
  have hp : 0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64 := by
    decide
  have heq : (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
      ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64⌝ =
    ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 104 < 2 ^ 63 ∧ (8#64 : BitVec 64) ≠ 0#64⌝ ∗
      ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 8#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) := by sep_ac_rfl
  rw [heq]
  exact Entails.pure_right hp (Entails.refl _)

private theorem prostSSGQAt_empty_intro (A : RustAlloc) (q : BitVec 64) :
    ssRawCells_entry q ∗
      memRegion (q + 0x9c8#64) 96 ∗
      memRegion (q + 0xa30#64) 40 ∗
      memRegion (q + 0xa60#64) 24 ⊢
      prostSSGQAt A (q + 0x930#64) SSGQ.empty := by
  rw [show SSGQ.empty = ⟨SSG.empty, ExtraGQ.empty⟩ from rfl,
      prostSSGQAt_empty A (q + 0x930#64) SSG.empty]
  unfold ssRawCells_entry prostSSGAt SSG.empty
  dsimp only
  have h1 := empty_vecU8_intro A (q + 0x930#64)
  have h2 := empty_vecU8_intro A (q + 0x930#64 + 0x18#64)
  have h3 := empty_vecU8_intro A (q + 0x930#64 + 0x30#64)
  have h4 := empty_vecChainG_intro A (q + 0x930#64 + 0x48#64)
  have h5 := empty_vecU8_intro A (q + 0x930#64 + 0x60#64)
  have h6 := empty_vecU8_intro A (q + 0x930#64 + 0x78#64)
  have hnone : (0xffffffffffffffff#64 : BitVec 64) = noneCap := rfl
  have hp64 : ((q + 0xa78#64) ↦₆₄ 0#64) =
      ((q + 0xa78#64) ↦₃₂ 0#32) ∗ ((q + 0xa78#64 + 4#64) ↦₃₂ 0#32) := by
    simpa using pointsTo64_split32 (q + 0xa78#64) 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3 h4 h5 h6 ⊢
  rw [hp64, hnone]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.trans (Entails.of_eq (by sep_ac_rfl))
    (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
      (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (Entails.refl _)))))))

private theorem sliceCursorAfter_self (slot ptr : BitVec 64) (bs : List (BitVec 8)) :
    (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) =
      sliceCursorAfter slot ptr bs bs := by
  unfold sliceCursorAfter
  rw [Nat.sub_self, show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]

set_option maxHeartbeats 800000 in
private theorem entry_placed_wp_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
     w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 : BitVec 64)
    (hlen_nz : BitVec.ofNat 64 g.enc.length ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x1ee8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hal : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x216c#64) s
      (vecHeader g.prevPtr g.encCap g.encPtr (BitVec.ofNat 64 g.enc.length) ∗
       entryScratchCells g.q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
         w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          vecHeader g.prevPtr g.encCap g.encPtr (BitVec.ofNat 64 g.enc.length) ∗
          ((g.q + 0x920#64) ↦₆₄ g.encPtr) ∗
          ((g.q + 0x928#64) ↦₆₄ BitVec.ofNat 64 g.enc.length) ∗
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          ssRawCells_entry g.q ∗
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
  dsimp only [vecHeader, entryScratchCells] at ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps_sync_518 ext ((blkPl_518).base + 0x216c#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by unfold ssRawCells_entry; sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded Entry (`+0x1ee8 → +0x216c`, `0` allocations). -/
theorem overDecEntry_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    OverDecEntryPlacedStmt A lim := by
  intro ext st s0 s g henc_ne henc_lt _hcl
    hpc hrun hsp hal htr hx19 hx20 hx26 hx21 hx24 hx25 hx27 hx29 hvregs
  have hlen_nz := enc_len_ofNat64_ne_zero henc_ne henc_lt
  unfold overPrevElemAtBudget
  refine SepWPp_weaken_frame (overPrevElemAt_entails_of_ne_nil (A := A.repAlloc) henc_ne)
    (by sep_focus) ?_
  rw [overDecScratchPre_split g.q]
  refine SepWPp_weaken_frame (Entails.of_eq (by sep_ac_rfl))
    (show (overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
          (g.encPtr ↦ₛ g.enc)) ∗
        ((∃∗ w25 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ w22 : BitVec 64,
          ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
          ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
          ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
          ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
          ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
          ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
            entryScratchCells g.q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
              w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25) ∗
          entryScratchKeep g.q) ∗
        stackAt g.q overDecStackX ∗ A.pool lim st s =
      (∃∗ w25 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w23 : BitVec 64, ∃∗ w22 : BitVec 64,
       ∃∗ w21 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w19 : BitVec 64, ∃∗ w18 : BitVec 64,
       ∃∗ w17 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w14 : BitVec 64,
       ∃∗ w13 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w10 : BitVec 64,
       ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w6 : BitVec 64,
       ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64,
       ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        entryScratchCells g.q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
          w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25) ∗
      (overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
        (g.encPtr ↦ₛ g.enc) ∗ entryScratchKeep g.q ∗
        stackAt g.q overDecStackX ∗ A.pool lim st s) by sep_ac_rfl) ?_
  repeat' (apply SepWPp_exists_left; intro _)
  rename_i w25 w24 w23 w22 w21 w20 w19 w18 w17 w16 w15 w14 w13 w12 w11 w10 w9 w8 w7 w6 w5 w4 w3 w2 w1 w0
  have hstep := entry_placed_wp_budget A lim st ext s g
    w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
    w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25
    hlen_nz hpc hrun hsp hal hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx29
  unfold overPrevElemRestExt
  refine SepWPp_bind_sepWP_frame hstep (by sep_focus)
    fun sf hpcf hrunf hclf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  have hss := prostSSGQAt_empty_intro A.repAlloc g.q
  have hcur := sliceCursorAfter_self (g.q + 0x920#64) g.encPtr g.enc
  rw [show g.q + 0x920#64 + 8#64 = g.q + 0x928#64 by bv_omega] at hcur
  let F_post : SepProp :=
    overPrevElemRestExt A.repAlloc g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
    sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc g.enc ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool lim st sf
  refine Entails.trans (Q := (ssRawCells_entry g.q ∗ memRegion (g.q + 0x9c8#64) 96 ∗
      memRegion (g.q + 0xa30#64) 40 ∗ memRegion (g.q + 0xa60#64) 24) ∗ F_post)
    (Entails.of_eq (by unfold F_post overPrevElemRestExt entryScratchKeep; rw [← hcur]; sep_ac_rfl))
    (Entails.trans (sepConj_mono_left (Q := F_post) hss)
      (Entails.of_eq (by unfold overDecHeapBudget LoopDefsBudget.overPrevElemRestBudget F_post; sep_ac_rfl)))

private theorem rest_len_ofNat64_ne_zero {rest enc : List (BitVec 8)}
    (hne : rest ≠ []) (hsuf : rest <:+ enc) (hlen : enc.length < 2 ^ 62) :
    BitVec.ofNat 64 rest.length ≠ 0#64 := by
  have hpos : 0 < rest.length := List.length_pos_iff.mpr hne
  rcases hsuf with ⟨t, ht⟩
  have hle : rest.length ≤ enc.length := by rw [← ht, List.length_append]; omega
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero,
      Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64)] at hnat
  omega

set_option maxHeartbeats 400000 in
private theorem head_cons_placed_wp_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
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
       sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest ∗
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
  dsimp only [sliceCursorAfter] at ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps_sync_518 ext ((blkPl_518).base + 0x216c#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem head_nil_placed_wp_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
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
       sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc [] ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc [] ∗
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
  dsimp only [sliceCursorAfter, List.length_nil, BitVec.ofNat_eq_ofNat] at ⊢
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps_sync_518 ext ((blkPl_518).base + 0x2620#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

/-- Relocatable `[LibsignalPlacement]` budget-threaded loop head (`+0x2160 → +0x216c`) when
`rest ≠ []` (`0` allocations). -/
theorem overDecHeadCons_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    OverDecHeadConsPlacedStmt A lim := by
  intro ext st s0 s g v rest hne hsuf hlen hregs
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hlen_nz := rest_len_ofNat64_ne_zero hne hsuf hlen
  have hstep := head_cons_placed_wp_budget A lim st ext s g rest hlen_nz
    hpc hrun hsp hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  unfold overDecHeapBudget
  refine SepWPp_bind_sepWP_frame hstep (by sep_focus)
    fun sf hpcf hrunf hclf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

/-- Relocatable `[LibsignalPlacement]` budget-threaded loop head (`+0x2160 → +0x2620`) when
`rest = []` (`0` allocations). -/
theorem overDecHeadNil_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    OverDecHeadNilPlacedStmt A lim := by
  intro ext st s0 s g v _hlen hregs
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hstep := head_nil_placed_wp_budget A lim st ext s g
    hpc hrun hsp hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  unfold overDecHeapBudget
  refine SepWPp_bind_sepWP_frame hstep (by sep_focus)
    fun sf hpcf hrunf hclf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hclf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 5. Budget-Synchronized Tag-6 & Tag-7 Segments and Tag-7 Heap Splits -/

set_option maxHeartbeats 600000 in
theorem overDecChain_segA_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
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
        ((q + 0x9f8#64) ↦₆₄ u7) ∗ ((q + 0xa00#64) ↦₆₄ u8) ∗ ((q + 0xa08#64) ↦₆₄ u9) ∗
        A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((q + 0x9c0#64) ↦₆₄ 0#64) ∗
          ((q + 0x9c8#64) ↦₆₄ 1#64) ∗ ((q + 0x9d0#64) ↦₆₄ 0#64) ∗ ((q + 0x9d8#64) ↦₆₄ 0#64) ∗
          ((q + 0x9e0#64) ↦₆₄ 1#64) ∗ ((q + 0x9e8#64) ↦₆₄ 0#64) ∗ ((q + 0x9f0#64) ↦₆₄ 0#64) ∗
          ((q + 0x9f8#64) ↦₆₄ 8#64) ∗ ((q + 0xa00#64) ↦₆₄ 0#64) ∗
          ((q + 0xa08#64) ↦₆₄ noneCap) ∗
          A.pool lim st s1) ∧
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
  wp_steps_sync_518 ext (lsmpl.base 516)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem overDecChain_segB_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
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
    SepWP (lsProg_518 ext) ((blkPl_518).base + 8544#64) s
      (A.pool lim st s)
      (fun sf P_f =>
        (P_f ⊢ A.pool lim st sf) ∧
        sf.sp = q ∧ sf.trace = s.trace ∧
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
  wp_steps_sync_518 ext ((blkPl_518).base + 8544#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (sepConj_emp _),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 600000 in
private theorem overDecRecv_pre_step_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    {s0 s : State} {g : CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.OverDecG}
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x22e0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (_hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hsaved : OverDecSavedRegs g s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 516) s
      (((g.q + 0xbf0#64) ↦₆₄ u0) ∗
        ((g.q + 0xbf8#64) ↦₆₄ u1) ∗ ((g.q + 0xc00#64) ↦₆₄ u2) ∗ ((g.q + 0xc08#64) ↦₆₄ u3) ∗
        ((g.q + 0xc10#64) ↦₆₄ u4) ∗ ((g.q + 0xc18#64) ↦₆₄ u5) ∗ ((g.q + 0xc20#64) ↦₆₄ u6) ∗
        ((g.q + 0xc28#64) ↦₆₄ u7) ∗ ((g.q + 0xc30#64) ↦₆₄ u8) ∗ ((g.q + 0xc38#64) ↦₆₄ u9) ∗
        A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbf0#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc00#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc08#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc10#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc18#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc20#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc28#64) ↦₆₄ 8#64) ∗ ((g.q + 0xc30#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc38#64) ↦₆₄ noneCap) ∗
          A.pool lim st s1) ∧
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
  wp_steps_sync_518 ext (lsmpl.base 516)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

set_option maxHeartbeats 400000 in
theorem overDecRecv_pre_step_80_placed_budget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    {ext : String → Option (State → State)}
    {s0 s : State} {g : CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.OverDecG}
    (hpc : s.pc = (blkPl_518).base + 0x22e0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hsaved : OverDecSavedRegs g s)
    (hx0 : s.readReg64 .x0 = 2#64) :
    SepWP (lsProg_518 ext) (lsmpl.base 516) s
      (memRegion (g.q + 0xbf0#64) 80 ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbf0#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xbf8#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc00#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc08#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc10#64) ↦₆₄ 1#64) ∗ ((g.q + 0xc18#64) ↦₆₄ 0#64) ∗ ((g.q + 0xc20#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc28#64) ↦₆₄ 8#64) ∗ ((g.q + 0xc30#64) ↦₆₄ 0#64) ∗
          ((g.q + 0xc38#64) ↦₆₄ noneCap) ∗
          A.pool lim st s1) ∧
        s1.sp = g.q ∧ s1.trace = s0.trace ∧
        s1.readReg64 .x0 = 2#64 ∧ s1.readReg64 .x1 = g.q + 0xbf0#64 ∧
        s1.readReg64 .x2 = g.q + 0xbe8#64 ∧
        s1.readReg64 .lr = (blkPl_518).base + 0x2310#64 ∧
        OverDecSavedRegs g s1) := by
  rw [memRegion80_bf0_eq_cells10 g.q]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun u9 => SepWP.exists_elim fun u8 =>
    SepWP.exists_elim fun u7 => SepWP.exists_elim fun u6 =>
    SepWP.exists_elim fun u5 => SepWP.exists_elim fun u4 =>
    SepWP.exists_elim fun u3 => SepWP.exists_elim fun u2 =>
    SepWP.exists_elim fun u1 => SepWP.exists_elim fun u0 => ?_
  exact overDecRecv_pre_step_placed_budget A lim st u0 u1 u2 u3 u4 u5 u6 u7 u8 u9
    hpc hrun hsp hsp_align htr hsaved hx0

/-- Untouched Tag-7 (`receiver_chains`) frame around `bl merge<Chain>` at `A.repAlloc`
(without `A.pool`, which flows through `chainMerge3RawSpecW`). -/
def overDecRecvFrameRestExt (A : RustAlloc) (g : OverDecG) (v : SSGQ) (curLen : Nat) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    (g.encPtr ↦ₛ g.enc.take (g.enc.length - curLen)) ∗
    prostSSGQAt A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xc58#64) 24 ∗
    memRegion (g.q - BitVec.ofNat 64 overDecStackX) (overDecStackX - chainMerge3StackX)

set_option maxHeartbeats 400000 in
theorem overDecHeap_eq_recv_split_ext {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (v : SSGQ) {c : ChainG} {rest : List (BitVec 8)}
    (hsuf : (c.payload ++ rest) <:+ g.enc) :
    overDecHeapBudget A lim st s g (c.payload ++ rest) v =
      (memRegion (g.q + 0xbf0#64) 80 ∗ A.pool lim st s) ∗
      (memRegion (g.q + 0xc40#64) 24 ∗
        ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        sliceCursorAt (g.q + 0x920#64)
          (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
          (c.payload ++ rest) ∗
        stackAt g.q chainMerge3StackX ∗
        overDecRecvFrameRestExt A.repAlloc g v (c.payload ++ rest).length) := by
  unfold overDecHeapBudget LoopDefsBudget.overPrevElemRestBudget overDecRecvFrameRestExt
  rw [sliceCursorAfter_split_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      memRegion128_bf0_split_80_24_24 g.q,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  sep_ac_rfl

set_option maxHeartbeats 400000 in
theorem overDecRecvPostMergeHeap_eq_unsplit_ext {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : OverDecG) (v : SSGQ) {c : ChainG} {rest : List (BitVec 8)}
    (hsuf : (c.payload ++ rest) <:+ g.enc) :
    prostChainGAt A.repAlloc (g.q + 0xbf0#64) c ∗
      ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
      sliceCursorAfter (g.q + 0x920#64)
        (g.encPtr + BitVec.ofNat 64 (g.enc.length - (c.payload ++ rest).length))
        (c.payload ++ rest) rest ∗
      A.pool lim st s ∗
      stackAt g.q chainMerge3StackX ∗
      overDecRecvFrameRestExt A.repAlloc g v (c.payload ++ rest).length =
    overDecRecvPostMergeHeapPlBudget A lim st s g rest v c := by
  unfold overDecRecvPostMergeHeapPlBudget overDecRecvFrameRestExt
  rw [← sliceCursorAfter_unsplit_of_suffix_recv (g.q + 0x920#64) g.encPtr hsuf,
      stackAt_overDecStackX_eq_chainMerge3StackX g.q]
  sep_ac_rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.TopPlacedBudgetAux
