/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable Helpers for `remove_pre_key::{closure#0}`

`AllocEvent` envelopes (`OptPkRemoveTailEnv`, `CliPkRemovePollEnv`) and budget-threaded call/frame
helpers for Block `575` (`lsProg_575 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DecimalGhost DirGetGhost DirGhost DirPutGhost PkPollGhost ReadRule decimalText dirAt
   getResultAt keyName pathOf withFsInv)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_575 blkPl_575 lsProg_575)
open CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
  (entails_withLsCodeRoLoaded_pre sepWPp_conseq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_base_add lsRetAddr624_base_zero
   lsRetAddr624_blockPlacement_base_add lsRetAddr624_blockPlacement_base_zero)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (optDeallocBufEvents)

section Placed

theorem freeOnlyEvs_rustDeallocEvents (size align : Nat) :
    FreeOnlyEvs (rustDeallocEvents size align) :=
  FreeOnlyEvs.singleton align size

theorem freeOnlyEvs_optDeallocBufEvents (cap : BitVec 64) :
    FreeOnlyEvs (optDeallocBufEvents cap) := by
  unfold optDeallocBufEvents
  split
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap.toNat

/-- Branch-dependent tail `AllocEvent` envelope after `Dir::get` in `remove_pre_key::{closure#0}`:
- on `.ok (_ :: _)`: `FreeOnlyEvs` drops of `bytes` and `name`, followed by a second `decimal` call
  on `x.id` and `Dir::put` on `(x.dir, keyName x.id, [])`;
- on `.error ()` or `.ok []`: `FreeOnlyEvs` buffer drops only. -/
def OptPkRemoveTailEnv
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (x : PkPollGhost) (gr : Except Unit (List (BitVec 8))) : List AllocEvent → Prop :=
  match gr with
  | .ok (_ :: _) =>
    SeqEnv FreeOnlyEvs (SeqEnv (DecEnv x.id) (PutEnv x.dir (keyName x.id) []))
  | _ => FreeOnlyEvs

/-- Composed `AllocEvent` envelope for `remove_pre_key::{closure#0}`: `decimal` followed by
`Dir::get` and `OptPkRemoveTailEnv`. -/
def CliPkRemovePollEnv (rd : ReadRule)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop)
    (PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (F0 : FsFiles) (x : PkPollGhost) : List AllocEvent → Prop :=
  SeqEnv (DecEnv x.id)
    (SeqEnv (GetEnv F0 x.dir (keyName x.id))
      (OptPkRemoveTailEnv DecEnv PutEnv x (x.dir.get rd F0 (keyName x.id))))

theorem pkrm_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A lim H) :
    subroutine_ok ((blkPC_575).rebase (blkPl_575).base H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (rustDeallocExternSpecWithStack M A lim extHookStack)) :=
  dealloc_lscro_of_cli (callerProg := lsProg_575 H) hC

/-- Call any total `Spec` whose panic/exit/OOM are `False`, preserving `LibsignalCodeRoLoaded pl`
in a `SepWPp` continuation. -/
theorem pkrm_call_total_placed_raw {α : Type} {prog : Program} {pl : MultiPlacement}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp), ¬ (sm.mem ⊨ spec.onPanic x s sm ∗ R'))
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded pl sm.mem →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_seq_lscro (mid := ret_pc) hcrl ?_
  exact ProofLib.SepWP.call_subroutine_frame hcall hpc hrun hsp_align hlr
    (fun R hm => by
      have hm' : s.mem ⊨ (spec.pre x s ∗ F) ∗ R := Satisfies.mono (sepConj_mono_left hpre) hm
      rwa [sepConj_assoc] at hm')
    (fun R' sm _ hp => hpan_imp sm R' hp)
    (fun R' code sm _ he => hexit_imp code sm R' he)
    (fun sm hpcm hrunm hspm hcsm =>
      ProofLib.SepWP.done hpcm hrunm (fun hcrlm => hnext sm hpcm hrunm hspm hcsm hcrlm))
    (fun R' sm _ ho => (hoom_imp sm (F ∗ R') ho).elim)

theorem pkrm_call_decimal_fs_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {decStk : Nat} {callee ret_pc ret : BitVec 64}
    {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee
      (withFsInv (decimalSpecPlaced A lim DecEnv decStk) s0_files s0_trace))
    (xg : DecimalGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hfit : FitsEnv M lim st (DecEnv xg.n))
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm → sm.trace = s.trace → DecEnv xg.n evs →
      SepWPp prog ret sm
        ((vecU8 A.repAlloc xg.ret (decimalText xg.n.toNat) ∗
          stackAt s.sp decStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    dsimp only [withFsInv]
    simp only [sepConj_assoc]
    refine Entails.pure_right hfs ?_
    unfold decimalSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFsInv, decimalSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    simp only [withFsInv, decimalSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm R' hpost
    simp only [withFsInv, decimalSpecPlaced, withLsCodeRoLoaded, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, decimalSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun hfsm =>
      SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm hfsm htrm hevs)

theorem pkrm_call_decimal_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {decStk : Nat} {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (decimalSpecPlaced A lim DecEnv decStk))
    (xg : DecimalGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hfit : FitsEnv M lim st (DecEnv xg.n))
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → DecEnv xg.n evs →
      SepWPp prog ret sm
        ((vecU8 A.repAlloc xg.ret (decimalText xg.n.toNat) ∗
          stackAt s.sp decStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    unfold decimalSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [decimalSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [decimalSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [decimalSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [decimalSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm htrm hevs)

theorem pkrm_call_dirGet_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (xg : DirGetGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hfit : FitsEnv M lim st (GetEnv s.fs.files xg.dir xg.name))
    (hpre : P ⊢ (dirAt A.repAlloc xg.self xg.dir ∗ bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace ∧
        GetEnv s.fs.files xg.dir xg.name evs) →
      SepWPp prog ret sm
        ((getResultAt A.repAlloc xg.ret gr ∗ dirAt A.repAlloc xg.self xg.dir ∗
          bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    unfold dirGetSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun gr =>
      SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs gr hpcm hrunm hspm hcsm hcrlm hgr)

theorem pkrm_call_dirPut_placed [LibsignalPlacement] {prog : Program}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {putStk : Nat} {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirPutSpecPlaced A lim PutEnv putStk))
    (xg : DirPutGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameV)
    (hx2 : s.readReg64 .x2 = xg.bytesV) (hlen : xg.dir.changed.length < 2 ^ 32)
    (hfit : FitsEnv M lim st (PutEnv xg.dir xg.name xg.bytes))
    (hpre : P ⊢ (dirAt A.repAlloc xg.self xg.dir ∗ vecU8 A.repAlloc xg.nameV xg.name ∗
      vecU8 A.repAlloc xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool lim st s) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → PutEnv xg.dir xg.name xg.bytes evs →
      SepWPp prog ret sm
        ((dirAt A.repAlloc xg.self (xg.dir.put xg.name xg.bytes) ∗
          memRegion xg.nameV 24 ∗ memRegion xg.bytesV 24 ∗
          stackAt s.sp putStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | (apply lsRetAddr624_blockPlacement_base_add <;> decide)
      | (apply lsRetAddr624_base_add <;> decide)
      | (apply lsRetAddr624_blockPlacement_base_zero <;> decide)
      | (apply lsRetAddr624_base_zero <;> decide)
      | simp (config := { decide := true }) only [wp_norm, arm64_norm]) :
    SepWPp prog ret s P Q Qp := by
  refine pkrm_call_total_placed_raw hcall (xg, st) F hpc hrun hsp_align hlr hcrl
    ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    unfold dirPutSpecPlaced
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    simp only [sepConj_assoc]
    have hlr30 : LsRetAddr624 (s.readReg64 .x30) := by
      change LsRetAddr624 (s.readReg64 Reg.lr)
      rwa [hlr]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlen, hfit, hlr30⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [dirPutSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [dirPutSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [dirPutSpecPlaced, withLsCodeRoLoaded] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [dirPutSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm htrm hevs)

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
