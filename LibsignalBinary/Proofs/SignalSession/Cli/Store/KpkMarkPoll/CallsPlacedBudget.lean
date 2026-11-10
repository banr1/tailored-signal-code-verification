/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import ProofLib.Hoare.Safety

/-!
# Budget-Threaded Relocatable Call Wrappers for `KpkMarkPoll`

Provides `kpk_call_total_raw_placed` and budget-threaded `SepWPp` call wrappers for `decimal`,
`Dir::get`, `Dir::put`, `PublicKey::serialize`, `concat [local#3]`, and `do_reserve_and_handle`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey djbType)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall PublicKeySerializeCall boxU8Buf publicKey_serialize_length reserveCap)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession.Cli
  (DecimalGhost DirGetGhost DirGhost DirPutGhost ReadRule decimalText dirAt getResultAt pathOf
   withFsInv)
open CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers (sepWPp_conseq)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (Concat2PosCall kpk_bcmp_placed_ok sepWPp_of_sepWP_fs_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_base_add lsRetAddr624_base_zero
   lsRetAddr624_blockPlacement_base_add lsRetAddr624_blockPlacement_base_zero)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (decimalSpecPlaced dirGetSpecPlaced dirPutSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesBudget
  (KpkConcat2PosEnv kpkConcat2PosEvents kpkConcat2PosSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserveSpecOf)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv PublicKeySerializeEnv doReserveEvents publicKeySerializeEvents
   publicKeySerializeSpecWithStack publicKeySerializeSpecX publicKeySerializeStackX)

export CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
  (kpk_bcmp_placed_ok sepWPp_of_sepWP_fs_placed)

private theorem entails_withLsCodeRoLoaded_pre [LibsignalPlacement]
    {s : State} {P Q F : SepProp}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : P ⊢ Q ∗ F) :
    P ⊢ (Q ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ F := by
  refine Entails.trans h ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hcrl (Entails.refl F))

private theorem entails_withFsInv_lscro_pre [LibsignalPlacement]
    {s : State} {F0 : FsFiles} {T0 : List TraceEvent} {P Q F : SepProp}
    (hfs : FsInv F0 T0 s) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : P ⊢ Q ∗ F) :
    P ⊢ (⌜FsInv F0 T0 s⌝ ∗ Q ∗ ⌜LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ F := by
  rw [sepConj_assoc]
  exact Entails.pure_right hfs (entails_withLsCodeRoLoaded_pre hcrl h)

private theorem not_satisfies_false_withFsInv {F0 : FsFiles} {T0 : List TraceEvent}
    {sm : State} {R' : SepProp} (h : sm.mem ⊨ (⌜FsInv F0 T0 sm⌝ ∗ ⌜False⌝) ∗ R') : False := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact not_satisfies_false_sepConj h.2

/-- Total-call `SepWPp` stepper under `LibsignalCodeRoLoaded` (`onPanic = onExit = onOom = False`). -/
theorem kpk_call_total_raw_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp), ¬ (sm.mem ⊨ spec.onPanic x s sm ∗ R'))
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp), ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_conseq hpre ?_
  intro R' hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hm_pre hsp_align hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen)
        R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpan_imp sm (F ∗ R') hpost).elim
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact (hoom_imp sm (F ∗ R') hpost).elim

theorem kpk_call_decimal_fs_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {decStk : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
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
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · dsimp only [withFsInv, decimalSpecPlaced]
    refine entails_withFsInv_lscro_pre hfs hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro code sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, decimalSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun hfsm =>
      SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm hfsm htrm hevs)

theorem kpk_call_decimal_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {decStk : Nat}
    {callee ret_pc ret : BitVec 64}
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
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · dsimp only [decimalSpecPlaced]
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [decimalSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm htrm hevs)

theorem kpk_call_dirGet_fs_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee
      (withFsInv (dirGetSpecPlaced rd pathOk A lim GetEnv getStk) s0_files s0_trace))
    (xg : DirGetGhost) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
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
      FsInv s0_files s0_trace sm →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace ∧
        GetEnv s.fs.files xg.dir xg.name evs) →
      SepWPp prog ret sm
        ((getResultAt A.repAlloc xg.ret gr ∗ dirAt A.repAlloc xg.self xg.dir ∗
          bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool lim (M.stepEvents evs st) sm) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · dsimp only [withFsInv, dirGetSpecPlaced]
    refine entails_withFsInv_lscro_pre hfs hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro code sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, dirGetSpecPlaced, withLsCodeRoLoaded,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun gr =>
      SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs gr hpcm hrunm hspm hcsm hcrlm hfsm hgr)

theorem kpk_call_dirGet_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop} {getStk : Nat}
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
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · dsimp only [dirGetSpecPlaced]
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [dirGetSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.exists_elim fun gr =>
      SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs gr hpcm hrunm hspm hcsm hcrlm hgr)

theorem kpk_call_dirPut_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop} {putStk : Nat}
    {callee ret_pc ret : BitVec 64}
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
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · dsimp only [dirPutSpecPlaced]
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    have hlr30 : LsRetAddr624 (s.readReg64 .x30) := by
      change LsRetAddr624 (s.readReg64 Reg.lr)
      rwa [hlr]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlen, hfit, hlr30⟩ (Entails.refl _)
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [dirPutSpecPlaced, withLsCodeRoLoaded, sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm evs hpcm hrunm hspm hcsm hcrlm htrm hevs)

theorem kpk_call_serialize_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (xg : PublicKeySerializeCall) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.self)
    (hfit : FitsEnv M lim st PublicKeySerializeEnv)
    (hpre : P ⊢ ((xg.self ↦ₛ xg.pk.bytes.toList) ∗ A.pool lim st s ∗
      stackAt s.sp publicKeySerializeStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.readReg64 .x0 ≠ 0#64 → sm.readReg64 .x1 = 33#64 → sm.trace = s.trace →
      SepWPp prog ret sm
        (((xg.self ↦ₛ xg.pk.bytes.toList) ∗
          A.live (sm.readReg64 .x0) 33 1 ∗ ((sm.readReg64 .x0) ↦ₛ xg.pk.serialize) ∗
          A.pool lim (M.stepEvents publicKeySerializeEvents st) sm ∗
          stackAt s.sp publicKeySerializeStackX) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · refine entails_withLsCodeRoLoaded_pre hcrl (Entails.trans hpre ?_)
    simp only [publicKeySerializeSpecX, publicKeySerializeSpecWithStack, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withLsCodeRoLoaded, publicKeySerializeSpecX, publicKeySerializeSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [withLsCodeRoLoaded, publicKeySerializeSpecX, publicKeySerializeSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [withLsCodeRoLoaded, publicKeySerializeSpecX, publicKeySerializeSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withLsCodeRoLoaded, publicKeySerializeSpecX, publicKeySerializeSpecWithStack,
      boxU8Buf, PublicKey.serialize, List.cons_ne_nil, ↓reduceIte,
      RustCliAllocBudget.repAlloc_live, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1, htrm⟩ => ?_
    have h33 : (djbType :: xg.pk.bytes.toList).length = 33 := publicKey_serialize_length xg.pk
    rw [h33]
    have heq_post :
        (xg.self ↦ₛ xg.pk.bytes.toList) ∗
          ⌜sm.readReg64 Reg.x0 ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗
          A.live (sm.readReg64 Reg.x0) 33 1 ∗
          ((sm.readReg64 Reg.x0) ↦ₛ (djbType :: xg.pk.bytes.toList)) ∗
          A.pool lim (M.stepEvents publicKeySerializeEvents st) sm ∗
          stackAt s.sp (CryptoVerification.LibsignalTripleRatchet.extHookStack + 32) ∗ F =
        ⌜sm.readReg64 Reg.x0 ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗
          (((xg.self ↦ₛ xg.pk.bytes.toList) ∗
            A.live (sm.readReg64 Reg.x0) 33 1 ∗ ((sm.readReg64 Reg.x0) ↦ₛ xg.pk.serialize) ∗
            A.pool lim (M.stepEvents publicKeySerializeEvents st) sm ∗
            stackAt s.sp publicKeySerializeStackX) ∗ F) := by
      unfold PublicKey.serialize publicKeySerializeStackX
      sep_ac_rfl
    rw [heq_post]
    refine SepWPp.pure_elim fun ⟨hp0, _⟩ =>
      hnext sm hpcm hrunm hspm hcsm hcrlm hp0 hx1 htrm

theorem kpk_call_concat2_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosSpec A lim stk)))
    (xg : Concat2PosCall) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.outVec) (hx1 : s.readReg64 .x1 = xg.slicesA)
    (hx2 : s.readReg64 .x2 = 2#64)
    (hpos0 : 0 < xg.bs0.length) (hpos1 : 0 < xg.bs1.length)
    (hmax : xg.bs0.length + xg.bs1.length < 2 ^ 63)
    (hfit : FitsEnv M lim st (KpkConcat2PosEnv xg))
    (hpre : P ⊢ (memRegion xg.outVec 24 ∗
      (xg.slicesA ↦₆₄ xg.p0) ∗ ((xg.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 xg.bs0.length) ∗
      ((xg.slicesA + 16#64) ↦₆₄ xg.p1) ∗ ((xg.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 xg.bs1.length) ∗
      (xg.p0 ↦ₛ xg.bs0) ∗ (xg.p1 ↦ₛ xg.bs1) ∗ A.pool lim st s ∗ stackAt s.sp stk) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A.repAlloc xg.outVec (xg.bs0 ++ xg.bs1) ∗
          (xg.slicesA ↦₆₄ xg.p0) ∗ ((xg.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 xg.bs0.length) ∗
          ((xg.slicesA + 16#64) ↦₆₄ xg.p1) ∗ ((xg.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 xg.bs1.length) ∗
          (xg.p0 ↦ₛ xg.bs0) ∗ (xg.p1 ↦ₛ xg.bs1) ∗
          A.pool lim (M.stepEvents (kpkConcat2PosEvents xg) st) sm ∗ stackAt s.sp stk) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · refine entails_withLsCodeRoLoaded_pre hcrl (Entails.trans hpre ?_)
    simp only [kpkConcat2PosSpec, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hpos0, hpos1, hmax, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withLsCodeRoLoaded, kpkConcat2PosSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [withLsCodeRoLoaded, kpkConcat2PosSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [withLsCodeRoLoaded, kpkConcat2PosSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withLsCodeRoLoaded, kpkConcat2PosSpec, KpkConcat2PosEnv,
      sepExists_sepConj_left, sepConj_assoc]
    refine SepWPp.exists_elim fun evs => SepWPp.pure_elim fun ⟨htrm, hevs⟩ => ?_
    subst hevs
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hcrlm htrm)

theorem kpk_call_reserve_fs_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {resStack : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee
      (withFsInv (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)) s0_files s0_trace))
    (xg : DoReserveCall) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.v) (hx1 : (s.readReg64 .x1).toNat = xg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = xg.additional)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap xg.cap.toNat xg.bs.length xg.additional + 1 ≤ 2 ^ 63)
    (hfit : FitsEnv M lim st (DoReserveEnv xg))
    (hpre : P ⊢ (vecU8At A.repAlloc xg.v xg.cap xg.ptr xg.bs ∗
      A.pool lim st s ∗ stackAt s.sp resStack) ∗ F)
    (hnext : ∀ (sm : State) (p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm → sm.trace = s.trace → p' ≠ 0#64 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc xg.v
            (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗
          stackAt s.sp resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · dsimp only [withFsInv]
    refine entails_withFsInv_lscro_pre hfs hcrl (Entails.trans hpre ?_)
    simp only [doReserveSpecOf, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro code sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, withLsCodeRoLoaded, doReserveSpecOf,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun p' => SepWPp.pure_elim fun hfsm =>
      SepWPp.pure_elim fun htrm => ?_
    have hp'_pull :
        vecU8At A.repAlloc xg.v
            (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack ∗ F =
        (vecU8At A.repAlloc xg.v
            (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗ F := by
      sep_ac_rfl
    rw [hp'_pull]
    intro R' hm hL
    have hp'_ne : p' ≠ 0#64 := by
      have hm1 : sm.mem ⊨ vecU8At A.repAlloc xg.v
          (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          ((A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗ F ∗ R') := by
        simpa only [sepConj_assoc] using hm
      unfold vecU8At at hm1
      rw [sepConj_assoc] at hm1
      have hm2 := Satisfies.of_sep_left (Satisfies.of_sep_right hm1)
      rw [satisfies_pure_sepConj] at hm2
      exact hm2.1.2.2
    exact hnext sm p' hpcm hrunm hspm hcsm hcrlm hfsm htrm hp'_ne R' hm hL

theorem kpk_call_reserve_placed [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {resStack : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee
      (withLsCodeRoLoaded lsmpl (doReserveSpecOf resStack A lim)))
    (xg : DoReserveCall) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.v) (hx1 : (s.readReg64 .x1).toNat = xg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = xg.additional)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap xg.cap.toNat xg.bs.length xg.additional + 1 ≤ 2 ^ 63)
    (hfit : FitsEnv M lim st (DoReserveEnv xg))
    (hpre : P ⊢ (vecU8At A.repAlloc xg.v xg.cap xg.ptr xg.bs ∗
      A.pool lim st s ∗ stackAt s.sp resStack) ∗ F)
    (hnext : ∀ (sm : State) (p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → p' ≠ 0#64 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc xg.v
            (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗
          stackAt s.sp resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_total_raw_placed hcall (xg, st) F hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · refine entails_withLsCodeRoLoaded_pre hcrl (Entails.trans hpre ?_)
    simp only [doReserveSpecOf, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound, hfit⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withLsCodeRoLoaded, doReserveSpecOf] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro code sm R' hpost
    simp only [withLsCodeRoLoaded, doReserveSpecOf] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [withLsCodeRoLoaded, doReserveSpecOf] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withLsCodeRoLoaded, doReserveSpecOf, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun p' => SepWPp.pure_elim fun htrm => ?_
    have hp'_pull :
        vecU8At A.repAlloc xg.v
            (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack ∗ F =
        (vecU8At A.repAlloc xg.v
            (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗ F := by
      sep_ac_rfl
    rw [hp'_pull]
    intro R' hm hL
    have hp'_ne : p' ≠ 0#64 := by
      have hm1 : sm.mem ⊨ vecU8At A.repAlloc xg.v
          (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          ((A.pool lim (M.stepEvents (doReserveEvents xg) st) sm ∗ stackAt s.sp resStack) ∗ F ∗ R') := by
        simpa only [sepConj_assoc] using hm
      unfold vecU8At at hm1
      rw [sepConj_assoc] at hm1
      have hm2 := Satisfies.of_sep_left (Satisfies.of_sep_right hm1)
      rw [satisfies_pure_sepConj] at hm2
      exact hm2.1.2.2
    exact hnext sm p' hpcm hrunm hspm hcsm hcrlm htrm hp'_ne R' hm hL

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget
