/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.RoDataPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlaced
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout

/-!
# Relocatable Call Wrappers for `KpkMarkPoll`

Provides `SepWPp` call wrappers for `mark_kyber_pre_key_used::{closure#0}` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SpqrV1.Varint

theorem kpk_bcmp_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ cliBcmpName) cliBcmpSpec := by
  obtain ⟨f, hf, hok⟩ := hBcmp
  exact subroutine_ok_of_hookOk ((ls_externAt?_of_mem (by decide) hi hunmut).trans hf) hok

private theorem entails_withLsCodeRoLoaded_pre [LibsignalPlacement]
    {s : State} {P Q F : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : P ⊢ Q ∗ F) :
    P ⊢ (Q ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ F := by
  refine Entails.trans h ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (Entails.pure_right hcrl (Entails.refl F))

private theorem entails_withFsInv_lscro_pre [LibsignalPlacement]
    {s : State} {F0 : FsFiles} {T0 : List TraceEvent} {P Q F : SepProp}
    (hfs : FsInv F0 T0 s) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : P ⊢ Q ∗ F) :
    P ⊢ (⌜FsInv F0 T0 s⌝ ∗ Q ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem⌝) ∗ F := by
  rw [sepConj_assoc]
  exact Entails.pure_right hfs (entails_withLsCodeRoLoaded_pre hcrl h)

private theorem not_satisfies_false_withFsInv {F0 : FsFiles} {T0 : List TraceEvent}
    {sm : State} {R' : SepProp} (h : sm.mem ⊨ (⌜FsInv F0 T0 sm⌝ ∗ ⌜False⌝) ∗ R') : False := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact not_satisfies_false_sepConj h.2

theorem sepWPp_of_sepWP_fs_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P : SepProp}
    {F0 : FsFiles} {T0 : List TraceEvent}
    {Q Qp : State → SepProp → Prop}
    (hFs : TraceFsSound prog) (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv F0 T0 s)
    (h : SepWP prog mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → FsInv F0 T0 sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := fun R hm hL => by
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨_, _, Pm, hsm, hnext⟩ | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) (hfs.of_steps hFs hsteps) R hsm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem kpk_call_panicking_raw_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok prog callee spec)
    (x : α) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic x s sm ∗ R') → allocFailedIn s sm ∧ s.trace <+: sm.trace)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit x code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom x s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_conseq hpre ?_
  intro R' hm hL
  have hm_pre : s.mem ⊨ spec.pre x s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall x (F ∗ R') hpc hrun hm_pre hsp_align hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic x s sm ∗ F) ∗ R' := by
      rwa [← sepConj_assoc] at hpost
    have halloc0 : allocFailedIn s0 sm ∧ s0.trace <+: sm.trace := by
      simpa [allocFailedIn, htr] using hpan_imp sm (F ∗ R') hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hm_pan, hpan sm _ halloc0⟩)⟩
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact (hoom_imp sm (F ∗ R') hpost).elim

theorem kpk_call_decimal_fs_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc} {decStk : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee (withFsInv (decimalSpecPlaced A decStk) s0_files s0_trace))
    (xg : DecimalGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm → sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.ret (decimalText xg.n.toNat) ∗ stackAt s.sp decStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_
  · dsimp only [withFsInv, decimalSpecPlaced]
    refine entails_withFsInv_lscro_pre hfs hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFsInv, decimalSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, decimalSpecPlaced, sepConj_assoc]
    refine SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hcrlm hfsm htrm)

theorem kpk_call_decimal_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc} {decStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (decimalSpecPlaced A decStk))
    (xg : DecimalGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg32 .x1 = xg.n)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (memRegion xg.ret 24 ∗ stackAt s.sp decStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.ret (decimalText xg.n.toNat) ∗ stackAt s.sp decStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_
  · dsimp only [decimalSpecPlaced]
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [decimalSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [decimalSpecPlaced, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hcrlm htrm)

theorem kpk_call_dirGet_fs_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee (withFsInv (dirGetSpecPlaced rd pathOk A getStk) s0_files s0_trace))
    (xg : DirGetGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.ret) (hx1 : s.readReg64 .x1 = xg.self)
    (hx2 : s.readReg64 .x2 = xg.nameA) (hx3 : (s.readReg64 .x3).toNat = xg.name.length)
    (hnlen : xg.name.length < 2 ^ 32) (hdlen : xg.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf xg.dir.path xg.name))
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
      memRegion xg.ret 48 ∗ stackAt s.sp getStk ∗ A.pool) ∗ F)
    (hnext : ∀ (sm : State) (gr : Except Unit (List (BitVec 8))),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm →
      (gr = xg.dir.get rd s.fs.files xg.name ∧ sm.trace = s.trace) →
      SepWPp prog ret sm
        ((getResultAt A xg.ret gr ∗ dirAt A xg.self xg.dir ∗
          SpqrV1.ChainProofs.bytesAt xg.nameRo xg.nameA xg.name ∗
          stackAt s.sp getStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_
  · dsimp only [withFsInv, dirGetSpecPlaced]
    refine entails_withFsInv_lscro_pre hfs hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hnlen, hdlen, hpOk⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFsInv, dirGetSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, dirGetSpecPlaced]
    kpk_sep_norm
    refine SepWPp.exists_elim fun gr => SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun hgr => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm gr hpcm hrunm hspm hcsm hcrlm hfsm hgr)

theorem kpk_call_dirPut_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc} {putStk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (dirPutSpecPlaced A putStk))
    (xg : DirPutGhost) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.self) (hx1 : s.readReg64 .x1 = xg.nameV)
    (hx2 : s.readReg64 .x2 = xg.bytesV) (hlen : xg.dir.changed.length < 2 ^ 32)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (dirAt A xg.self xg.dir ∗ vecU8 A xg.nameV xg.name ∗
      vecU8 A xg.bytesV xg.bytes ∗ stackAt s.sp putStk ∗ A.pool) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((dirAt A xg.self (xg.dir.put xg.name xg.bytes) ∗
          memRegion xg.nameV 24 ∗ memRegion xg.bytesV 24 ∗
          stackAt s.sp putStk ∗ A.pool) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_
  · dsimp only [dirPutSpecPlaced]
    refine entails_withLsCodeRoLoaded_pre hcrl ?_
    refine Entails.trans hpre ?_
    simp only [sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlen⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [dirPutSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [dirPutSpecPlaced, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hcrlm htrm)

theorem kpk_call_serialize_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX A)))
    (xg : PublicKeySerializeCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.self)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ ((xg.self ↦ₛ xg.pk.bytes.toList) ∗ A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.readReg64 .x0 ≠ 0#64 → sm.readReg64 .x1 = 33#64 → sm.trace = s.trace →
      SepWPp prog ret sm
        (((xg.self ↦ₛ xg.pk.bytes.toList) ∗
          A.live (sm.readReg64 .x0) 33 1 ∗ ((sm.readReg64 .x0) ↦ₛ xg.pk.serialize) ∗
          A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_
  · refine entails_withLsCodeRoLoaded_pre hcrl (Entails.trans hpre ?_)
    simp only [publicKeySerializeSpecX, sepConj_assoc]
    exact Entails.pure_right hx0 (Entails.refl _)
  · intro sm R' hpost
    simp only [publicKeySerializeSpecX, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [publicKeySerializeSpecX] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [publicKeySerializeSpecX] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [publicKeySerializeSpecX, boxU8Buf, PublicKey.serialize,
      List.cons_ne_nil, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1, htrm⟩ => ?_
    have h33 : (djbType :: xg.pk.bytes.toList).length = 33 := publicKey_serialize_length xg.pk
    rw [h33]
    rw [show (xg.self ↦ₛ xg.pk.bytes.toList) ∗ ⌜sm.readReg64 Reg.x0 ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗
          A.live (sm.readReg64 Reg.x0) 33 1 ∗ ((sm.readReg64 Reg.x0) ↦ₛ (djbType :: xg.pk.bytes.toList)) ∗
          A.pool ∗ stackAt s.sp publicKeySerializeStackX ∗ F =
        ⌜sm.readReg64 Reg.x0 ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗
          (((xg.self ↦ₛ xg.pk.bytes.toList) ∗
            A.live (sm.readReg64 Reg.x0) 33 1 ∗ ((sm.readReg64 Reg.x0) ↦ₛ xg.pk.serialize) ∗
            A.pool ∗ stackAt s.sp publicKeySerializeStackX) ∗ F) by
          unfold PublicKey.serialize; ac_rfl]
    refine SepWPp.pure_elim fun ⟨hp0, _⟩ => ?_
    exact hnext sm hpcm hrunm hspm hcsm hcrlm hp0 hx1 htrm

theorem kpk_call_concat2_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc} {stk : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl (kpkConcat2PosSpec A stk)))
    (xg : Concat2PosCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.outVec) (hx1 : s.readReg64 .x1 = xg.slicesA)
    (hx2 : s.readReg64 .x2 = 2#64)
    (hpos0 : 0 < xg.bs0.length) (hpos1 : 0 < xg.bs1.length)
    (hmax : xg.bs0.length + xg.bs1.length < 2 ^ 63)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (memRegion xg.outVec 24 ∗
      (xg.slicesA ↦₆₄ xg.p0) ∗ ((xg.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 xg.bs0.length) ∗
      ((xg.slicesA + 16#64) ↦₆₄ xg.p1) ∗ ((xg.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 xg.bs1.length) ∗
      (xg.p0 ↦ₛ xg.bs0) ∗ (xg.p1 ↦ₛ xg.bs1) ∗ A.pool ∗ stackAt s.sp stk) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace →
      SepWPp prog ret sm
        ((vecU8 A xg.outVec (xg.bs0 ++ xg.bs1) ∗
          (xg.slicesA ↦₆₄ xg.p0) ∗ ((xg.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 xg.bs0.length) ∗
          ((xg.slicesA + 16#64) ↦₆₄ xg.p1) ∗ ((xg.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 xg.bs1.length) ∗
          (xg.p0 ↦ₛ xg.bs0) ∗ (xg.p1 ↦ₛ xg.bs1) ∗ A.pool ∗ stackAt s.sp stk) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_
  · refine entails_withLsCodeRoLoaded_pre hcrl (Entails.trans hpre ?_)
    simp only [kpkConcat2PosSpec, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hpos0, hpos1, hmax⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [kpkConcat2PosSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [kpkConcat2PosSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [kpkConcat2PosSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [kpkConcat2PosSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hcrlm htrm)

theorem kpk_call_reserve_fs_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc} {resStack : Nat}
    {callee ret_pc ret : BitVec 64} {s0_files : FsFiles} {s0_trace : List TraceEvent}
    (hcall : subroutine_ok prog callee
      (withFsInv (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)) s0_files s0_trace))
    (xg : DoReserveCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hfs : FsInv s0_files s0_trace s)
    (hx0 : s.readReg64 .x0 = xg.v) (hx1 : (s.readReg64 .x1).toNat = xg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = xg.additional)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap xg.cap.toNat xg.bs.length xg.additional + 1 ≤ 2 ^ 63)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (vecU8At A xg.v xg.cap xg.ptr xg.bs ∗ A.pool ∗ stackAt s.sp resStack) ∗ F)
    (hnext : ∀ (sm : State) (p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      FsInv s0_files s0_trace sm → sm.trace = s.trace → p' ≠ 0#64 →
      SepWPp prog ret sm
        ((vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_
  · dsimp only [withFsInv]
    refine entails_withFsInv_lscro_pre hfs hcrl (Entails.trans hpre ?_)
    simp only [SpqrV1.Varint.doReserveSpecOf, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [withFsInv, SpqrV1.Varint.doReserveSpecOf, doReserveSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2.1
  · intro code sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm R' hpost
    exact not_satisfies_false_withFsInv hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [withFsInv, SpqrV1.Varint.doReserveSpecOf]
    kpk_sep_norm
    refine SepWPp.exists_elim fun p' => SepWPp.pure_elim fun hfsm =>
      SepWPp.pure_elim fun htrm => ?_
    have hp'_pull :
        vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack ∗ F =
        (vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack) ∗ F := by
      ac_rfl
    rw [hp'_pull]
    intro R' hm hL
    have hp'_ne : p' ≠ 0#64 := by
      have hm1 : sm.mem ⊨ vecU8At A xg.v
          (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          ((A.pool ∗ stackAt s.sp resStack) ∗ F ∗ R') := by
        simpa only [sepConj_assoc] using hm
      unfold vecU8At at hm1
      rw [sepConj_assoc] at hm1
      have hm2 := Satisfies.of_sep_left (Satisfies.of_sep_right hm1)
      rw [satisfies_pure_sepConj] at hm2
      exact hm2.1.2.2
    exact hnext sm p' hpcm hrunm hspm hcsm hcrlm hfsm htrm hp'_ne R' hm hL

theorem kpk_call_reserve_placed [LibsignalPlacement] {prog : Program} {A : RustAlloc} {resStack : Nat}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl (SpqrV1.Varint.doReserveSpecOf resStack A)))
    (xg : DoReserveCall) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = xg.v) (hx1 : (s.readReg64 .x1).toNat = xg.bs.length)
    (hx2 : (s.readReg64 .x2).toNat = xg.additional)
    (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hbound : reserveCap xg.cap.toNat xg.bs.length xg.additional + 1 ≤ 2 ^ 63)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hpre : P ⊢ (vecU8At A xg.v xg.cap xg.ptr xg.bs ∗ A.pool ∗ stackAt s.sp resStack) ∗ F)
    (hnext : ∀ (sm : State) (p' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s.trace → p' ≠ 0#64 →
      SepWPp prog ret sm
        ((vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_panicking_raw_placed hcall xg F hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_
  · refine entails_withLsCodeRoLoaded_pre hcrl (Entails.trans hpre ?_)
    simp only [SpqrV1.Varint.doReserveSpecOf, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [SpqrV1.Varint.doReserveSpecOf, doReserveSpec,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro code sm R' hpost
    simp only [SpqrV1.Varint.doReserveSpecOf, doReserveSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [SpqrV1.Varint.doReserveSpecOf, doReserveSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm hcsm hcrlm
    simp only [SpqrV1.Varint.doReserveSpecOf]
    kpk_sep_norm
    refine SepWPp.exists_elim fun p' => SepWPp.pure_elim fun htrm => ?_
    have hp'_pull :
        vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack ∗ F =
        (vecU8At A xg.v (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          A.pool ∗ stackAt s.sp resStack) ∗ F := by
      ac_rfl
    rw [hp'_pull]
    intro R' hm hL
    have hp'_ne : p' ≠ 0#64 := by
      have hm1 : sm.mem ⊨ vecU8At A xg.v
          (BitVec.ofNat 64 (reserveCap xg.cap.toNat xg.bs.length xg.additional)) p' xg.bs ∗
          ((A.pool ∗ stackAt s.sp resStack) ∗ F ∗ R') := by
        simpa only [sepConj_assoc] using hm
      unfold vecU8At at hm1
      rw [sepConj_assoc] at hm1
      have hm2 := Satisfies.of_sep_left (Satisfies.of_sep_right hm1)
      rw [satisfies_pure_sepConj] at hm2
      exact hm2.1.2.2
    exact hnext sm p' hpcm hrunm hspm hcsm hcrlm htrm hp'_ne R' hm hL

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
