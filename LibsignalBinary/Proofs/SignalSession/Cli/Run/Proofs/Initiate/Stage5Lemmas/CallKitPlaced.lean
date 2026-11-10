/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.VtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKit
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public meta import Lean
public meta import LibsignalBinary.Proofs.Common.InImageKit
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 5 Call Combinators and Frame Tactics (`[LibsignalPlacement]`)

Re-exports Stage 5 frame tactics and stack splits alongside `s5_call_raw_placed` and specialized
`initProgPlaced W` call wrappers (`s5_call_futDrop_placed`, `s5_call_dealloc_placed`,
`s5_call_dropSS_placed`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

theorem initEntryPlaced_eq_blkPl [LibsignalPlacement] :
    initEntryPlaced = (blkPl_521).base := rfl

theorem entails_withLsCodeRoLoaded {α : Type} {pl : MultiPlacement} {spec : Spec α}
    {xg : α} {s : State} {P F : SepProp}
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded pl s.mem)
    (h : P ⊢ spec.pre xg s ∗ F) :
    P ⊢ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded pl spec).pre xg s ∗ F := by
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc]
  exact Entails.trans h (sepConj_mono_right (Entails.pure_right hcrl (Entails.refl _)))

/-- Unified `SepWPp` call combinator preserving `s.trace`, `s.fs.files`, `s.spAligned`, and
`LibsignalCodeRoLoaded lsmpl ·.mem` across every normal return, while routing `allocFailedIn`
panics to `Qp`. -/
theorem s5_call_raw_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hFs : TraceFsSound prog)
    (hcall : subroutine_ok prog callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (xg : α) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ spec.pre xg s ∗ F)
    (htr_post : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.post xg s sm ∗ R') → sm.trace = s.trace)
    (hpan_imp : ∀ (sm : State) (R' : SepProp),
      (sm.mem ⊨ spec.onPanic xg s sm ∗ R') → allocFailedIn s sm)
    (hexit_imp : ∀ (code : BitVec 64) (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onExit xg code s sm ∗ R'))
    (hoom_imp : ∀ (sm : State) (R' : SepProp),
      ¬ (sm.mem ⊨ spec.onOom xg s sm ∗ R'))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp prog ret sm (spec.post xg s sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_conseq (entails_withLsCodeRoLoaded hcrl hpre) ?_
  intro R' hm hL
  have hm_pre : s.mem ⊨ (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec).pre xg s ∗ (F ∗ R') := by
    rwa [sepConj_assoc] at hm
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall xg (F ∗ R') hpc hrun hm_pre hsp_align hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · have htrm : sm.trace = s.trace := htr_post sm (F ∗ R') hpost
    have hfilesm : sm.fs.files = s.fs.files :=
      hFs.files_eq hsteps (evs := []) (by rw [htrm, List.append_nil]) NoFsEv.nil
    have halignm : sm.spAligned = true := by
      simp only [State.spAligned] at hsp_align ⊢
      rwa [hspm]
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm halignm hcsm (hcrl.of_keepsFrozen hsteps.keepsFrozen)
        (htrm.trans htr) hfilesm R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · have hm_pan : sm.mem ⊨ (spec.onPanic xg s sm ∗ F) ∗ R' := by
      rwa [← sepConj_assoc] at hpost
    have halloc0 : allocFailedIn s0 sm := by
      simpa [allocFailedIn, htr] using hpan_imp sm (F ∗ R') hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan_st, _, hm_pan, hpan sm _ halloc0⟩)⟩
  · exact (hexit_imp code sm (F ∗ R') hpost).elim
  · exact (hoom_imp sm (F ∗ R') hpost).elim

theorem s5_dealloc_ok_at_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A extHookStack)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hh.alloc.dealloc

theorem s5_memcpy_ok_at_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpySpec extHookStack)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (hh.alloc.session_memcpy extHookStack (by decide) (by decide))

theorem s5_call_futDrop_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {B : RunBudgets}
    {stk : Nat} {ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (fsp : BitVec 64) (F : SepProp) {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 547)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm F Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hStore.futDrop () F
    hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [StoreSession.futDropSpec, emp_sepConj]
    exact Entails.refl _
  · intro sm R' hpost
    simp only [StoreSession.futDropSpec, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro sm R' hpost
    simp only [StoreSession.futDropSpec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [StoreSession.futDropSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [StoreSession.futDropSpec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm
    simp only [StoreSession.futDropSpec]
    refine SepWPp.pure_elim fun _ => ?_
    exact hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hcrlm htrm hfilesm

theorem s5_call_dealloc_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustDeallocExternSpecWithStack A extHookStack)))
    (fsp ptr : BitVec 64) (size align : Nat) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align) (hlay : LayoutOk size align)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (A.pool ∗ A.live ptr size align ∗ memRegion ptr size ∗ stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm ((A.pool ∗ stackAt fsp extHookStack) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hcall (ptr, size, align) F
    hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [rustDeallocExternSpecWithStack, hsp, sepConj_assoc]
    exact Entails.pure_right ⟨hx0, hx1, hx2, hlay⟩ (Entails.refl _)
  · intro sm R' hpost
    simp only [rustDeallocExternSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro sm R' hpost
    simp only [rustDeallocExternSpecWithStack] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [rustDeallocExternSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [rustDeallocExternSpecWithStack] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm
    simp only [rustDeallocExternSpecWithStack, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hcrlm htrm hfilesm)

theorem s5_call_dropSS_placed [LibsignalPlacement] {A : RustAlloc} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {callee ret_pc ret : BitVec 64}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (FromRecordCallees.dropSessionStructureLocal2Spec A)))
    (fsp ssPtr : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8))) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = ssPtr)
    (hpan : ∀ sf P_f, allocFailedIn s0 sf → Qp sf P_f)
    (hpre : P ⊢ (sessionStateAt A ssPtr G st ∗ A.pool ∗
      stackAt fsp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((memRegion ssPtr 344 ∗ A.pool ∗
          stackAt fsp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) Q Qp) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp := by
  refine s5_call_raw_placed hh.fs hcall ⟨ssPtr, G, st⟩ F
    hpc hrun hsp_align hlr htr hcrl hpan ?_ ?_ ?_ ?_ ?_ ?_
  · refine Entails.trans hpre ?_
    simp only [FromRecordCallees.dropSessionStructureLocal2Spec, hsp, sepConj_assoc]
    exact Entails.pure_right hx0 (Entails.refl _)
  · intro sm R' hpost
    simp only [FromRecordCallees.dropSessionStructureLocal2Spec, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    exact hpost.1
  · intro sm R' hpost
    simp only [FromRecordCallees.dropSessionStructureLocal2Spec] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · intro code sm R' hpost
    simp only [FromRecordCallees.dropSessionStructureLocal2Spec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm R' hpost
    simp only [FromRecordCallees.dropSessionStructureLocal2Spec] at hpost
    exact not_satisfies_false_sepConj hpost
  · intro sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm
    simp only [FromRecordCallees.dropSessionStructureLocal2Spec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun _ => ?_
    exact sepWPp_conseq (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm (hspm.trans hsp) halm hcsm hcrlm htrm hfilesm)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
