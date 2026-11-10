/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public meta import Lean
public meta import LibsignalBinary.Proofs.Common.InImageKit
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.HelpersPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.ErrExitPlaced

/-!
# Budget-Threaded Stage 5 Call Combinators (`[LibsignalPlacement]`)

Provides `s5_call_raw_placed` and budget-threaded call combinators for `futDrop`, `__rust_dealloc`,
`memcpy`, and `dropSessionStructure` on `initProgPlaced W`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

noncomputable section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
  (sepWPp_weaken_pre sepWPp_pure_left sepWPp_exists_left)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
  (sepWPp_seq_files sepWPp_call_wpp_split_lscro)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas hiding
  s5_call_raw_placed s5_dealloc_ok_at_placed s5_memcpy_ok_at_placed s5_call_futDrop_placed
  s5_call_dealloc_placed s5_call_dropSS_placed
open CryptoVerification.CliHandshake.InitiatePlaced
open LibsignalBinary.Heap
  (VmPreserved AllocEvent AllocCostModel BudgetLimits FreeOnlyEvs RustLayoutOk
   RustCliAllocBudget rustDeallocEvents rustCliDeallocBudgetExternSpecWithStack)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (InitTraceFsSound traceFsSound_initPlaced)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_base_add)

/-- Budget-ready `SepWPp` call combinator preserving `s.fs.files` (on unchanged trace),
`s.spAligned`, and `LibsignalCodeRoLoaded lsmpl ·.mem` across every normal return, polymorphic in
`Qp` and `oom`. -/
theorem s5_call_raw_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {callee ret_pc ret : BitVec 64} {spec : Spec α}
    (hFs : TraceFsSound prog)
    (hcall : subroutine_ok prog callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec))
    (xg : α) (F : SepProp) {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre : P ⊢ spec.pre xg s ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit xg code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked →
      (∃ R', sf.mem ⊨ spec.onPanic xg s sf ∗ R') → Qp sf (spec.onPanic xg s sf ∗ F))
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      (sm.trace = s.trace → sm.fs.files = s.fs.files) →
      SepWPp prog ret sm (spec.post xg s sm ∗ F) Q Qp oom)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom xg s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp oom := by
  refine sepWPp_weaken_pre hpre ?_
  refine sepWPp_seq_files hFs (mid := ret_pc)
    (Qm := fun sm Pm =>
      sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem ∧
      Pm = spec.post xg s sm ∗ F)
    ?_ ?_
  · refine sepWPp_call_wpp_split_lscro hcall xg hcrl hpc hrun hsp_align hlr rfl
      (Entails.refl _) hexit hpanic ?_ hoom
    intro sm hpcm hrunm hspm hcsm hcrlm
    exact SepWPp.of_sepWP_ret (SepWP.done hpcm hrunm ⟨hspm, hcsm, hcrlm, rfl⟩)
  · rintro sm _ hpcm hrunm hfs ⟨hspm, hcsm, hcrlm, rfl⟩
    have halignm : sm.spAligned = true := by
      simp only [State.spAligned] at hsp_align ⊢
      rwa [hspm]
    exact hnext sm hpcm hrunm hspm halignm hcsm hcrlm hfs

theorem s5_dealloc_ok_at_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ lsRustDeallocSymCli)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hAlloc.dealloc

theorem s5_memcpy_ok_at_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    (hAlloc : AllocContractsXCliPlaced A lim (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsρ memcpyName)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (sessionMemcpyBudgetSpec extHookStack)) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (hAlloc.session_memcpy extHookStack (by decide) (by decide))

theorem s5_call_futDrop_placed [LibsignalPlacement] {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {ret_pc ret : BitVec 64}
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (fsp : BitVec 64) (F : SepProp) {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 547)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre : P ⊢ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files → VmPreserved s sm →
      SepWPp (initProgPlaced mmpl gh W) ret sm F Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hFutDrop () F
    hpc hrun hsp_align hlr hcrl
    (by dsimp only [futDropBudgetSpec]; rw [emp_sepConj]; exact hpre)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  dsimp only [futDropBudgetSpec]
  apply sepWPp_pure_left; rintro ⟨htrm, hvmm⟩
  exact hnext sm hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm
    (htrm.trans htr) (hfs htrm) hvmm

theorem s5_call_futDrop_pool_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {ret_pc ret : BitVec 64}
    (hFutDrop : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 547)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec))
    (fsp : BitVec 64) (st : M.σ) (F : SepProp) {s0 s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = lsmpl.base 547)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre : P ⊢ A.pool lim st s ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm (A.pool lim st sm ∗ F) Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  refine s5_call_futDrop_placed hFutDrop fsp (A.pool lim st s ∗ F)
    hpc hrun hsp hsp_align hlr htr hcrl hpre ?_
  intro sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm hvmm
  rw [← A.pool_of_vmPreserved hvmm]
  exact hnext sm hpcm hrunm hspm halm hcsm hcrlm htrm hfilesm

theorem s5_call_dealloc_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (fsp ptr : BitVec 64) (size align : Nat) (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = ptr) (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align) (hlay : RustLayoutOk size align)
    (hpre : P ⊢ (A.pool lim st s ∗ A.live ptr size align ∗ memRegion ptr size ∗
      stackAt fsp extHookStack) ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sm ∗
          stackAt fsp extHookStack) ∗ F) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | (try dsimp only [initPcPlaced, initEntryPlaced]); simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  let _ := hlr_ls
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (ptr, size, align, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
        rustCliDeallocBudgetExternSpecWithStack]
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hx1, hx2, hlay, hlr ▸ hlr_ls⟩ (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  dsimp only [LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack]
  simp only [hsp, sepConj_assoc]
  apply sepWPp_pure_left; intro htrm
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm (htrm.trans htr) (hfs htrm))

theorem s5_call_dropSS_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} [InitTraceFsSound mmpl gh W]
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok (initProgPlaced mmpl gh W) callee
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
          M A lim)))
    (fsp ssPtr : BitVec 64) (G : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (st : M.σ) (F : SepProp)
    {s0 s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htr : s.trace = s0.trace)
    (hcrl : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = ssPtr)
    (hpre : P ⊢ (sessionStateAt A.repAlloc ssPtr G ss ∗ A.pool lim st s ∗
      stackAt fsp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F)
    (hnext : ∀ (sm : State) (evs : List AllocEvent),
      FreeOnlyEvs evs →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = fsp → sm.spAligned = true → CalleeSavedPreserved s sm →
      LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace → sm.fs.files = s.fs.files →
      SepWPp (initProgPlaced mmpl gh W) ret sm
        ((memRegion ssPtr 344 ∗ A.pool lim (M.stepEvents evs st) sm ∗
          stackAt fsp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) Q Qp oom)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first
      | assumption
      | (try dsimp only [initPcPlaced, initEntryPlaced]); simp (config := { decide := true }) only [arm64_norm, wp_norm]) :
    SepWPp (initProgPlaced mmpl gh W) ret s P Q Qp oom := by
  let _ := hlr_ls
  refine s5_call_raw_placed (traceFsSound_initPlaced mmpl gh W) hcall (⟨ssPtr, G, ss⟩, st) F
    hpc hrun hsp_align hlr hcrl
    (Entails.trans hpre (by
      dsimp only [LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec]
      simp only [hsp, sepConj_assoc]
      exact Entails.pure_right ⟨hx0, hlr ▸ hlr_ls⟩ (Entails.refl _)))
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ ⟨_, hm⟩ => (not_satisfies_false_sepConj hm).elim)
    ?_
  intro sm hpcm hrunm hspm halignm hcsm hcrlm hfs
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec]
  simp only [hsp, sepExists_sepConj_left, sepConj_assoc]
  apply sepWPp_exists_left; intro evs
  apply sepWPp_pure_left; rintro ⟨htrm, hfree⟩
  exact sepWPp_weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm evs hfree hpcm hrunm (hspm.trans hsp) halignm hcsm hcrlm (htrm.trans htr) (hfs htrm))

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKitPlacedBudget
end
