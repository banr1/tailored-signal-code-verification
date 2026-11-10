/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2a
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Cache-Miss Path Dispatch for `Dir::get`

Verifies the cache-miss empty-directory path (`dir.path = []`) and non-empty `dir.path` branch
(`+164`..`+332`) for `Dir::get` on Block 589 under `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2b

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.Get.Helpers
open CryptoVerification.SignalSession.Cli.Get.PlacedHelpers
  (HighCalleeSaved call_lscro_frame cstk_le_pow64 dirGetRoBundlePlaced ite_false_eq
   lt_pow63_of_lt_pow32 lt_pow64_of_lt_pow32 lt_pow64_of_lt_pow63
   ofNat64_toNat_of_lt32 ofNat64_toNat_of_lt63
   sepWPp_exists_left sepWPp_unfold_vecU8 seq_lscro_state
   spAligned_of_sp_eq subroutine_ok_lscro_withFsInv)
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false bytesAt_true)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
   RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved rustAllocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli shim_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2a

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 10. Miss Empty-Dir Path (`+164`..`+332` for `dir.path = []`) on Block `589` -/

theorem step_miss_empty_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {st0 : M.σ} {s0 s : State}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hIoCall : PathIoContractPlacedBudget A lim H rd pathOk ReadEnv ioStk)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hname_lt : x.name.length < 2 ^ 32)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hdir_nil : x.dir.path = [])
    (hfit_miss : FitsEnv M lim st0 (DirGetMissEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name))
    (hEnv_miss : ∀ evs, DirGetMissEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name evs →
      GetEnv s0.fs.files x.dir x.name evs)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 164#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfs : s.fs.files = s0.fs.files)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21 : s.readReg64 .x21 = x.self)
    (hx22 : s.readReg64 .x22 = x.nameA)
    (hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 s) ∗
        dirGetRoBundlePlaced w0 w1 wTail)
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hget_eq : x.dir.get rd s0.fs.files x.name =
      rd s0.fs.files (pathOf x.dir.path x.name) := by
    cases hd : x.dir with | mk p ch =>
    simp only [hd] at hall_ne ⊢
    have h1 := dirGhost_get_append_of_ne ch [] p rd s0.fs.files x.name hall_ne
    simpa [dirGhost_get_nil] using h1
  unfold dirAt strRefAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun dirPathPtr => ?_
  have hself32 : (x.self + 24#64) + 8#64 = x.self + 32#64 := by simp only [BitVec.add_assoc]; rfl
  rw [hself32]
  have hrepack_dir :
      vecOf A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self x.dir.changed ∗
        ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
        ((x.self + 32#64) ↦₆₄ BitVec.ofNat 64 x.dir.path.length) ∗
        (dirPathPtr ↦ᵣ x.dir.path) ⊢
      dirAt A.repAlloc x.self x.dir := by
    unfold dirAt strRefAt
    refine sepConj_mono (Entails.refl _) ?_
    refine Entails.trans ?_ (Entails.sepExists_intro dirPathPtr)
    rw [hself32]
    exact Entails.refl _
  have hbit63 : (BitVec.ofNat 64 x.name.length)[63] = false :=
    ofNat_getElem_63_false (lt_pow63_of_lt_pow32 hname_lt)
  have hbit63_lsb : (BitVec.ofNat 64 x.name.length).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (lt_pow63_of_lt_pow32 hname_lt)
  have _ := hbit63; have _ := hbit63_lsb
  have hsp24_split :
      memRegion (s0.sp - 112#64 + 24#64) 24 =
        (∃∗ p2 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p0 : BitVec 64,
          ((s0.sp - 112#64 + 24#64) ↦₆₄ p0) ∗
          ((s0.sp - 112#64 + 32#64) ↦₆₄ p1) ∗
          ((s0.sp - 112#64 + 40#64) ↦₆₄ p2)) := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsp24_split]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun p2 => sepWPp_exists_left fun p1 =>
    sepWPp_exists_left fun p0 => ?_
  have hnm_cases : x.name = [] ∨ 0 < x.name.length := by cases x.name <;> simp
  rcases hnm_cases with hnm_nil | hnm_pos
  · have hpath_ev0 : DirGetPathEnv PathEnv x.dir.path x.name [] := by
      simp [DirGetPathEnv, hdir_nil, hnm_nil, allocBytes1Events]
    refine seq_lscro_state (mid := (blkPl_589).base + 320#64) hcrl ?_
    simp only [hdir_nil, hnm_nil, List.length_nil] at hx20 ⊢
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 320#64)
    have hrepack_dir0 :
        vecOf A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self x.dir.changed ∗
          ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
          ((x.self + 32#64) ↦₆₄ 0#64) ∗
          (dirPathPtr ↦ᵣ []) ⊢
        dirAt A.repAlloc x.self x.dir := by
      simpa [hdir_nil] using hrepack_dir
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_m
    have heq_emp : ((1#64 : BitVec 64) ↦ₛ ([] : List (BitVec 8))) = emp := pointsToBytes_nil _
    rw [← emp_sepConj (dirAt A.repAlloc x.self x.dir), ← heq_emp]
    refine SepWPp.perm
      (step_miss_call_io_budget (pathStk := pathStk) (evs_path := [])
        hC hIoCall hstk hfull hsp0_al hpOk hget_eq
        (pathCap := 0#64) (pathPtr := 1#64) (pth := [])
        (w0 := w0) (w1 := w1) (wTail := wTail)
        (by simp [hdir_nil, hnm_nil, pathOf]) (by simp) (by decide) (by decide)
        (hfit_miss.seq_right hpath_ev0)
        (fun evs_rest hrest => hEnv_miss ([] ++ evs_rest) (SeqEnv.append hpath_ev0 hrest))
        hcrl_m
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm]))
      (by
        have h0_ite :
            (if (0#64 : BitVec 64) = 0 then emp
             else A.repAlloc.live 1#64 (0#64).toNat 1 ∗
               memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
                 ((0#64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
        have h0_len : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
        rw [hnm_nil, h0_ite, h0_len]
        simp only [M.stepEvents_nil, emp_sepConj, sepConj_emp]
        sep_ac_rfl)
  · have hnm_ne0 : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      ofNat_beq_zero_false hnm_pos (lt_pow64_of_lt_pow32 hname_lt)
    have _ := hnm_ne0
    have hnm_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat64_toNat_of_lt32 hname_lt
    have hlay_nm : RustLayoutOk x.name.length 1 :=
      ⟨⟨hnm_pos, ⟨0, rfl⟩, Nat.succ_le_of_lt (lt_pow63_of_lt_pow32 hname_lt)⟩,
       by have := lt_pow63_of_lt_pow32 hname_lt; omega⟩
    have hpath_ev_nm : DirGetPathEnv PathEnv x.dir.path x.name
        (rustAllocEvents x.name.length 1) := by
      simp [DirGetPathEnv, hdir_nil, allocBytes1Events, Nat.ne_of_gt hnm_pos]
    have hfit_nm : FitsEvents M lim st0 (rustAllocEvents x.name.length 1) :=
      hfit_miss.seq_left _ hpath_ev_nm
    have hshim_fs := subroutine_ok_lscro_withFsInv hFs
      (shim_lscro_of_cli (callerProg := lsProg_589 H) (stk := extHookStack) hC)
      s0.fs.files s0.trace
    have halloc_fs := subroutine_ok_lscro_withFsInv hFs
      (allocNoOom_lscro_of_cli (callerProg := lsProg_589 H) hC)
      s0.fs.files s0.trace
    have hmc_fs := subroutine_ok_lscro_withFsInv hFs
      (memcpy_bytesAt_lscro_vm_ok_at_589 hC hRO x.nameRo)
      s0.fs.files s0.trace
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_ext (cstk_le_pow64 hstk hfull)]
    have hcstk_ext_join :
        memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
          stackAt (s0.sp - 112#64) extHookStack ⊢
        stackAt (s0.sp - 112#64) cstk := by
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk_ext (cstk_le_pow64 hstk hfull)]
      exact Entails.refl _
    refine seq_lscro_state (mid := lsρ lsRustNoAllocShimSymCli) hcrl ?_
    simp only [hdir_nil, List.length_nil]
    dsimp only [lsProg_589]
    wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
    have hrepack_dir0 :
        vecOf A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self x.dir.changed ∗
          ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
          ((x.self + 32#64) ↦₆₄ 0#64) ∗
          (dirPathPtr ↦ᵣ []) ⊢
        dirAt A.repAlloc x.self x.dir := by
      simpa [hdir_nil] using hrepack_dir
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    refine call_lscro_frame (x := ())
      (T := stackAt (s0.sp - 112#64) extHookStack)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_budget ho))
      hshim_fs hcrl1 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [withFsInv, withStack, sessionShimBudgetSpec, withVmPreserved,
            CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
            emp_sepConj, pure_true_sepConj, wp_norm, hsp]; rfl)
      (fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_budget hex)
      (fun _ _ => panicQpBudget_of_fsInv_false)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
    dsimp only [withFsInv, withStack, sessionShimBudgetSpec,
      CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hfs1_inv => SepWPp.pure_left fun hvm1 =>
      SepWPp.pure_left fun htr1 => ?_
    refine SepWPp.transport_budgetPool hvm1 (hnext := ?_)
    simp only [wp_norm, hsp, sepConj_assoc]
    have hhcs1 : HighCalleeSaved s0 sf1 :=
      hhcs.of_step_call hcs1
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp1_al : sf1.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
    have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
    have hx19_1 : sf1.readReg64 .x19 = x.ret := by
      have := hcs1.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
    have hx20_1 : sf1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
      have := hcs1.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20
    have hx22_1 : sf1.readReg64 .x22 = x.nameA := by
      have := hcs1.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22
    have htr1_s0 : sf1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
    have hfs1 : sf1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs1_inv htr1_s0
    refine seq_lscro_state (mid := lsρ lsRustAllocSymCli) hcrl2 ?_
    wp_steps_sync_pool (lsρ lsRustAllocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl3
    refine call_lscro_frame (x := (x.name.length, 1, st0))
      (T := A.pool lim st0 _ ∗ stackAt (s0.sp - 112#64) extHookStack)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_budget ho))
      halloc_fs hcrl3 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp1_al)
      (by wp_norm_lhs)
      (by dsimp only [withFsInv, TripleRatchet.Hooks2Budget.rustAllocNoOomSpecWithStack,
            rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomSpec]
          simp only [wp_norm, hsp1_eq, pure_sepConj_pure_assoc]; rfl)
      (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                    (by simp only [wp_norm, arm64_norm, *]),
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm],
                  hlay_nm, hfit_nm,
                  by simp (config := { decide := true }) only [Reg.x30, Reg.lr, wp_norm, arm64_norm]⟩)
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_budget hex)
      (fun _ _ => panicQpBudget_of_fsInv_false)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 hcrl4 => ?_)
    dsimp only [withFsInv, TripleRatchet.Hooks2Budget.rustAllocNoOomSpecWithStack,
      rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomSpec]
    simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp1_eq, sepConj_assoc]
    refine SepWPp.pure_left fun hfs2_inv =>
      SepWPp.pure_left fun ⟨hacp2, hoom_ne, _⟩ => ?_
    set buf := sf2.readReg64 (Reg.gpr 0#5)
    have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
    have _ := hoom_beq
    have hhcs2 : HighCalleeSaved s0 sf2 :=
      hhcs1.of_step_call hcs2
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp2_al : sf2.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp1_al) hsp2
    have hsp2_eq : sf2.sp = s0.sp - 112#64 := by rw [hsp2]; simp only [wp_norm, arm64_norm, *]
    have hx19_2 : sf2.readReg64 .x19 = x.ret := by
      have := hcs2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_1
    have hx20_2 : sf2.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
      have := hcs2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_1
    have hx22_2 : sf2.readReg64 .x22 = x.nameA := by
      have := hcs2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22_1
    have htr2_s0 : sf2.trace = s0.trace := by rw [hacp2.2.1]; simp only [wp_norm, arm64_norm, *]
    have hfs2 : sf2.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs2_inv htr2_s0
    refine seq_lscro_state (mid := lsρ memcpyName) hcrl4 ?_
    wp_steps_sync_pool (lsρ memcpyName)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl5
    refine call_lscro_frame (x := (buf, x.nameA, x.name))
      (T := memRegion buf x.name.length ∗
        bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) extHookStack)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_budget ho))
      hmc_fs hcrl5 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp2_al)
      (by wp_norm_lhs)
      (by simp only [withFsInv, withStack, withVmPreserved, sessionMemcpyBytesAtSpec, wp_norm,
            hsp2_eq, sepConj_assoc, pure_sepConj_pure_assoc]; rfl)
      (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                    (by simp only [wp_norm, arm64_norm, *]),
                  rfl,
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  Nat.le_of_lt (lt_pow64_of_lt_pow32 hname_lt)⟩)
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_budget hex)
      (fun _ _ => panicQpBudget_of_fsInv_false)
      (fun sf3 hpc3 hrun3 hsp3 hcs3 hcrl6 => ?_)
    dsimp only [withFsInv, withStack, withVmPreserved, sessionMemcpyBytesAtSpec]
    simp only [sepConj_assoc]
    refine SepWPp.pure_left fun hfs3_inv =>
      SepWPp.pure_left fun hvm3 =>
      SepWPp.pure_left fun ⟨_, htr3⟩ => ?_
    refine SepWPp.transport_budgetPool hvm3 (hnext := ?_)
    simp only [wp_norm, hsp2_eq, sepConj_assoc]
    have hhcs3 : HighCalleeSaved s0 sf3 :=
      hhcs2.of_step_call hcs3
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp3_eq : sf3.sp = s0.sp - 112#64 := by rw [hsp3]; simp only [wp_norm, arm64_norm, *]
    have hsp3_al : sf3.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp2_al) hsp3
    have hx19_3 : sf3.readReg64 .x19 = x.ret := by
      have := hcs3.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_2
    have hx20_3 : sf3.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
      have := hcs3.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_2
    have hx21_3 : sf3.readReg64 .x21 = buf := by
      have := hcs3.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have htr3_s0 : sf3.trace = s0.trace := by rw [htr3]; simp only [wp_norm, arm64_norm, *]
    have hfs3 : sf3.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs3_inv htr3_s0
    have hcap_ne : BitVec.ofNat 64 x.name.length ≠ 0 := by
      intro h0
      have ht : (BitVec.ofNat 64 x.name.length).toNat = (0 : BitVec 64).toNat :=
        congrArg BitVec.toNat h0
      rw [hnm_toNat] at ht
      exact Nat.ne_of_gt hnm_pos ht
    refine seq_lscro_state (mid := (blkPl_589).base + 320#64) hcrl6 ?_
    wp_steps_sync_pool ((blkPl_589).base + 320#64)
    apply SepWP.fold hcstk_ext_join (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl7
    have hrem_zero :
        memRegion (buf + BitVec.ofNat 64 x.name.length)
          ((BitVec.ofNat 64 x.name.length).toNat - x.name.length) = emp := by
      rw [hnm_toNat, Nat.sub_self, memRegion_zero]
    rw [← sepConj_emp (A.live buf x.name.length 1), ← hrem_zero]
    have hlive_eq :
        A.live buf x.name.length 1 ∗
          memRegion (buf + BitVec.ofNat 64 x.name.length)
            ((BitVec.ofNat 64 x.name.length).toNat - x.name.length) =
        (if BitVec.ofNat 64 x.name.length = 0 then emp
         else A.repAlloc.live buf (BitVec.ofNat 64 x.name.length).toNat 1 ∗
           memRegion (buf + BitVec.ofNat 64 x.name.length)
             ((BitVec.ofNat 64 x.name.length).toNat - x.name.length)) := by
      rw [ite_false_eq hcap_ne, hnm_toNat, RustCliAllocBudget.repAlloc_live_norm]
    rw [hlive_eq]
    refine SepWPp.perm
      (step_miss_call_io_budget (pathStk := pathStk)
        (evs_path := rustAllocEvents x.name.length 1)
        hC hIoCall hstk hfull hsp0_al hpOk hget_eq
        (pathCap := BitVec.ofNat 64 x.name.length) (pathPtr := buf) (pth := x.name)
        (w0 := w0) (w1 := w1) (wTail := wTail)
        (by simp [hdir_nil, pathOf]) (by rw [hnm_toNat])
        (by rw [hnm_toNat]; exact lt_pow63_of_lt_pow32 hname_lt) hname_lt
        (hfit_miss.seq_right hpath_ev_nm)
        (fun evs_rest hrest => hEnv_miss _ (SeqEnv.append hpath_ev_nm hrest))
        hcrl7
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp3_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs3.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
      (by sep_frame)

/-! ## 11. Miss Path Dispatch & Non-Empty `path` Branch (`+164`..`+332`) on Block `589` -/

theorem step_miss_tail_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {PathEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {st0 : M.σ} {s0 s : State}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A lim H)
    (hRO : HookSat H memcpyName (withVmPreserved sessionMemcpyRegionROSpec))
    (hPath : subroutine_ok (lsProg_589 H) (lsmpl.base 596)
      (SpecsPlacedBudget.pathSpecPlaced A lim PathEnv pathStk))
    (hIoCall : PathIoContractPlacedBudget A lim H rd pathOk ReadEnv ioStk)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hname_lt : x.name.length < 2 ^ 32)
    (hdir_lt : x.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hpth_len_lt : (pathOf x.dir.path x.name).length < 2 ^ 32)
    (hfit_miss : FitsEnv M lim st0 (DirGetMissEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name))
    (hEnv_miss : ∀ evs, DirGetMissEnv PathEnv ReadEnv rd s0.fs.files x.dir x.name evs →
      GetEnv s0.fs.files x.dir x.name evs)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 164#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfs : s.fs.files = s0.fs.files)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21 : s.readReg64 .x21 = x.self)
    (hx22 : s.readReg64 .x22 = x.nameA)
    (hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool lim st0 s) ∗
        dirGetRoBundlePlaced w0 w1 wTail)
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) := by
  have hdir_cases : x.dir.path = [] ∨ (x.dir.path ≠ [] ∧ 0 < x.dir.path.length) := by
    cases x.dir.path <;> simp
  rcases hdir_cases with hdir_nil | ⟨hdir_ne, hdir_pos⟩
  · exact step_miss_empty_budget hC hRO hIoCall hFs hstk hfull hsp0_al
      hname_lt hpOk hdir_nil hfit_miss hEnv_miss hcrl hpc hrun hsp_al hsp hhcs hfs htr
      hx19 hx20 hx21 hx22 hall_ne
  · let cstk := dirGetCalleeStk pathStk ioStk
    have hcstk_path : pathStk ≤ cstk :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hfit_path : FitsEnv M lim st0 (PathEnv x.dir.path x.name) :=
      fun evs he => hfit_miss.seq_left evs (by simpa [DirGetPathEnv, hdir_ne] using he)
    have hget_eq : x.dir.get rd s0.fs.files x.name =
        rd s0.fs.files (pathOf x.dir.path x.name) := by
      cases hd : x.dir with | mk p ch =>
      simp only [hd] at hall_ne ⊢
      have h1 := dirGhost_get_append_of_ne ch [] p rd s0.fs.files x.name hall_ne
      simpa [dirGhost_get_nil] using h1
    unfold dirAt strRefAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_left fun dirPathPtr => ?_
    have hself32 : (x.self + 24#64) + 8#64 = x.self + 32#64 := by simp only [BitVec.add_assoc]; rfl
    rw [hself32]
    have hrepack_dir :
        vecOf A.repAlloc 48 8 (dirEntryAt A.repAlloc) x.self x.dir.changed ∗
          ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
          ((x.self + 32#64) ↦₆₄ BitVec.ofNat 64 x.dir.path.length) ∗
          (dirPathPtr ↦ᵣ x.dir.path) ⊢
        dirAt A.repAlloc x.self x.dir := by
      unfold dirAt strRefAt
      refine sepConj_mono (Entails.refl _) ?_
      refine Entails.trans ?_ (Entails.sepExists_intro dirPathPtr)
      rw [hself32]
      exact Entails.refl _
    have hdir_ne0 : (BitVec.ofNat 64 x.dir.path.length == 0#64) = false :=
      ofNat_beq_zero_false hdir_pos (lt_pow64_of_lt_pow32 hdir_lt)
    have hdir_toNat : (BitVec.ofNat 64 x.dir.path.length).toNat = x.dir.path.length :=
      ofNat64_toNat_of_lt32 hdir_lt
    have hnm_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat64_toNat_of_lt32 hname_lt
    have _ := hdir_ne0; have _ := hdir_toNat; have _ := hnm_toNat
    have hpth_lt32 : (x.dir.path ++ [0x2f#8] ++ x.name).length < 2 ^ 32 := by
      rw [(pathOf_eq_path hdir_ne x.name).symm]
      exact hpth_len_lt
    have hpath_fs := subroutine_ok_lscro_withFsInv hFs hPath s0.fs.files s0.trace
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_path (cstk_le_pow64 hstk hfull)]
    have hcstk_path_join :
        memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - pathStk) ∗
          stackAt (s0.sp - 112#64) pathStk ⊢
        stackAt (s0.sp - 112#64) cstk := by
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk_path (cstk_le_pow64 hstk hfull)]
      exact Entails.refl _
    refine seq_lscro_state (mid := lsmpl.base 596) hcrl ?_
    dsimp only [lsProg_589]
    wp_steps_sync_pool (lsmpl.base 596)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    refine call_lscro_frame
      (x := (PathGhost.mk dirPathPtr x.dir.path true x.nameA x.name x.nameRo
        (s0.sp - 112#64 + 24#64), st0))
      (T := (dirPathPtr ↦ᵣ x.dir.path) ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        stackAt (s0.sp - 112#64) pathStk ∗ A.pool lim st0 _)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_budget ho))
      hpath_fs hcrl1 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by dsimp only [SpecsPlacedBudget.pathSpecPlaced]
          simp only [withFsInv, bytesAt_true, wp_norm, hsp, pure_sepConj_pure_assoc]; rfl)
      (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                    (by simp only [wp_norm, arm64_norm, *]),
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm, *],
                  hdir_lt, hname_lt, hfit_path⟩)
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_budget hex)
      (fun _ _ => panicQpBudget_of_fsInv_false)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
    dsimp only [SpecsPlacedBudget.pathSpecPlaced, withFsInv]
    simp only [bytesAt_true, wp_norm, hsp, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc]
    refine sepWPp_exists_left fun evs_path =>
      SepWPp.pure_left fun hfs1_inv =>
      SepWPp.pure_left fun ⟨htr1, hPath_ev⟩ => ?_
    have hPath_ev' : DirGetPathEnv PathEnv x.dir.path x.name evs_path := by
      simpa [DirGetPathEnv, hdir_ne] using hPath_ev
    refine sepWPp_unfold_vecU8 fun pathCap pathPtr hpth_le hpth_cap_lt _ => ?_
    have hhcs1 : HighCalleeSaved s0 sf1 :=
      hhcs.of_step_call hcs1
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
    have hsp1_al : sf1.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
    have hx19_1 : sf1.readReg64 .x19 = x.ret := by
      have := hcs1.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
    have htr1_s0 : sf1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
    have hfs1 : sf1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs1_inv htr1_s0
    simp only [arm64_norm]
    refine seq_lscro_state (mid := (blkPl_589).base + 320#64) hcrl2 ?_
    wp_steps_sync_pool ((blkPl_589).base + 320#64)
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.fold hcstk_path_join (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl3
    refine SepWPp.perm
      (step_miss_call_io_budget (pathStk := pathStk) (evs_path := evs_path)
        hC hIoCall hstk hfull hsp0_al hpOk hget_eq
        (pathCap := pathCap) (pathPtr := pathPtr) (pth := x.dir.path ++ [0x2f#8] ++ x.name)
        (w0 := w0) (w1 := w1) (wTail := wTail)
        (pathOf_eq_path hdir_ne x.name).symm hpth_le hpth_cap_lt hpth_lt32
        (hfit_miss.seq_right hPath_ev')
        (fun evs_rest hrest => hEnv_miss _ (SeqEnv.append hPath_ev' hrest))
        hcrl3
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp1_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs1.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]))
      (by simp only [arm64_norm]; sep_frame)

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2b
