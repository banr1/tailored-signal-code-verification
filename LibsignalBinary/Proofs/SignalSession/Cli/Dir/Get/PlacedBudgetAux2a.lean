/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1b
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded Post-I/O Result Construction and `read_file` Wrapper for `Dir::get`

Verifies post-I/O result construction (`+336`..`+508`) and the `PathIoContractPlacedBudget` call
wrapper (`+320`..`+336`) for `Dir::get` on Block 589.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2a

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
  (FrozenEq HighCalleeSaved call_lscro_frame cstk_le_pow64 dgReadOpAddr dgUnreadableAddr
   dirGetRoBundlePlaced ite_false_eq lt_pow64_of_lt_pow32 lt_pow64_of_lt_pow63
   ofNat64_toNat_of_lt32 ofNat64_toNat_of_lt63
   sepWPp_exists_left sepWPp_pure_mid2 sepWPp_unfold_vecU8 sepWPp_weaken_pre seq_lscro_state
   spAligned_of_sp_eq stateOfLscroMiss subroutine_ok_lscro_withFsInv)
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs (bytesAt bytesAt_false bytesAt_true)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliAllocNoOomSpecWithStack)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
  (allocNoOom_lscro_of_cli shim_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[local arm64_norm, local wp_norm]
private theorem spAligned_writeVReg128_local (s : State) (v : BitVec 5) (val : BitVec 128) :
    (s.writeVReg128 v val).spAligned = s.spAligned := rfl

/-! ## 8. Post-I/O Result Construction (`+336`..`+508`) on Block `589` -/

theorem step_after_read_ok_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs_before : List AllocEvent}
    {s0 s : State} {outBs : List (BitVec 8)}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {r0 r1 r2 r3 r4 r5 : BitVec 64}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A lim H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : Except.ok outBs = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace)
    (hEnv_after : ∀ evs_f, FreeOnlyEvs evs_f →
      GetEnv s0.fs.files x.dir x.name (evs_before ++ evs_f)) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((((ioVecAt A.repAlloc (s0.sp - 112#64) (.ok outBs) ∗
        (if pathCap = 0 then emp
         else A.repAlloc.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        ((x.ret ↦₆₄ r5) ∗ ((x.ret + 8#64) ↦₆₄ r4) ∗ ((x.ret + 16#64) ↦₆₄ r3) ∗
         ((x.ret + 24#64) ↦₆₄ r2) ∗ ((x.ret + 32#64) ↦₆₄ r1) ∗ ((x.ret + 40#64) ↦₆₄ r0)) ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.pool lim (M.stepEvents evs_before st0) s) ∗
        dirGetRoBundlePlaced w0 w1 wTail))
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  dsimp only [ioVecAt]
  simp only [sepConj_assoc]
  refine sepWPp_unfold_vecU8 fun outCap outPtr hout_le hout_cap_lt hout_ptr_ne => ?_
  have hcmn : (outCap + 1#64 == 0#64) = false := cap_cmn1_beq_zero_false hout_cap_lt
  have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by simp only [BitVec.add_assoc]; rfl
  have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by simp only [BitVec.add_assoc]; rfl
  have hrepack_out :
      ((x.ret + 8#64) ↦₆₄ outCap) ∗
        ((x.ret + 16#64) ↦₆₄ outPtr) ∗
        ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 outBs.length) ∗
        (outPtr ↦ₛ outBs) ∗
        (if outCap = 0 then emp
         else A.repAlloc.live outPtr outCap.toNat 1 ∗
           memRegion (outPtr + BitVec.ofNat 64 outBs.length) (outCap.toNat - outBs.length)) ⊢
      vecU8 A.repAlloc (x.ret + 8#64) outBs := by
    dsimp only [vecU8]
    refine Entails.trans ?_ (Entails.sepExists_intro outCap)
    refine Entails.trans ?_ (Entails.sepExists_intro outPtr)
    rw [vecU8At_expose, hret8, hret16]
    exact Entails.pure_right ⟨hout_le, hout_cap_lt, hout_ptr_ne⟩ (Entails.refl _)
  have hsp0_24 :
      ((s0.sp - 112#64) ↦₆₄ outCap) ∗
        ((s0.sp - 112#64 + 8#64) ↦₆₄ outPtr) ∗
        ((s0.sp - 112#64 + 16#64) ↦₆₄ BitVec.ofNat 64 outBs.length) ⊢
      memRegion (s0.sp - 112#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  by_cases hpcap : pathCap = 0
  · subst hpcap
    have hEnv_nil : GetEnv s0.fs.files x.dir x.name evs_before := by
      simpa only [List.append_nil] using hEnv_after [] FreeOnlyEvs.nil
    simp only [↓reduceIte, emp_sepConj]
    refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl ?_
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 284#64)
    apply SepWP.fold hrepack_out (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A.repAlloc x.ret r1 r0 outBs) (by sep_frame)
    apply SepWP.fold hsp0_24 (by sep_frame)
    apply SepWP.fold hp24 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcrl_epi
    refine SepWPp.perm
      (step_epilogue_284_budget (evs := evs_before) (r := .ok outBs)
        (Extra := dirGetRoBundlePlaced w0 w1 wTail)
        hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2], hEnv_nil⟩)
      (by sep_frame)
  · have hpcap_beq : (pathCap == 0#64) = false := beq_false_of_ne hpcap
    have hEnv_free :
        GetEnv s0.fs.files x.dir x.name (evs_before ++ rustDeallocEvents pathCap.toNat 1) :=
      hEnv_after (rustDeallocEvents pathCap.toNat 1) (FreeOnlyEvs.singleton 1 pathCap.toNat)
    simp only [hpcap, ↓reduceIte]
    refine seq_lscro_state (mid := (blkPl_589).base + 464#64) hcrl ?_
    dsimp only [lsProg_589]
    wp_steps_sync_pool ((blkPl_589).base + 464#64)
    apply SepWP.fold hrepack_out (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A.repAlloc x.ret r1 r0 outBs) (by sep_frame)
    apply SepWP.fold hsp0_24 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    refine SepWPp.perm
      (step_dealloc_epilogue_464_budget (evs_pre := evs_before) (r := .ok outBs)
        (pathCap := pathCap) (pathPtr := pathPtr) (pathLenW := BitVec.ofNat 64 pth.length)
        (Extra := dirGetRoBundlePlaced w0 w1 wTail)
        hC hcstk hstk hfull hsp0_al hcrl_d
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
        hpcap hpth_cap_lt
        ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2], hEnv_free⟩)
      (by sep_frame)

theorem step_after_read_err_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs_before : List AllocEvent}
    {s0 s : State}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {r0 r1 r2 r3 r4 r5 : BitVec 64}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A lim H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hfit_22 : FitsEvents M lim (M.stepEvents evs_before st0) (rustAllocEvents 22 1))
    (hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : (Except.error () : Except Unit (List (BitVec 8))) = x.dir.get rd s0.fs.files x.name ∧
      s.trace = s0.trace)
    (hEnv_after : ∀ evs_f, FreeOnlyEvs evs_f →
      GetEnv s0.fs.files x.dir x.name ((evs_before ++ rustAllocEvents 22 1) ++ evs_f)) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((((ioVecAt A.repAlloc (s0.sp - 112#64) (.error ()) ∗
        (if pathCap = 0 then emp
         else A.repAlloc.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        ((x.ret ↦₆₄ r5) ∗ ((x.ret + 8#64) ↦₆₄ r4) ∗ ((x.ret + 16#64) ↦₆₄ r3) ∗
         ((x.ret + 24#64) ↦₆₄ r2) ∗ ((x.ret + 32#64) ↦₆₄ r1) ∗ ((x.ret + 40#64) ↦₆₄ r0)) ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.pool lim (M.stepEvents evs_before st0) s) ∗
        dirGetRoBundlePlaced w0 w1 wTail))
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  dsimp only [ioVecAt]
  simp only [sepConj_assoc]
  have hsp0_24_err :
      ((s0.sp - 112#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (s0.sp - 112#64 + 8#64) 16 ⊢
      memRegion (s0.sp - 112#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64) 8 16 (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)
  have hshim := shim_lscro_of_cli (callerProg := lsProg_589 H) (stk := extHookStack) hC
  have halloc := allocNoOom_lscro_of_cli (callerProg := lsProg_589 H) hC
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
  have hcstk_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
        stackAt (s0.sp - 112#64) extHookStack ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    exact Entails.refl _
  refine seq_lscro_state (mid := lsρ lsRustNoAllocShimSymCli) hcrl ?_
  dsimp only [lsProg_589]
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSymCli)
  apply SepWP.fold hsp0_24_err (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  refine call_lscro_frame (x := ())
    (T := stackAt (s0.sp - 112#64) extHookStack)
    hshim hcrl1 (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp_al)
    (by wp_norm_lhs)
    (by simp only [withStack, sessionShimBudgetSpec, withVmPreserved,
          CryptoVerification.LibsignalTripleRatchet.sessionShimSpec,
          emp_sepConj, pure_true_sepConj, wp_norm, hsp])
    trivial (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQpBudget_false)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
  dsimp only [withStack, sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_left fun hvm1 => SepWPp.pure_left fun htr1 => ?_
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
  have hx21_1 : sf1.readReg64 .x21 = pathPtr := by
    have := hcs1.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21
  have htr1_eq : sf1.trace = s.trace := htr1
  have hlay22 : RustLayoutOk 22 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  refine seq_lscro_state (mid := lsρ lsRustAllocSymCli) hcrl2 ?_
  wp_steps_sync_pool (lsρ lsRustAllocSymCli)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl3
  refine call_lscro_frame (x := (22, 1, M.stepEvents evs_before st0))
    (T := A.pool lim (M.stepEvents evs_before st0) _ ∗ stackAt (s0.sp - 112#64) extHookStack)
    halloc hcrl3 (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp1_al)
    (by wp_norm_lhs)
    (by dsimp only [TripleRatchet.Hooks2Budget.rustAllocNoOomSpecWithStack,
          rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomSpec]
        simp only [wp_norm, hsp1_eq]; rfl)
    (by refine ⟨by simp only [wp_norm, arm64_norm],
                by simp only [wp_norm, arm64_norm],
                hlay22, hfit_22,
                by simp (config := { decide := true }) only [Reg.x30, Reg.lr, wp_norm, arm64_norm]⟩)
    (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQpBudget_false)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 hcrl4 => ?_)
  dsimp only [TripleRatchet.Hooks2Budget.rustAllocNoOomSpecWithStack,
    rustCliAllocNoOomSpecWithStack, LibsignalBinary.Heap.rustCliAllocNoOomSpec]
  simp only [Bool.false_eq_true, ↓reduceIte, wp_norm, hsp1_eq, sepConj_assoc,
    ← M.stepEvents_append]
  refine SepWPp.pure_left fun ⟨hacp2, hoom_ne, _⟩ => ?_
  set buf := sf2.readReg64 (Reg.gpr 0#5)
  have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
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
  have hx21_2 : sf2.readReg64 .x21 = pathPtr := by
    have := hcs2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21_1
  have htr2_eq : sf2.trace = s.trace := by
    rw [hacp2.2.1]; simp only [wp_norm, arm64_norm, htr1_eq]
  have hmem22 :
      memRegion buf 22 =
        (∃∗ b1 : BitVec 64, ∃∗ b0 : BitVec 64,
          (buf ↦₆₄ b0) ∗ ((buf + 8#64) ↦₆₄ b1) ∗ memRegion (buf + 16#64) 6) := by
    rw [memRegion_split buf 8 14 (by decide),
        memRegion_split (buf + 8#64) 8 6 (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hmem22]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun b1 => sepWPp_exists_left fun b0 => ?_
  unfold dirGetRoBundlePlaced
  refine seq_lscro_state (mid := (blkPl_589).base + 424#64) hcrl4 ?_
  wp_steps_sync_pool ((blkPl_589).base + 424#64)
  apply SepWP.fold (write_22_overlap_mid buf w1) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl5
  rw [ProofLib.memRegion_eight (buf + 14#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun bt => ?_
  let errBs := unpack64 w0 ++ (unpack64 w1).take 6 ++ unpack64 wTail
  have herr_len : errBs.length = 22 := by simp [errBs, unpack64_length]
  have herr_pack :
      (x.ret ↦₆₄ 9223372036854775809#64) ∗ ((x.ret + 8#64) ↦₆₄ 22#64) ∗
        ((x.ret + 16#64) ↦₆₄ buf) ∗ ((x.ret + 24#64) ↦₆₄ 22#64) ∗
        ((x.ret + 32#64) ↦₆₄ dgReadOpAddr) ∗ ((x.ret + 40#64) ↦₆₄ 4#64) ∗
        A.live buf 22 1 ∗ (buf ↦ₛ errBs) ∗ (dgReadOpAddr ↦ᵣ Cli.utf8 "read") ⊢
      getResultAt A.repAlloc x.ret (.error ()) :=
    getResultAt_err_of_ro A.repAlloc x.ret buf dgReadOpAddr errBs herr_len hoom_ne
  by_cases hpcap : pathCap = 0
  · subst hpcap
    have hEnv_nil : GetEnv s0.fs.files x.dir x.name (evs_before ++ rustAllocEvents 22 1) := by
      simpa only [List.append_nil] using hEnv_after [] FreeOnlyEvs.nil
    simp only [↓reduceIte, emp_sepConj]
    refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl5 ?_
    wp_steps_sync_pool ((blkPl_589).base + 284#64)
    apply SepWP.fold (write_22_overlap_done buf w0 w1 wTail) (by sep_frame)
    apply SepWP.fold herr_pack (by dsimp only [errBs]; sep_frame)
    apply SepWP.fold hp24 (by sep_frame)
    apply SepWP.fold hcstk_join (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcrl6
    refine SepWPp.perm
      (step_epilogue_284_budget (evs := evs_before ++ rustAllocEvents 22 1) (r := .error ())
        (Extra := (dgUnreadableAddr ↦₆₄ᵣ w0) ∗
          ((dgUnreadableAddr + 8#64) ↦₆₄ᵣ w1) ∗
          ((dgUnreadableAddr + 14#64) ↦₆₄ᵣ wTail))
        hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs2.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs_setMem, calleeSavedVRegs_setPC, calleeSavedVRegs_writeReg64];
              exact calleeSavedVRegs_writeVReg128 sf2 (0#5) (w1 ++ w0) (by decide)))
        ⟨hres.1, by simp only [wp_norm, arm64_norm, htr2_eq, hres.2], hEnv_nil⟩)
      (by sep_frame)
  · have hpcap_beq : (pathCap == 0#64) = false := beq_false_of_ne hpcap
    have hEnv_free :
        GetEnv s0.fs.files x.dir x.name
          ((evs_before ++ rustAllocEvents 22 1) ++ rustDeallocEvents pathCap.toNat 1) :=
      hEnv_after (rustDeallocEvents pathCap.toNat 1) (FreeOnlyEvs.singleton 1 pathCap.toNat)
    simp only [hpcap, ↓reduceIte]
    refine seq_lscro_state (mid := (blkPl_589).base + 464#64) hcrl5 ?_
    wp_steps_sync_pool ((blkPl_589).base + 464#64)
    apply SepWP.fold (write_22_overlap_done buf w0 w1 wTail) (by sep_frame)
    apply SepWP.fold herr_pack (by dsimp only [errBs]; sep_frame)
    apply SepWP.fold hcstk_join (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl6
    refine SepWPp.perm
      (step_dealloc_epilogue_464_budget
        (evs_pre := evs_before ++ rustAllocEvents 22 1) (r := .error ())
        (pathCap := pathCap) (pathPtr := pathPtr) (pathLenW := BitVec.ofNat 64 pth.length)
        (Extra := (dgUnreadableAddr ↦₆₄ᵣ w0) ∗
          ((dgUnreadableAddr + 8#64) ↦₆₄ᵣ w1) ∗
          ((dgUnreadableAddr + 14#64) ↦₆₄ᵣ wTail))
        hC hcstk hstk hfull hsp0_al hcrl6
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp2_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs2.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs_setMem, calleeSavedVRegs_setPC, calleeSavedVRegs_writeReg64];
              exact calleeSavedVRegs_writeVReg128 sf2 (0#5) (w1 ++ w0) (by decide)))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hpcap hpth_cap_lt
        ⟨hres.1, by simp only [wp_norm, arm64_norm, htr2_eq, hres.2], hEnv_free⟩)
      (by simp only [← RustCliAllocBudget.repAlloc_live_norm]; sep_frame)

theorem step_after_read_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {cstk stk : Nat} {x : DirGetGhost} {st0 : M.σ} {evs_before : List AllocEvent}
    {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A lim H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpth_le : pth.length ≤ pathCap.toNat)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hfit_after : FitsEnv M lim (M.stepEvents evs_before st0)
      (DirGetAfterReadEnv rd s0.fs.files (pathOf x.dir.path x.name)))
    (hr_rd : r = rd s0.fs.files (pathOf x.dir.path x.name))
    (hEnv_after : ∀ evs_ar,
      DirGetAfterReadEnv rd s0.fs.files (pathOf x.dir.path x.name) evs_ar →
      GetEnv s0.fs.files x.dir x.name (evs_before ++ evs_ar))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      (((ioVecAt A.repAlloc (s0.sp - 112#64) r ∗
        (pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.repAlloc.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.pool lim (M.stepEvents evs_before st0) s) ∗
        dirGetRoBundlePlaced w0 w1 wTail))
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hdrop := vecU8At_drop_buf A.repAlloc pathCap pathPtr pth hpth_le hpth_cap_lt
  have hpre_drop :
      ((ioVecAt A.repAlloc (s0.sp - 112#64) r ∗
        (pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.repAlloc.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.pool lim (M.stepEvents evs_before st0) s) ∗
        dirGetRoBundlePlaced w0 w1 wTail) ⊢
      (((ioVecAt A.repAlloc (s0.sp - 112#64) r ∗
        (if pathCap = 0 then emp
         else A.repAlloc.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.pool lim (M.stepEvents evs_before st0) s) ∗
        dirGetRoBundlePlaced w0 w1 wTail) := by
    simp only [sepConj_assoc]
    rw [← sepConj_assoc (pathPtr ↦ₛ pth)]
    exact sepConj_mono_right (sepConj_mono_left hdrop)
  refine sepWPp_weaken_pre hpre_drop ?_
  rw [memRegion_48_split6 x.ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun r0 => sepWPp_exists_left fun r1 =>
    sepWPp_exists_left fun r2 => sepWPp_exists_left fun r3 =>
    sepWPp_exists_left fun r4 => sepWPp_exists_left fun r5 => ?_
  have hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  cases r with
  | ok outBs =>
    have herr_nil : DirGetErrAllocEnv rd s0.fs.files (pathOf x.dir.path x.name) [] := by
      unfold DirGetErrAllocEnv
      rw [← hr_rd]
    exact step_after_read_ok_budget hC hcstk hstk hfull hsp0_al hpth_cap_lt hp24
      hcrl hpc hrun hsp_al hsp hhcs hx19 hx21 hres
      (fun evs_f hf => hEnv_after evs_f (SeqEnv.append herr_nil hf))
  | error u =>
    cases u
    have herr_22 :
        DirGetErrAllocEnv rd s0.fs.files (pathOf x.dir.path x.name) (rustAllocEvents 22 1) := by
      unfold DirGetErrAllocEnv
      rw [← hr_rd]
    have hfit_22 : FitsEvents M lim (M.stepEvents evs_before st0) (rustAllocEvents 22 1) :=
      hfit_after.seq_left (rustAllocEvents 22 1) herr_22
    exact step_after_read_err_budget hC hcstk hstk hfull hsp0_al hpth_cap_lt hfit_22 hp24
      hcrl hpc hrun hsp_al hsp hhcs hx19 hx21 hres
      (fun evs_f hf => by
        rw [List.append_assoc]
        exact hEnv_after (rustAllocEvents 22 1 ++ evs_f) (SeqEnv.append herr_22 hf))

/-! ## 9. `read_file` Call Wrapper (`+320`..`+336`) on Block `589` -/

def PathIoContractPlacedBudget [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks)
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop)
    (ioStk : Nat) : Prop :=
  ∀ (s0 s : State) (st1 : M.σ) (pathPtr : BitVec 64) (pth : List (BitVec 8)) (F : SepProp)
    (Q : State → SepProp → Prop) (Qp : State → SepProp → Prop),
    StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
    s.pc = (blkPl_589).base + 332#64 →
    s.status = .Running →
    s.spAligned = true →
    FsInv s0.fs.files s0.trace s →
    s.trace = s0.trace →
    s.readReg64 .x0 = pathPtr →
    (s.readReg64 .x1).toNat = pth.length →
    s.readReg64 .x8 = s.sp →
    pth.length < 2 ^ 32 →
    pathOk pth →
    FitsEnv M lim st1 (ReadEnv s0.fs.files pth) →
    (∀ sf : State,
      sf.pc = (blkPl_589).base + 336#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (lsProg_589 H) (s0.readReg64 .x30) sf
        (((∃∗ evs_read : List AllocEvent,
            ⌜ReadEnv s0.fs.files pth evs_read⌝ ∗
              (∃∗ r : Except Unit (List (BitVec 8)),
                ⌜r = rd s0.fs.files pth ∧ sf.trace = s0.trace⌝ ∗
                ioVecAt A.repAlloc s.sp r) ∗
              (pathPtr ↦ₛ pth) ∗ stackAt s.sp ioStk ∗
              A.pool lim (M.stepEvents evs_read st1) sf)) ∗ F)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (lsProg_589 H) (s0.readReg64 .x30) s
      (((pathPtr ↦ₛ pth) ∗ memRegion s.sp 24 ∗ stackAt s.sp ioStk ∗ A.pool lim st1 s) ∗ F)
      Q Qp (fun _ => ⌜False⌝)

theorem step_miss_call_io_budget [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {ReadEnv : FsFiles → List (BitVec 8) → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {st0 : M.σ} {evs_path : List AllocEvent} {s0 sm : State}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A lim H)
    (hIoCall : PathIoContractPlacedBudget A lim H rd pathOk ReadEnv ioStk)
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hget_eq : x.dir.get rd s0.fs.files x.name = rd s0.fs.files (pathOf x.dir.path x.name))
    (hpth_eq : pth = pathOf x.dir.path x.name)
    (hpth_le : pth.length ≤ pathCap.toNat)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hpth_lt32 : pth.length < 2 ^ 32)
    (hfit_after_path : FitsEnv M lim (M.stepEvents evs_path st0)
      (SeqEnv (ReadEnv s0.fs.files (pathOf x.dir.path x.name))
        (DirGetAfterReadEnv rd s0.fs.files (pathOf x.dir.path x.name))))
    (hEnv_path : ∀ evs_rest,
      SeqEnv (ReadEnv s0.fs.files (pathOf x.dir.path x.name))
        (DirGetAfterReadEnv rd s0.fs.files (pathOf x.dir.path x.name)) evs_rest →
      GetEnv s0.fs.files x.dir x.name (evs_path ++ evs_rest))
    (hcrl_m : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpc_m : sm.pc = (blkPl_589).base + 320#64)
    (hrun_m : sm.status = .Running)
    (hsp_al_m : sm.spAligned = true)
    (hsp_m : sm.sp = s0.sp - 112#64)
    (hhcs_m : HighCalleeSaved s0 sm)
    (hfs_m : sm.fs.files = s0.fs.files)
    (htr_m : sm.trace = s0.trace)
    (hx19_m : sm.readReg64 .x19 = x.ret)
    (hx20_m : sm.readReg64 .x20 = BitVec.ofNat 64 pth.length)
    (hx21_m : sm.readReg64 .x21 = pathPtr) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) sm
      (((pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.repAlloc.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A.repAlloc x.self x.dir ∗
        bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.pool lim (M.stepEvents evs_path st0) sm) ∗
        dirGetRoBundlePlaced w0 w1 wTail)
      (dirGetPostQPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQpPlacedBudget rd pathOk A lim GetEnv stk x st0 s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hcstk_io : ioStk ≤ cstk :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk_io (cstk_le_pow64 hstk hfull)]
  have hcstk_io_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
        stackAt (s0.sp - 112#64) ioStk ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_io (cstk_le_pow64 hstk hfull)]
    exact Entails.refl _
  have hpth_fz : FrozenEq pth (pathOf x.dir.path x.name) := ⟨hpth_eq⟩
  clear hpth_eq
  refine seq_lscro_state (mid := (blkPl_589).base + 332#64) hcrl_m ?_
  dsimp only [lsProg_589]
  wp_steps_sync_pool ((blkPl_589).base + 332#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_io
  rcases hpth_fz with ⟨hpth_eq⟩
  let s_io := stateOfLscroMiss hcrl_io
  have hpth_nat : (BitVec.ofNat 64 pth.length).toNat = pth.length :=
    ofNat64_toNat_of_lt32 hpth_lt32
  have hsp_cur : s_io.sp = s0.sp - 112#64 := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hpc_cur : s_io.pc = (blkPl_589).base + 332#64 := by
    dsimp only [s_io, stateOfLscroMiss]; wp_norm_lhs
  have hrun_cur : s_io.status = ExecStatus.Running := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hsp_al_cur : s_io.spAligned = true := by simpa only [s_io, stateOfLscroMiss, wp_norm, arm64_norm] using hsp_al_m
  have hinv_cur : FsInv s0.fs.files s0.trace s_io :=
    fsInv_of_files_trace_eq (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *])
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *])
  have htr_cur : s_io.trace = s0.trace := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hx0_cur : s_io.readReg64 .x0 = pathPtr := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hx1_cur : (s_io.readReg64 .x1).toNat = pth.length := by
    simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, hpth_nat]
  have hx8_cur : s_io.readReg64 .x8 = s_io.sp := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hhcs_cur : HighCalleeSaved s0 s_io :=
    hhcs_m.of_steps
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfLscroMiss, calleeSavedVRegs, wp_norm, arm64_norm])
  have hx19_cur : s_io.readReg64 .x19 = x.ret := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hx21_cur : s_io.readReg64 .x21 = pathPtr := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  let F_io : SepProp :=
    ((if pathCap = 0 then emp
      else A.repAlloc.live pathPtr pathCap.toNat 1 ∗
        memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
     ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
     ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
     ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
     dirAt A.repAlloc x.self x.dir ∗
     bytesAt x.nameRo x.nameA x.name ∗
     memRegion x.ret 48 ∗
     memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
     savedRegsAt (s0.sp - 112#64) s0) ∗
    dirGetRoBundlePlaced w0 w1 wTail
  refine SepWPp.perm
    (P' := ((pathPtr ↦ₛ pth) ∗ memRegion s_io.sp 24 ∗
      stackAt s_io.sp ioStk ∗ A.pool lim (M.stepEvents evs_path st0) s_io) ∗ F_io)
    ?_ (by rw [hsp_cur]; dsimp only [F_io, s_io, stateOfLscroMiss]; sep_frame)
  refine hIoCall s0 s_io (M.stepEvents evs_path st0) pathPtr pth F_io _ _ hcrl_io
    hpc_cur hrun_cur hsp_al_cur hinv_cur htr_cur
    hx0_cur hx1_cur hx8_cur hpth_lt32 (by rwa [hpth_eq])
    (by rw [hpth_eq]; exact hfit_after_path.seq_left)
    (fun sf_r hpc_r hrun_r hsp_r hcs_r hcrl_r => ?_)
  have hsp_r_al : sf_r.spAligned = true := spAligned_of_sp_eq hsp_al_cur hsp_r
  rw [hsp_cur] at hsp_r ⊢
  dsimp only [F_io]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWPp_exists_left fun evs_read => SepWPp.pure_left fun hRead_ev =>
    sepWPp_exists_left fun r_io => SepWPp.pure_left fun hres_io => ?_
  rw [← M.stepEvents_append]
  have hhcs_r : HighCalleeSaved s0 sf_r := hhcs_cur.of_calleeSaved hcs_r
  have hx19_r : sf_r.readReg64 .x19 = x.ret := hcs_r.1.trans hx19_cur
  have hx21_r : sf_r.readReg64 .x21 = pathPtr := hcs_r.2.2.1.trans hx21_cur
  let P_ar : SepProp :=
    (ioVecAt A.repAlloc (s0.sp - 112#64) r_io ∗
      (pathPtr ↦ₛ pth) ∗
      (if pathCap = 0 then emp
       else A.repAlloc.live pathPtr pathCap.toNat 1 ∗
         memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
      ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
      ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
      dirAt A.repAlloc x.self x.dir ∗
      bytesAt x.nameRo x.nameA x.name ∗
      memRegion x.ret 48 ∗
      savedRegsAt (s0.sp - 112#64) s0 ∗
      A.pool lim (M.stepEvents (evs_path ++ evs_read) st0) sf_r) ∗
    dirGetRoBundlePlaced w0 w1 wTail
  refine SepWPp.perm
    (P' := (memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
      stackAt (s0.sp - 112#64) ioStk) ∗ P_ar) ?_
    (by dsimp only [P_ar]; sep_frame)
  refine sepWPp_weaken_pre (sepConj_mono hcstk_io_join (Entails.refl P_ar)) ?_
  refine SepWPp.perm
    (step_after_read_budget (cstk := cstk) (evs_before := evs_path ++ evs_read) (r := r_io)
      (pathCap := pathCap) (pathPtr := pathPtr) (pth := pth)
      (w0 := w0) (w1 := w1) (wTail := wTail)
      hC hcstk_ext hstk hfull hsp0_al hpth_le hpth_cap_lt
      (by rw [M.stepEvents_append]; exact hfit_after_path.seq_right (hpth_eq ▸ hRead_ev))
      (hpth_eq ▸ hres_io.1)
      (fun evs_ar har => by
        rw [List.append_assoc]
        exact hEnv_path (evs_read ++ evs_ar) (SeqEnv.append (hpth_eq ▸ hRead_ev) har))
      hcrl_r hpc_r hrun_r hsp_r_al hsp_r hhcs_r hx19_r hx21_r
      ⟨by rw [hres_io.1, hpth_eq, hget_eq], hres_io.2⟩)
    (by dsimp only [P_ar]; sep_frame)

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux2a
