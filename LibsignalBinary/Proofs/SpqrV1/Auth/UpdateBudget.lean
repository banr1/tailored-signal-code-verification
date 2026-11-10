/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import Lean -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Auth.Update -- shake: keep
public meta import ProofLib.SepLogic.WP.ControlTactics -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Fixed-Offset Proof of `<spqr::authenticator::Authenticator>::update`

Re-exports the envelopes, `RustCliAllocBudget` specifications, and `[LibsignalPlacement]` proofs
from `UpdateBudgetAux`, and proves the fixed-offset `.inImage img` contracts for
`<Authenticator>::update` (`0x58ac4`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState toBEBytes)
open CryptoVerification (
  LibsignalPlacement libsignalSessionCode libsignalSessionImage
  libsignalSessionCode_fnOff_0x58ac4 libsignalSessionCode_fnOff_0x5de8c
  libsignalSessionCode_fnOff_0x5eab8
)
open CryptoVerification.InImageLift (OptCallInv)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator HkdfFn hkdfToSliceUnchecked hkdfToVecUnchecked spqrHkdfWith
)
open CryptoVerification.LibsignalTripleRatchet (
  ImgCallInv allocName allocZeroedName deallocName extHookStack
  shimName subroutine_ok_inImage_of_subroutine_ok tripleRatchetProgAtExt
)
open CryptoVerification.LibsignalTripleRatchet.Keys (
  SepWPp.rw_pre memRegion_32_cells sub_ok_at_rebase
)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecU8At)
open CryptoVerification.SpqrV1.Auth (
  AuthUpdateGhost AuthUpdatePinnedGhost AuthenticatorGhost
  SepWPp.pure_left_focus
  authUpdateName authUpdateStackExt authUpdateStackX
  authenticatorAt authenticatorAt_eq_exists_pinned authenticatorPinAt
  authenticatorPinAt_expose_entails dealloc_vecBuf_cases
  drop_32_take_32_eq_drop_32_of_length_64 hkdfToVecUnchecked_eq_hkdfToSliceUnchecked
  pointsTo64_rev64_eq_toBEBytes pointsToBytes_64_entails_memRegion
  pointsToBytes_replicate_64_entails_memRegion toBEBytes_8_length
  vecBufAt vecBufAt_fold vecBufAt_of_cap_ne_zero vecBufAt_of_cap_zero
  vecU8At_expose_entails
)
open CryptoVerification.SpqrV1.Auth.UpdateFacts (
  allocZeroed_fnOff alloc_fnOff authUpdate_fnOff authenticatorAt_of_32_32
  handleError_fnOff rejoin_stack_authUpdateX replicate_32_zero_length
  rodata_updateLabel rodata_zeros32_update
  shim_fnOff stackAt_authUpdateX_split updateLabel_length
)
open CryptoVerification.SpqrV1.ChainProofs (
  HkdfToSliceGhost SliceConcat2Ghost
  bytesAt bytesAt_false bytesAt_true exists_unpack64_of_length_64_split
  hkdfToSliceName hkdfToSliceSpec hkdfToSliceSpecExt hkdfToSliceSpqrSpec
  hkdfToSliceStackExt sliceConcatName
)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (
  SepWP.pure_left_focus
  dealloc_fnOff drop_32_take_32_length_of_64 hkdfToSlice_fnOff sliceConcat_fnOff
  subroutine_ok_inImage_rodata2_keep take_32_length_of_64
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStackBase rustCliAllocNoOomSpecWithStackBase
  rustCliDeallocBudgetExternSpecWithStackBase subroutine_ok_rustCliAllocBudget_withStackBase
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  SliceConcat2Env sliceConcat2Events sliceConcat2Spec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (subroutine_ok_post_entails)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (AllocContractsXBudget)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (
  allocNoOomWithStack_inImage_of_budget allocNoOom_opt_of_x dealloc_opt_of_x
  rebase_trapHooks_fnAddr sepWP_optImage_rebase_vm sepWPp_optImage_rebase_vm
  shimSpecWithStack shim_opt_of_x
)

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst := h

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length updateLabel_length replicate_32_zero_length
  List.length_append
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  authUpdate_fnOff sliceConcat_fnOff hkdfToSlice_fnOff
  shim_fnOff alloc_fnOff allocZeroed_fnOff dealloc_fnOff handleError_fnOff
  libsignalSessionCode_fnOff_0x58ac4 libsignalSessionCode_fnOff_0x5eab8
  libsignalSessionCode_fnOff_0x5de8c
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc") (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed") (ls_hook% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc") (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error") (ls_hook% "alloc::raw_vec::handle_error")

/-! ## Re-Exports from `UpdateBudgetAux` -/

abbrev optCapDeallocEvents := @UpdateBudgetAux.optCapDeallocEvents
abbrev sliceConcat2DeallocEvents := @UpdateBudgetAux.sliceConcat2DeallocEvents
abbrev optCapDeallocEvents_ofNat := @UpdateBudgetAux.optCapDeallocEvents_ofNat
abbrev freeOnlyEvs_optCapDeallocEvents := @UpdateBudgetAux.freeOnlyEvs_optCapDeallocEvents
abbrev freeOnlyEvs_sliceConcat2DeallocEvents :=
  @UpdateBudgetAux.freeOnlyEvs_sliceConcat2DeallocEvents
abbrev authUpdatePinnedEvents := @UpdateBudgetAux.authUpdatePinnedEvents
abbrev AuthUpdatePinnedEnv := @UpdateBudgetAux.AuthUpdatePinnedEnv
abbrev fitsEnv_authUpdatePinned_iff := @UpdateBudgetAux.fitsEnv_authUpdatePinned_iff
abbrev AuthUpdatePreAlloc1Env := @UpdateBudgetAux.AuthUpdatePreAlloc1Env
abbrev AuthUpdateAlloc2Env := @UpdateBudgetAux.AuthUpdateAlloc2Env
abbrev AuthUpdateLenEnv := @UpdateBudgetAux.AuthUpdateLenEnv
abbrev AuthUpdateEnv := @UpdateBudgetAux.AuthUpdateEnv
abbrev authUpdatePinnedEvents_mem_authUpdateLenEnv :=
  @UpdateBudgetAux.authUpdatePinnedEvents_mem_authUpdateLenEnv
abbrev authUpdatePinnedEvents_mem_authUpdateEnv :=
  @UpdateBudgetAux.authUpdatePinnedEvents_mem_authUpdateEnv
abbrev fitsEvents_pinned_of_fitsEnv_authUpdateEnv :=
  @UpdateBudgetAux.fitsEvents_pinned_of_fitsEnv_authUpdateEnv
abbrev spqrBoundedEvs_of_authUpdateLenEnv := @UpdateBudgetAux.spqrBoundedEvs_of_authUpdateLenEnv
abbrev spqrBoundedEvs_of_authUpdateEnv := @UpdateBudgetAux.spqrBoundedEvs_of_authUpdateEnv
abbrev fitsEvents_authUpdatePinned_unpack := @UpdateBudgetAux.fitsEvents_authUpdatePinned_unpack
abbrev authUpdatePinnedSpecAt := @UpdateBudgetAux.authUpdatePinnedSpecAt
abbrev authUpdateSpecAt := @UpdateBudgetAux.authUpdateSpecAt
abbrev authUpdatePinnedSpec := @UpdateBudgetAux.authUpdatePinnedSpec
abbrev authUpdateSpec := @UpdateBudgetAux.authUpdateSpec
abbrev authUpdatePinnedSpecExt := @UpdateBudgetAux.authUpdatePinnedSpecExt
abbrev authUpdateSpecExt := @UpdateBudgetAux.authUpdateSpecExt
abbrev AuthUpdatePlacedOk := @UpdateBudgetAux.AuthUpdatePlacedOk
abbrev AuthUpdateOkX := @UpdateBudgetAux.AuthUpdateOkX
abbrev AuthUpdateOkExt := @UpdateBudgetAux.AuthUpdateOkExt
abbrev seq_frame_lsCallInv_pool := @UpdateBudgetAux.seq_frame_lsCallInv_pool
abbrev seq_frame_inImage_pool := @UpdateBudgetAux.seq_frame_inImage_pool
abbrev withStack_withVmPreserved_shim_of_rustAllocShimVm :=
  @UpdateBudgetAux.withStack_withVmPreserved_shim_of_rustAllocShimVm
abbrev withLsCallInv_withVmPreserved_of_withAllocVmPreserved :=
  @UpdateBudgetAux.withLsCallInv_withVmPreserved_of_withAllocVmPreserved
abbrev expose_info_vecU8At := @UpdateBudgetAux.expose_info_vecU8At
abbrev vecBufAt_fold_append := @UpdateBudgetAux.vecBufAt_fold_append
abbrev authUpdatePinned_placed_ok := @UpdateBudgetAux.authUpdatePinned_placed_ok
abbrev authUpdate_placed_ok := @UpdateBudgetAux.authUpdate_placed_ok
abbrev AllocContractsX := @AllocContractsXBudget

/-! ## Fixed-Offset Callee Contracts -/

def SliceConcat2OkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr sliceConcatName)
    ((sliceConcat2Spec M A lim).inImage img)

def HkdfToSliceSpqrOkX (img : Obj.Image) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
    ((withVmPreserved (hkdfToSliceSpqrSpec hkdf)).inImage img)

def HkdfToSliceSpqrOkExt (img : Obj.Image) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
    ((withVmPreserved (hkdfToSliceSpecExt hkdf)).inImage img)

def AllocZeroedWithStackOkX (img : Obj.Image) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr allocZeroedName)
    ((rustCliAllocBudgetSpecWithStackBase M A lim true extHookStack).inImage img)

theorem allocZeroedWithStackOkX_of_hook {img : Obj.Image} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hZero : HookSat ext allocZeroedName (rustCliAllocBudgetSpecBase M A lim true)) :
    AllocZeroedWithStackOkX img M A lim ext := by
  have h0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocZeroedName)
      (rustCliAllocBudgetSpecBase M A lim true) := by
    have h := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := ext)
      (name := allocZeroedName) (hname := allocZeroedName)
      (stub := num% (ls_off% "__rustc::__rust_alloc_zeroed"))
      (k := 0) allocZeroed_fnOff (Nat.add_zero _) (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, allocZeroedName]) hZero
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  exact subroutine_ok_inImage_of_subroutine_ok img
    (subroutine_ok_rustCliAllocBudget_withStackBase (by decide) (by decide) h0)

/-! ## Fixed-Offset Proof (`0x58ac4`) -/

private theorem optCallInv_none (s : State) : OptCallInv none s := trivial

local elab "lift_fetches_withSvc" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut hyps : Array Lean.Meta.Hypothesis := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Arm64.Program.fetch 2 then
          let progE := (ty.getArg! 1).getArg! 0
          if !progE.isAppOfArity ``Arm64.Program.withSvc 2 then
            let prf ← Lean.Meta.mkAppM ``withSvc_fetch_eq
              #[Lean.mkConst ``Arm64.noSyscalls, decl.toExpr]
            let newTy ← Lean.Meta.inferType prf
            hyps := hyps.push { userName := `this, type := newTy, value := prf }
    if !hyps.isEmpty then
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← g.assertHypotheses hyps
      Lean.Elab.Tactic.replaceMainGoal [g']

private theorem sub_ok_at_rebase_off {α : Type} {b : BitVec 64}
    {Hk : String → Option (State → State)} {spec : Spec α}
    (name callee : String) (off : Nat)
    (hoff : libsignalSessionCode.fnOff name + off = libsignalSessionCode.fnOff callee)
    (h : subroutine_ok (libsignalSessionCode.rebase b Hk)
      ((libsignalSessionCode.rebase b Hk).fnAddr callee) spec) :
    subroutine_ok (libsignalSessionCode.rebase b Hk)
      ((libsignalSessionCode.rebase b Hk).fnAddr name + BitVec.ofNat 64 off) spec :=
  sub_ok_at_rebase (name := name) (callee := callee) (k := off) hoff h

private def authHkdfVmSpecAt (stk : Nat) (hkdf : HkdfFn) : Spec HkdfToSliceGhost where
  pre x s := ⌜s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
    s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
    s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
    s.readReg64 .x6 = x.okmA ∧ s.readReg64 .x7 = BitVec.ofNat 64 x.okmLen ∧
    x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
    (¬x.saltRO ∨ x.salt.length ≤ 64) ∧ (¬x.ikmRO ∨ x.ikm.length < 64) ∧
    32 ≤ x.info.length ∧ x.info.length < 55 ∧
    (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
    bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
    bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗ stackAt s.sp stk
  post x s0 sf :=
    ⌜VmPreserved s0 sf ∧ (hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧
      sf.trace = s0.trace⌝ ∗
    bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
    bytesAt x.infoRO x.infoA x.info ∗ (x.okmA ↦ₛ hkdf x.salt x.ikm x.info x.okmLen) ∗
    stackAt s0.sp stk

private def AuthHkdfVmOkAt (stk : Nat) (img : Obj.Image) (hkdf : HkdfFn)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfToSliceName)
    ((authHkdfVmSpecAt stk hkdf).inImage img)

attribute [local irreducible] FitsEvents

private def authUpdatePinnedInImagePostConcrete (img : Obj.Image) (stk : Nat)
    (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    (AuthUpdatePinnedGhost × M.σ) → State → State → SepProp :=
  fun (x, st) s0 sf =>
    ((img.base + bv% (ls_xref% 0x58b0c 0x58b10)) ↦ᵣ Authenticator.updateLabel) ∗
    ((img.base + bv% (ls_xref% 0x58b5c 0x58b60)) ↦ᵣ List.replicate 32 0#8) ∗
    ⌜sf.trace = s0.trace⌝ ∗
    authenticatorAt A.repAlloc x.selfA (x.auth.update F x.ep x.k) ∗
    bytesAt x.kRO x.kA x.k ∗
    A.pool lim (M.stepEvents (authUpdatePinnedEvents x.g x.auth.rootKey.length x.k.length) st) sf ∗
    stackAt s0.sp stk

set_option maxHeartbeats 3200000 in
private theorem authUpdatePinned_ok_gen {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {totalStk hkdfStk extra : Nat}
    (hsplit_top : ∀ sp, stackAt sp totalStk =
      memRegion (sp - BitVec.ofNat 64 totalStk) extra ∗ stackAt sp authUpdateStackX)
    (hjoin_hkdf : ∀ sp, memRegion (sp - BitVec.ofNat 64 totalStk) extra ∗
      stackAt (sp - 160#64) extHookStack = stackAt (sp - 160#64) hkdfStk)
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img M A lim ext)
    (hhkdf : AuthHkdfVmOkAt hkdfStk img (hkdfToSliceUnchecked F) ext)
    (hA : AllocContractsXBudget img M A lim ext)
    (hallocZeroed : AllocZeroedWithStackOkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpecAt totalStk F M A lim).inImage img) := by
  unfold tripleRatchetProgAtExt
  refine subroutine_ok_inImage_rodata2_keep
    (rodata_updateLabel himg) (rodata_zeros32_update himg) ?_
  refine subroutine_ok_post_entails
    (authUpdatePinnedInImagePostConcrete img totalStk F M A lim)
    (fun (x, st) s0 sf => by
      dsimp only [authUpdatePinnedInImagePostConcrete, authUpdatePinnedSpecAt]
      refine sepConj_mono_right (sepConj_mono_right ?_)
      refine Entails.pure_left fun htr => ?_
      refine Entails.sepExists_right
        (authUpdatePinnedEvents x.g x.auth.rootKey.length x.k.length) ?_
      exact Entails.pure_right ⟨htr, rfl⟩ (Entails.refl _))
    ?_
  wpp_init x_st s0
  rcases x_st with ⟨⟨selfA, g, auth, ep, kRO, kA, k⟩, st⟩
  dsimp only [authUpdatePinnedInImagePostConcrete, authUpdatePinnedSpecAt,
    UpdateBudgetAux.authUpdatePinnedSpecAt] at *
  have hinv0 : ImgCallInv img s0 := ⟨h_2, h_1⟩
  have hlen_bound : auth.rootKey.length + k.length < 2 ^ 63 := h_7
  subst h_3 h_4 h_5
  have hfits_all : FitsEvents M lim st
      (authUpdatePinnedEvents g auth.rootKey.length k.length) :=
    h _ rfl
  obtain ⟨hf0, hf1, hf2, hf3, _, hf5, _, _, _, _, hst_final⟩ :=
    fitsEvents_authUpdatePinned_unpack hfits_all
  have h_shim0 : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr authUpdateName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4)))
      ((shimSpecWithStack extHookStack).inImage img) :=
    @shim_opt_of_x img M A lim ext hA authUpdateName
      (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4))
      (by rw [authUpdate_fnOff, shim_fnOff])
  have h_alloc0 : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr authUpdateName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" - 0x58ac4)))
      ((rustCliAllocNoOomSpecWithStackBase M A lim false extHookStack).inImage img) :=
    @allocNoOom_opt_of_x img M A lim ext hA authUpdateName
      (num% (ls_off% "__rustc::__rust_alloc" - 0x58ac4))
      (by rw [authUpdate_fnOff, alloc_fnOff])
  have h_dealloc0 : subroutine_ok (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      ((libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr authUpdateName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)))
      ((rustCliDeallocBudgetExternSpecWithStackBase M A lim extHookStack).inImage img) :=
    @dealloc_opt_of_x img M A lim ext hA authUpdateName
      (num% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4))
      (by rw [authUpdate_fnOff, dealloc_fnOff])
  unfold SliceConcat2OkX at hconcat
  unfold AuthHkdfVmOkAt at hhkdf
  unfold AllocZeroedWithStackOkX at hallocZeroed
  unfold tripleRatchetProgAtExt at hconcat hhkdf hallocZeroed
  have h_concat := sub_ok_at_rebase_off authUpdateName sliceConcatName
    (num% (0x5eab8 - 0x58ac4)) (by rw [authUpdate_fnOff, sliceConcat_fnOff]) hconcat
  have h_hkdf := sub_ok_at_rebase_off authUpdateName hkdfToSliceName
    (num% (0x5de8c - 0x58ac4)) (by rw [authUpdate_fnOff, hkdfToSlice_fnOff]) hhkdf
  have h_allocZeroed := allocNoOomWithStack_inImage_of_budget
    (sub_ok_at_rebase_off authUpdateName allocZeroedName
      (num% (ls_off% "__rustc::__rust_alloc_zeroed" - 0x58ac4))
      (by rw [authUpdate_fnOff, allocZeroed_fnOff]) hallocZeroed)
  clear hconcat hhkdf hA hallocZeroed
  have hfn : libsignalSessionCode.fnOff authUpdateName = 0x58ac4 := authUpdate_fnOff
  code_fetches CryptoVerification.libsignalSessionCode CryptoVerification.SpqrV1.Auth.libsignalSessionBin img.base trapHooks hfn 0x58ac4 428
  have hadrp1 : ((libsignalSessionCode.rebase img.base trapHooks).fnAddr
      authUpdateName + 72#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x58b0c 0x58b10 - 0x58000) =
      img.base + bv% (ls_xref% 0x58b0c 0x58b10) := by
    have hb := ProofLib.ObjectLoad.base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  have hadrp2 : ((libsignalSessionCode.rebase img.base trapHooks).fnAddr
      authUpdateName + 152#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x58b5c 0x58b60 - 0x58000) =
      img.base + bv% (ls_xref% 0x58b5c 0x58b60) := by
    have hb := ProofLib.ObjectLoad.base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base trapHooks).fnAddr authUpdateName :=
    hpc.trans (by rw [Program.fnAddr_rebase, hfn])
  rw [← rebase_trapHooks_fnAddr libsignalSessionCode img.base (Rust.withPanics ext) authUpdateName]
    at h_concat h_hkdf h_shim0 h_alloc0 h_allocZeroed h_dealloc0
  clear himg hfn
  generalize_entry (libsignalSessionCode.rebase img.base trapHooks).fnAddr authUpdateName = entry
  lift_fetches_withSvc
  examples_hide_fetches
  refine SepWPp.rw_pre (by rw [hsplit_top s0.sp, stackAt_authUpdateX_split s0.sp]) ?_
  sep_elim_exists
  refine sepWPp_optImage_rebase_vm (oimg := some img)
    (mid := entry + bv% (0x5eab8 - 0x58ac4)) hinv0 ?_
  refine SepWP.fold
    (authenticatorPinAt_expose_entails A.repAlloc g (s0.readReg64 (.gpr 0#5)) auth)
    (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨⟨hrk_le, hrk_lt, hrk_ptr⟩, ⟨hmk_le, hmk_lt, hmk_ptr⟩⟩
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    ⟨by simp only [wp_norm, arm64_norm], fun hinv1 hvm_seg1 => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg1 (hnext := ?_)
  have hfit_c1 : FitsEnv M lim st
      (SliceConcat2Env
        ⟨s0.sp - 160#64, s0.sp - 112#64, false, g.rootKey.ptr, auth.rootKey,
          kRO, s0.readReg64 (.gpr 2#5), k⟩) := by
    intro evs hevs; rw [hevs]; exact hf0
  wpp_call_inImage_mid h_concat
    ((⟨s0.sp - 160#64, s0.sp - 112#64, false, g.rootKey.ptr, auth.rootKey,
       kRO, s0.readReg64 (.gpr 2#5), k⟩ : SliceConcat2Ghost), st)
    hinv1
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro evs1
  apply SepWPp.exists_elim; intro ptr_ikm
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr1, _, hevs1⟩
  have hevs1_eq : evs1 = sliceConcat2Events (auth.rootKey.length + k.length) := hevs1
  subst hevs1_eq
  refine sepWPp_optImage_rebase_vm (oimg := some img)
    (mid := entry + bv% (0x5eab8 - 0x58ac4)) hF_sf ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 56#64) (s0.readReg64 (.gpr 1#5))))
    (by sep_focus) ?_
  have hstack_sf : stackAt (s0.sp - 160#64) extHookStack = stackAt sf.sp extHookStack := by
    rw [‹sf.sp = s0.sp - 160#64›]
  refine SepWP.fold (Entails.of_eq hstack_sf) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    ⟨by simp only [wp_norm, arm64_norm], fun hinv2 hvm_seg2 => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg2 (hnext := ?_)
  let st1 := M.stepEvents (sliceConcat2Events (auth.rootKey.length + k.length)) st
  have heq53 :
      sliceConcat2Events
        (Authenticator.updateLabel.length + (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length) =
        rustAllocEvents 53 1 := by
    simp [sliceConcat2Events, updateLabel_length, toBEBytes_8_length]
  have hfit_c2 : FitsEnv M lim st1
      (SliceConcat2Env
        ⟨s0.sp - 136#64, s0.sp - 112#64,
          true, img.base + bv% (ls_xref% 0x58b0c 0x58b10), Authenticator.updateLabel,
          false, s0.sp - 56#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5))⟩) := by
    intro evs hevs
    dsimp only [SliceConcat2Env] at hevs
    rw [hevs, heq53]
    exact hf1
  wpp_call_inImage_mid h_concat
    ((⟨s0.sp - 136#64, s0.sp - 112#64,
       true, img.base + bv% (ls_xref% 0x58b0c 0x58b10), Authenticator.updateLabel,
       false, s0.sp - 56#64, toBEBytes 8 (s0.readReg64 (.gpr 1#5))⟩ : SliceConcat2Ghost), st1)
    hinv2
  try simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro evs2
  apply SepWPp.exists_elim; intro ptr_info
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr2, _, hevs2⟩
  have hevs2_eq : evs2 = rustAllocEvents 53 1 := by
    dsimp only [SliceConcat2Env] at hevs2
    rwa [heq53] at hevs2
  subst hevs2_eq
  refine sepWPp_optImage_rebase_vm (oimg := some img)
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4))
    hF_sf_1 ?_
  have hinfo_cap_eq :
      BitVec.ofNat 64
        (Authenticator.updateLabel.length + (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length) =
        53#64 := by
    simp [updateLabel_length, toBEBytes_8_length]
  try rw [hinfo_cap_eq]
  refine SepWP.fold
    (vecU8At_expose_entails A.repAlloc (s0.sp - 160#64)
      (BitVec.ofNat 64 (auth.rootKey.length + k.length)) ptr_ikm (auth.rootKey ++ k))
    (by sep_focus) ?_
  refine SepWP.fold
    (expose_info_vecU8At A.repAlloc s0.sp ptr_info (s0.readReg64 (.gpr 1#5)))
    (by sep_focus) ?_
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  intro hinfo_ptr
  refine SepWP.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hikm_le, hikm_lt, hikm_ptr⟩
  have hikm_len_lt : (auth.rootKey ++ k).length < 2 ^ 63 := Nat.lt_of_le_of_lt hikm_le hikm_lt
  wp_steps
  have hstack_sf1 : stackAt sf.sp extHookStack = stackAt sf_1.sp extHookStack := by
    rw [‹sf_1.sp = sf.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf1) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    ⟨by simp only [wp_norm, arm64_norm], fun hinv3 hvm_seg3 => ?_⟩
  wpp_call_inImage_mid h_shim0 () hinv3
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr_s1, hvm_s1⟩
  refine SepWPp.transport_budgetPool (hvm_seg3.trans hvm_s1) (hnext := ?_)
  refine sepWPp_optImage_rebase_vm (oimg := some img)
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc_zeroed" - 0x58ac4)) hF_sf_2 ?_
  wp_steps
  have hstack_sf2 : stackAt sf_1.sp extHookStack = stackAt sf_2.sp extHookStack := by
    rw [‹sf_2.sp = sf_1.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf2) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    ⟨by simp only [wp_norm, arm64_norm], fun hinv4 hvm_seg4 => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg4 (hnext := ?_)
  let st2 := M.stepEvents (rustAllocEvents 53 1) st1
  have hlay64 : RustLayoutOk 64 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  wpp_call_inImage_mid h_allocZeroed (64, 1, st2) hinv4
  try simp only [↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hacp3, hoom64, _⟩
  have htr3 : sf_3.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, *] using hacp3.2.1
  have hoom64_beq : (sf_3.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom64
  refine sepWPp_optImage_rebase_vm (oimg := some img)
    (mid := entry + bv% (0x5de8c - 0x58ac4)) hF_sf_3 ?_
  refine SepWP.fold
    (pointsToBytes_replicate_64_entails_memRegion (sf_3.readReg64 Reg.x0)) (by sep_focus) ?_
  wp_steps
  have hstack_sf3 :
      memRegion (s0.sp - BitVec.ofNat 64 totalStk) extra ∗ stackAt sf_2.sp extHookStack =
        stackAt sf_3.sp hkdfStk := by
    rw [‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 160#64›,
      hjoin_hkdf s0.sp]
  refine SepWP.fold (Entails.of_eq hstack_sf3) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    ⟨by simp only [wp_norm, arm64_norm], fun hinv5 hvm_seg5 => ?_⟩
  have hinfo_ge :
      32 ≤ (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length := by simp
  have hinfo_lt :
      (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length < 55 := by simp
  have hsalt_ro_ok : ¬true ∨ (List.replicate 32 (0#8 : BitVec 8)).length ≤ 64 :=
    Or.inr (by decide)
  wpp_call_inImage_mid h_hkdf
    (⟨true, img.base + bv% (ls_xref% 0x58b5c 0x58b60), List.replicate 32 0#8,
      false, ptr_ikm, auth.rootKey ++ k,
      false, ptr_info, Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)),
      sf_3.readReg64 Reg.x0, 64⟩ : HkdfToSliceGhost)
    hinv5
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hvm_hkdf, hkdf_len, htr4⟩
  refine SepWPp.transport_budgetPool (hvm_seg5.trans hvm_hkdf) (hnext := ?_)
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hokm_all, hokm_take, hokm_drop⟩ :=
    exists_unpack64_of_length_64_split hkdf_len
  refine sepWPp_optImage_rebase_vm (oimg := some img)
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4))
    hF_sf_4 ?_
  wp_steps
  have hstack_sf4 : stackAt sf_3.sp hkdfStk =
      memRegion (s0.sp - BitVec.ofNat 64 totalStk) extra ∗ stackAt sf_4.sp extHookStack := by
    rw [‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›,
      ‹sf.sp = s0.sp - 160#64›, ← hjoin_hkdf s0.sp]
  refine SepWP.fold (Entails.of_eq hstack_sf4) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    ⟨by simp only [wp_norm, arm64_norm], fun hinv6 hvm_seg6 => ?_⟩
  wpp_call_inImage_mid h_shim0 () hinv6
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨htr_s2, hvm_s2⟩
  refine SepWPp.transport_budgetPool (hvm_seg6.trans hvm_s2) (hnext := ?_)
  refine sepWPp_optImage_rebase_vm (oimg := some img)
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x58ac4)) hF_sf_5 ?_
  wp_steps
  have hstack_sf5 : stackAt sf_4.sp extHookStack = stackAt sf_5.sp extHookStack := by
    rw [‹sf_5.sp = sf_4.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf5) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    ⟨by simp only [wp_norm, arm64_norm], fun hinv7 hvm_seg7 => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg7 (hnext := ?_)
  let st3 := M.stepEvents (rustAllocEvents 64 1) st2
  have hlay32 : RustLayoutOk 32 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
  wpp_call_inImage_mid h_alloc0 (32, 1, st3) hinv7
  try simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hacp6, hoom32_1, _⟩
  have htr6 : sf_6.trace = s0.trace := by
    simpa only [wp_norm, arm64_norm, *] using hacp6.2.1
  have hoom32_1_beq : (sf_6.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom32_1
  let st4 := M.stepEvents (rustAllocEvents 32 1) st3
  refine sepWPp_optImage_rebase_vm (oimg := some img)
    (mid := entry + 228#64) hF_sf_6 ?_
  refine SepWP.fold (Entails.of_eq (hokm_all (sf_3.readReg64 Reg.x0))) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_32_cells (sf_6.readReg64 Reg.x0))) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold (Entails.of_eq (hokm_take (sf_6.readReg64 Reg.x0)).symm) (by sep_focus) ?_
  refine SepWP.fold
    (vecBufAt_fold A.repAlloc g.rootKey.cap g.rootKey.ptr auth.rootKey) (by sep_focus) ?_
  have hstack_sf6 : stackAt sf_5.sp extHookStack = stackAt sf_6.sp extHookStack := by
    rw [‹sf_6.sp = sf_5.sp›]
  refine SepWP.fold (Entails.of_eq hstack_sf6) (by sep_focus) ?_
  refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    ⟨by simp only [wp_norm, arm64_norm], fun hinv8 hvm_seg8 => ?_⟩
  refine SepWPp.transport_budgetPool hvm_seg8 (hnext := ?_)
  let st5 := M.stepEvents (optCapDeallocEvents g.rootKey.cap) st4
  refine seq_frame_inImage_pool
    (mid_pc := entry + 244#64)
    (P_local := fun s_cur =>
      vecBufAt A.repAlloc g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
        A.pool lim st4 s_cur ∗ stackAt sf_6.sp extHookStack)
    (Q_local := fun sm1 =>
      A.pool lim st5 sm1 ∗ stackAt sf_6.sp extHookStack)
    hinv8 (by sep_focus) ?_ ?_
  · by_cases hcap_rk : g.rootKey.cap = 0#64
    · have hst5 : st5 = st4 := by simp [st5, optCapDeallocEvents, UpdateBudgetAux.optCapDeallocEvents, hcap_rk]
      refine sepWP_optImage_rebase_vm (oimg := some img) (mid := entry + 244#64) hinv8 ?_
      refine SepWP.fold (vecBufAt_of_cap_zero A.repAlloc hcap_rk hrk_le) (by sep_focus) ?_
      simp only [hcap_rk, hst5]
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        ⟨by simp only [wp_norm, arm64_norm], fun _ hvm_rk0 => ?_⟩
      refine SepWP.transport_budgetPool hvm_rk0 (hnext := ?_)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by wp_norm_goal,
        by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
        by wp_norm_goal, Entails.refl _⟩
    · have hcap_rk_beq : (g.rootKey.cap == 0#64) = false := beq_false_of_ne hcap_rk
      have hst5 : st5 = M.stepEvents (rustDeallocEvents g.rootKey.cap.toNat 1) st4 := by
        simp [st5, optCapDeallocEvents, UpdateBudgetAux.optCapDeallocEvents, hcap_rk]
      refine sepWP_optImage_rebase_vm (oimg := some img)
        (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hinv8 ?_
      refine SepWP.fold
        (vecBufAt_of_cap_ne_zero A.repAlloc hcap_rk hrk_le hrk_lt) (by sep_focus) ?_
      refine SepWP.pure_left_focus _ (by sep_focus) ?_
      intro hrk_lay
      have ⟨_, _, _⟩ := hrk_lay
      have hrk_rlay : RustLayoutOk g.rootKey.cap.toNat 1 := ⟨hrk_lay, by decide⟩
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        ⟨by simp only [wp_norm, arm64_norm], fun hinv_d1 hvm_d1 => ?_⟩
      refine SepWP.transport_budgetPool hvm_d1 (hnext := ?_)
      rcases hinv_d1 with ⟨hF_d1, hsym_d1⟩
      wp_call h_dealloc0 (g.rootKey.ptr, g.rootKey.cap.toNat, 1, st4)
      rw [← hst5]
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        Entails.refl _⟩
  · intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 hcs_sm1 htr_sm1 hF_sm1
    simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm1 hcs_sm1 htr_sm1
    have hstack_sm1 : stackAt sf_6.sp extHookStack = stackAt sm1.sp extHookStack := by
      rw [hsp_sm1, ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sf_4.sp›, ‹sf_4.sp = sf_3.sp›,
        ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sf_1.sp›, ‹sf_1.sp = sf.sp›, ‹sf.sp = s0.sp - 160#64›]
    rcases hcs_sm1 with ⟨hx19_sm1, hx20_sm1, hx21_sm1, hx22_sm1, hx23_sm1, hx24_sm1,
      hx25_sm1, hx26_sm1, hx27_sm1, hx28_sm1, hx29_sm1, hvregs_sm1⟩
    refine sepWPp_optImage_rebase_vm (oimg := some img)
      (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x58ac4))
      hF_sm1 ?_
    refine SepWP.fold (Entails.of_eq hstack_sm1) (by sep_focus) ?_
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      ⟨by simp only [wp_norm, arm64_norm], fun hinv9 hvm_seg9 => ?_⟩
    wpp_call_inImage_mid h_shim0 () hinv9
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨htr_s3, hvm_s3⟩
    refine SepWPp.transport_budgetPool (hvm_seg9.trans hvm_s3) (hnext := ?_)
    refine sepWPp_optImage_rebase_vm (oimg := some img)
      (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - 0x58ac4)) hF_sf_7 ?_
    wp_steps
    have hstack_sf7 : stackAt sm1.sp extHookStack = stackAt sf_7.sp extHookStack := by
      rw [‹sf_7.sp = sm1.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf7) (by sep_focus) ?_
    refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      ⟨by simp only [wp_norm, arm64_norm], fun hinv10 hvm_seg10 => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg10 (hnext := ?_)
    wpp_call_inImage_mid h_alloc0 (32, 1, st5) hinv10
    try simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_left_focus _ (by sep_focus) ?_
    rintro ⟨hacp8, hoom32_2, _⟩
    have htr8 : sf_8.trace = s0.trace := by
      simpa only [wp_norm, arm64_norm, *] using hacp8.2.1
    have hoom32_2_beq : (sf_8.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom32_2
    let st6 := M.stepEvents (rustAllocEvents 32 1) st5
    refine sepWPp_optImage_rebase_vm (oimg := some img)
      (mid := entry + 292#64) hF_sf_8 ?_
    refine SepWP.fold (Entails.of_eq (memRegion_32_cells (sf_8.readReg64 Reg.x0))) (by sep_focus) ?_
    sep_elim_exists
    wp_steps
    refine SepWP.fold (Entails.of_eq (hokm_drop (sf_8.readReg64 Reg.x0)).symm) (by sep_focus) ?_
    refine SepWP.fold
      (vecBufAt_fold A.repAlloc g.macKey.cap g.macKey.ptr auth.macKey) (by sep_focus) ?_
    have hstack_sf8 : stackAt sf_7.sp extHookStack = stackAt sf_8.sp extHookStack := by
      rw [‹sf_8.sp = sf_7.sp›]
    refine SepWP.fold (Entails.of_eq hstack_sf8) (by sep_focus) ?_
    refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      ⟨by simp only [wp_norm, arm64_norm], fun hinv11 hvm_seg11 => ?_⟩
    refine SepWPp.transport_budgetPool hvm_seg11 (hnext := ?_)
    let st7 := M.stepEvents (optCapDeallocEvents g.macKey.cap) st6
    refine seq_frame_inImage_pool
      (mid_pc := entry + 308#64)
      (P_local := fun s_cur =>
        ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
          vecBufAt A.repAlloc g.macKey.cap g.macKey.ptr auth.macKey ∗
          A.pool lim st6 s_cur ∗ stackAt sf_8.sp extHookStack)
      (Q_local := fun sm2 =>
        ((s0.readReg64 (.gpr 0#5) + 32#64) ↦₆₄ g.macKey.ptr) ∗
          A.pool lim st7 sm2 ∗ stackAt sf_8.sp extHookStack)
      hinv11 (by sep_focus) ?_ ?_
    · by_cases hcap_mk : g.macKey.cap = 0#64
      · have hst7 : st7 = st6 := by simp [st7, optCapDeallocEvents, UpdateBudgetAux.optCapDeallocEvents, hcap_mk]
        refine sepWP_optImage_rebase_vm (oimg := some img) (mid := entry + 308#64) hinv11 ?_
        refine SepWP.fold (vecBufAt_of_cap_zero A.repAlloc hcap_mk hmk_le) (by sep_focus) ?_
        simp only [hcap_mk, hst7]
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          ⟨by simp only [wp_norm, arm64_norm], fun _ hvm_mk0 => ?_⟩
        refine SepWP.transport_budgetPool hvm_mk0 (hnext := ?_)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by wp_norm_goal,
          by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
          by wp_norm_goal, Entails.of_eq (by sep_ac_rfl)⟩
      · have hcap_mk_beq : (g.macKey.cap == 0#64) = false := beq_false_of_ne hcap_mk
        have hst7 : st7 = M.stepEvents (rustDeallocEvents g.macKey.cap.toNat 1) st6 := by
          simp [st7, optCapDeallocEvents, UpdateBudgetAux.optCapDeallocEvents, hcap_mk]
        refine sepWP_optImage_rebase_vm (oimg := some img)
          (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hinv11 ?_
        refine SepWP.fold
          (vecBufAt_of_cap_ne_zero A.repAlloc hcap_mk hmk_le hmk_lt) (by sep_focus) ?_
        refine SepWP.pure_left_focus _ (by sep_focus) ?_
        intro hmk_lay
        have ⟨_, _, _⟩ := hmk_lay
        have hmk_rlay : RustLayoutOk g.macKey.cap.toNat 1 := ⟨hmk_lay, by decide⟩
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          ⟨by simp only [wp_norm, arm64_norm], fun hinv_d2 hvm_d2 => ?_⟩
        refine SepWP.transport_budgetPool hvm_d2 (hnext := ?_)
        rcases hinv_d2 with ⟨hF_d2, hsym_d2⟩
        wp_call h_dealloc0 (g.macKey.ptr, g.macKey.cap.toNat, 1, st6)
        rw [← hst7]
        apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        refine ⟨by simp only [wp_norm, arm64_norm, *],
          by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by sep_ac_rfl)⟩
    · intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 hcs_sm2 htr_sm2 hF_sm2
      simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm2 hcs_sm2 htr_sm2
      have hstack_sm2 : stackAt sf_8.sp extHookStack = stackAt sm2.sp extHookStack := by
        rw [hsp_sm2, ‹sf_8.sp = sf_7.sp›, ‹sf_7.sp = sm1.sp›, hsp_sm1]
      rcases hcs_sm2 with ⟨hx19_sm2, hx20_sm2, hx21_sm2, hx22_sm2, hx23_sm2, hx24_sm2,
        hx25_sm2, hx26_sm2, hx27_sm2, hx28_sm2, hx29_sm2, hvregs_sm2⟩
      refine sepWPp_optImage_rebase_vm (oimg := some img)
        (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hF_sm2 ?_
      refine SepWP.fold (Entails.of_eq hstack_sm2) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (hokm_all (sf_3.readReg64 Reg.x0)).symm) (by sep_focus) ?_
      refine SepWP.fold
        (pointsToBytes_64_entails_memRegion (sf_3.readReg64 Reg.x0) hkdf_len) (by sep_focus) ?_
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        ⟨by simp only [wp_norm, arm64_norm], fun hinv12 hvm_seg12 => ?_⟩
      refine SepWPp.transport_budgetPool hvm_seg12 (hnext := ?_)
      wpp_call_inImage_mid h_dealloc0 (sf_3.readReg64 Reg.x0, 64, 1, st7) hinv12
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      intro htr9
      let st8 := M.stepEvents (rustDeallocEvents 64 1) st7
      have h53_beq : (53#64 == 0#64) = false := by decide
      have hlay53 : RustLayoutOk 53 1 := ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩
      have hmr_info :
          (ptr_info ↦ₛ (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5)))) ⊢
            memRegion ptr_info 53 := by
        have hlen53 :
            (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 53 := by
          simp only [List.length_append, updateLabel_length, toBEBytes_8_length]
        rw [← hlen53]
        exact pointsToBytes_entails_memRegion ptr_info _
      refine sepWPp_optImage_rebase_vm (oimg := some img)
        (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hF_sf_9 ?_
      refine SepWP.fold hmr_info (by sep_focus) ?_
      have hstack_sf9 : stackAt sm2.sp extHookStack = stackAt sf_9.sp extHookStack := by
        rw [‹sf_9.sp = sm2.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf9) (by sep_focus) ?_
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        ⟨by simp only [wp_norm, arm64_norm], fun hinv13 hvm_seg13 => ?_⟩
      refine SepWPp.transport_budgetPool hvm_seg13 (hnext := ?_)
      wpp_call_inImage_mid h_dealloc0 (ptr_info, 53, 1, st8) hinv13
      refine SepWPp.pure_left_focus _ (by sep_focus) ?_
      intro htr10
      let st9 := M.stepEvents (rustDeallocEvents 53 1) st8
      refine sepWPp_optImage_rebase_vm (oimg := some img)
        (mid := entry + 360#64) hF_sf_10 ?_
      refine SepWP.fold
        (vecBufAt_fold_append A.repAlloc (BitVec.ofNat 64 (auth.rootKey.length + k.length))
          ptr_ikm auth.rootKey k) (by sep_focus) ?_
      have hstack_sf10 : stackAt sf_9.sp extHookStack = stackAt sf_10.sp extHookStack := by
        rw [‹sf_10.sp = sf_9.sp›]
      refine SepWP.fold (Entails.of_eq hstack_sf10) (by sep_focus) ?_
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
        ⟨by simp only [wp_norm, arm64_norm], fun hinv14 hvm_seg14 => ?_⟩
      refine SepWPp.transport_budgetPool hvm_seg14 (hnext := ?_)
      let st10 := M.stepEvents (sliceConcat2DeallocEvents (auth.rootKey.length + k.length)) st9
      have hopt_ikm :
          optCapDeallocEvents (BitVec.ofNat 64 (auth.rootKey.length + k.length)) =
            sliceConcat2DeallocEvents (auth.rootKey.length + k.length) :=
        optCapDeallocEvents_ofNat (by omega)
      refine seq_frame_inImage_pool
        (mid_pc := entry + 376#64)
        (P_local := fun s_cur =>
          vecBufAt A.repAlloc (BitVec.ofNat 64 (auth.rootKey.length + k.length))
            ptr_ikm (auth.rootKey ++ k) ∗
            A.pool lim st9 s_cur ∗ stackAt sf_10.sp extHookStack)
        (Q_local := fun sm3 =>
          A.pool lim st10 sm3 ∗ stackAt sf_10.sp extHookStack)
        hinv14 (by sep_focus) ?_ ?_
      · rcases dealloc_vecBuf_cases hikm_le with hcap_ikm | hcap_ikm
        · have hst10 : st10 = st9 := by
            simp only [st10, ← hopt_ikm, optCapDeallocEvents,
              UpdateBudgetAux.optCapDeallocEvents, hcap_ikm, ↓reduceIte, M.stepEvents_nil]
          refine sepWP_optImage_rebase_vm (oimg := some img) (mid := entry + 376#64) hinv14 ?_
          refine SepWP.fold (vecBufAt_of_cap_zero A.repAlloc hcap_ikm hikm_le) (by sep_focus) ?_
          simp only [hcap_ikm, hst10]
          wp_steps
          refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            ⟨by simp only [wp_norm, arm64_norm], fun _ hvm_ikm0 => ?_⟩
          refine SepWP.transport_budgetPool hvm_ikm0 (hnext := ?_)
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by wp_norm_goal,
            by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, and_self],
            by wp_norm_goal, Entails.refl _⟩
        · have hcap_ikm_beq :
              (BitVec.ofNat 64 (auth.rootKey.length + k.length) == 0#64) = false :=
            beq_false_of_ne hcap_ikm
          have hst10 :
              st10 = M.stepEvents
                (rustDeallocEvents (BitVec.ofNat 64 (auth.rootKey.length + k.length)).toNat 1)
                st9 := by
            simp only [st10, ← hopt_ikm, optCapDeallocEvents,
              UpdateBudgetAux.optCapDeallocEvents, hcap_ikm, ↓reduceIte]
          refine sepWP_optImage_rebase_vm (oimg := some img)
            (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" - 0x58ac4)) hinv14 ?_
          refine SepWP.fold
            (vecBufAt_of_cap_ne_zero A.repAlloc hcap_ikm hikm_le hikm_lt) (by sep_focus) ?_
          refine SepWP.pure_left_focus _ (by sep_focus) ?_
          intro hikm_lay
          have ⟨_, _, _⟩ := hikm_lay
          have hikm_rlay :
              RustLayoutOk (BitVec.ofNat 64 (auth.rootKey.length + k.length)).toNat 1 :=
            ⟨hikm_lay, by decide⟩
          wp_steps
          refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
            ⟨by simp only [wp_norm, arm64_norm], fun hinv_d3 hvm_d3 => ?_⟩
          refine SepWP.transport_budgetPool hvm_d3 (hnext := ?_)
          rcases hinv_d3 with ⟨hF_d3, hsym_d3⟩
          wp_call h_dealloc0
            (ptr_ikm, (BitVec.ofNat 64 (auth.rootKey.length + k.length)).toNat, 1, st9)
          rw [← hst10]
          apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          refine ⟨by simp only [wp_norm, arm64_norm, *],
            by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            Entails.refl _⟩
      · intro sm3 hpc_sm3 hrun_sm3 hsp_sm3 hcs_sm3 htr_sm3 _
        have hstack_sm3 : stackAt sf_10.sp extHookStack = stackAt (s0.sp - 160#64) extHookStack := by
          rw [‹sf_10.sp = sf_9.sp›, ‹sf_9.sp = sm2.sp›, hsp_sm2]
        simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *] at hsp_sm3 hcs_sm3 htr_sm3
        rcases hcs_sm3 with ⟨hx19_sm3, hx20_sm3, hx21_sm3, hx22_sm3, hx23_sm3, hx24_sm3,
          hx25_sm3, hx26_sm3, hx27_sm3, hx28_sm3, hx29_sm3, hvregs_sm3⟩
        apply SepWPp.of_sepWP_ret
        refine sepWP_optImage_rebase_vm (mid := s0.readReg64 (.gpr 30#5)) (optCallInv_none sm3) ?_
        refine SepWP.fold (Entails.of_eq hstack_sm3) (by sep_focus) ?_
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_goal)
          ⟨by simp only [wp_norm, arm64_norm], fun _ hvm_ret => ?_⟩
        refine SepWP.transport_budgetPool hvm_ret (hnext := ?_)
        have hbe_len : (toBEBytes 8 (s0.readReg64 (.gpr 1#5))).length = 8 := by simp
        refine SepWP.fold
          (rejoin_stack_authUpdateX s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ hbe_len _ _ _ _ _ _)
          (by sep_focus) ?_
        refine SepWP.fold (Entails.of_eq (hsplit_top s0.sp).symm) (by sep_focus) ?_
        have hrk_new_len :
            (List.take 32
              (hkdfToSliceUnchecked F (List.replicate 32 0#8) (auth.rootKey ++ k)
                (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))) 64)).length =
              32 :=
          take_32_length_of_64 hkdf_len
        have hmk_new_len :
            (List.take 32
              (List.drop 32
                (hkdfToSliceUnchecked F (List.replicate 32 0#8) (auth.rootKey ++ k)
                  (Authenticator.updateLabel ++ toBEBytes 8 (s0.readReg64 (.gpr 1#5))) 64))).length =
              32 :=
          drop_32_take_32_length_of_64 hkdf_len
        have h_auth_fold :=
          authenticatorAt_of_32_32 A.repAlloc (s0.readReg64 (.gpr 0#5))
            (sf_6.readReg64 Reg.x0) (sf_8.readReg64 Reg.x0)
            _ _ hrk_new_len hmk_new_len hoom32_1 hoom32_2
        rw [RustCliAllocBudget.repAlloc_live] at h_auth_fold
        dsimp only [Reg.x0] at h_auth_fold
        refine SepWP.fold h_auth_fold (by sep_focus) ?_
        rw [drop_32_take_32_eq_drop_32_of_length_64 hkdf_len]
        have hst10_eq : st10 =
            M.stepEvents (authUpdatePinnedEvents g auth.rootKey.length k.length) st :=
          hst_final
        rw [hst10_eq]
        dsimp only [Authenticator.update, hkdfToVecUnchecked_eq_hkdfToSliceUnchecked]
        wp_done

/-! ## Public Fixed-Offset Contracts -/

private theorem authHkdf_of_okX {img : Obj.Image} {hkdf : HkdfFn}
    {ext : String → Option (State → State)} (h : HkdfToSliceSpqrOkX img hkdf ext) :
    AuthHkdfVmOkAt extHookStack img hkdf ext := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [Spec.inImage, authHkdfVmSpecAt, withVmPreserved, hkdfToSliceSpqrSpec,
      hkdfToSliceSpec] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have h2 := hpre.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at h2 ⊢
    rcases h2 with ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hs, hi, _, _, hf1, hf2, ho⟩, hrest⟩
    exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hs, hi, hf1, hf2, ho⟩, hrest⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.inImage, authHkdfVmSpecAt, withVmPreserved, hkdfToSliceSpqrSpec,
        hkdfToSliceSpec] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hvm, hpost⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hvm, hpost.1.1, hpost.1.2⟩, hpost.2⟩
    · exact Or.inr (Or.inl ⟨hp, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

private theorem authHkdf_of_okExt {img : Obj.Image} {hkdf : HkdfFn}
    {ext : String → Option (State → State)} (h : HkdfToSliceSpqrOkExt img hkdf ext) :
    AuthHkdfVmOkAt hkdfToSliceStackExt img hkdf ext := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _ =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · dsimp only [Spec.inImage, authHkdfVmSpecAt, withVmPreserved, hkdfToSliceSpecExt] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    refine ⟨hpre.1, ?_⟩
    have h2 := hpre.2
    rw [sepConj_assoc, satisfies_pure_sepConj] at h2 ⊢
    rcases h2 with ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hs, hi, hsro, hiro, hf1, hf2, ho⟩, hrest⟩
    exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, hs, hi, hf1, hf2, ho, hsro, hiro⟩, hrest⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Spec.inImage, authHkdfVmSpecAt, withVmPreserved, hkdfToSliceSpecExt] at hpost ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hvm, hpost⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨⟨hvm, hpost.1.1, hpost.1.2⟩, hpost.2⟩
    · exact Or.inr (Or.inl ⟨hp, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem authUpdatePinned_ok_of_contracts_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img M A lim ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext)
    (hA : AllocContractsXBudget img M A lim ext)
    (hallocZeroed : AllocZeroedWithStackOkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpec F M A lim).inImage img) :=
  authUpdatePinned_ok_gen (extra := 0)
    (fun _ => by rw [ProofLib.memRegion_zero, emp_sepConj])
    (fun _ => by rw [ProofLib.memRegion_zero, emp_sepConj])
    himg hconcat (authHkdf_of_okX hhkdf) hA hallocZeroed

theorem authUpdatePinned_ok_of_contracts_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img M A lim ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext)
    (hA : AllocContractsXBudget img M A lim ext)
    (hallocZeroed : AllocZeroedWithStackOkX img M A lim ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpecExt F M A lim).inImage img) :=
  authUpdatePinned_ok_gen (extra := 1232)
    (fun sp => ProofLib.stackAt_split_bottom sp authUpdateStackX 1232 (by decide))
    (fun sp => by
      have h := ProofLib.stackAt_split_bottom (sp - 160#64) extHookStack 1232 (by decide)
      have hsub : sp - 160#64 - BitVec.ofNat 64 (extHookStack + 1232) =
          sp - BitVec.ofNat 64 authUpdateStackExt := by
        dsimp only [extHookStack, authUpdateStackExt, hkdfToSliceStackExt]; bv_kernel
      have hstk : stackAt (sp - 160#64) (extHookStack + 1232) =
          stackAt (sp - 160#64) hkdfToSliceStackExt := rfl
      exact ((hstk.symm.trans h).trans (by rw [hsub])).symm)
    himg hconcat (authHkdf_of_okExt hhkdf) hA hallocZeroed

private theorem authUpdate_ok_of_pinned {img : Obj.Image} {stk : Nat}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hpinned : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdatePinnedSpecAt stk F M A lim).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr authUpdateName)
      ((authUpdateSpecAt stk F M A lim).inImage img) := by
  refine subroutine_ok.of_codeLoaded fun (x, st) R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [Spec.inImage, authUpdateSpecAt, UpdateBudgetAux.authUpdateSpecAt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg_s0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hfit⟩, hpre⟩
  have h1 : s0.mem ⊨ authenticatorAt A.repAlloc x.selfA x.auth ∗
      (bytesAt x.kRO x.kA x.k ∗ A.pool lim st s0 ∗ stackAt s0.sp stk ∗ R) := by
    have hEq :
        authenticatorAt A.repAlloc x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
          A.pool lim st s0 ∗ stackAt s0.sp stk ∗ R =
        authenticatorAt A.repAlloc x.selfA x.auth ∗
          (bytesAt x.kRO x.kA x.k ∗ A.pool lim st s0 ∗ stackAt s0.sp stk ∗ R) := by
      sep_ac_rfl
    simpa only [sepConj_assoc, hEq] using hpre
  rw [authenticatorAt_eq_exists_pinned A.repAlloc x.selfA x.auth,
    sepExists_sepConj_left, satisfies_sepExists] at h1
  rcases h1 with ⟨g, hg⟩
  let xp : AuthUpdatePinnedGhost := ⟨x.selfA, g, x.auth, x.ep, x.kRO, x.kA, x.k⟩
  have hfit_pin : FitsEnv M lim st (AuthUpdatePinnedEnv xp) := by
    intro evs hevs
    rw [hevs]
    exact fitsEvents_pinned_of_fitsEnv_authUpdateEnv g hfit
  have hpre_pin :
      s0.mem ⊨ ((authUpdatePinnedSpecAt stk F M A lim).inImage img).pre (xp, st) s0 ∗ R := by
    dsimp only [Spec.inImage, authUpdatePinnedSpecAt, UpdateBudgetAux.authUpdatePinnedSpecAt, xp]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg_s0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hlen, hfit_pin⟩, ?_⟩
    have hEq :
        (authenticatorPinAt A.repAlloc g x.selfA x.auth ∗ bytesAt x.kRO x.kA x.k ∗
          A.pool lim st s0 ∗ stackAt s0.sp stk) ∗ R =
        authenticatorPinAt A.repAlloc g x.selfA x.auth ∗
          (bytesAt x.kRO x.kA x.k ∗ A.pool lim st s0 ∗ stackAt s0.sp stk ∗ R) := by
      sep_ac_rfl
    rwa [hEq]
  refine hpinned.mono_outcome (xp, st) R s0 hpc hrun hpre_pin hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, authUpdatePinnedSpecAt, UpdateBudgetAux.authUpdatePinnedSpecAt,
      authUpdateSpecAt, UpdateBudgetAux.authUpdateSpecAt, xp] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨htr, hevs⟩, hrest⟩
    rw [hevs]
    exact ⟨⟨htr, authUpdatePinnedEvents_mem_authUpdateEnv g x⟩, by rwa [← hevs]⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- `<spqr::authenticator::Authenticator>::update` (`0x589e0`, 107 instructions) meets
`(authUpdateSpec F M A lim).inImage img` (`AuthUpdateOkX`). -/
theorem authUpdate_ok_of_contracts_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img M A lim ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext)
    (hA : AllocContractsXBudget img M A lim ext)
    (hallocZeroed : AllocZeroedWithStackOkX img M A lim ext) :
    AuthUpdateOkX img F M A lim ext :=
  authUpdate_ok_of_pinned (authUpdatePinned_ok_of_contracts_x himg hconcat hhkdf hA hallocZeroed)

theorem authUpdate_ok_of_hook_x {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img M A lim ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext)
    (hA : AllocContractsXBudget img M A lim ext)
    (hZero : HookSat ext allocZeroedName (rustCliAllocBudgetSpecBase M A lim true)) :
    AuthUpdateOkX img F M A lim ext :=
  authUpdate_ok_of_contracts_x himg hconcat hhkdf hA (allocZeroedWithStackOkX_of_hook hZero)

theorem authUpdate_ok_of_contracts_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img M A lim ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext)
    (hA : AllocContractsXBudget img M A lim ext)
    (hallocZeroed : AllocZeroedWithStackOkX img M A lim ext) :
    AuthUpdateOkExt img F M A lim ext :=
  authUpdate_ok_of_pinned (authUpdatePinned_ok_of_contracts_ext himg hconcat hhkdf hA hallocZeroed)

theorem authUpdate_ok_of_hook_ext {img : Obj.Image}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat : SliceConcat2OkX img M A lim ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext)
    (hA : AllocContractsXBudget img M A lim ext)
    (hZero : HookSat ext allocZeroedName (rustCliAllocBudgetSpecBase M A lim true)) :
    AuthUpdateOkExt img F M A lim ext :=
  authUpdate_ok_of_contracts_ext himg hconcat hhkdf hA (allocZeroedWithStackOkX_of_hook hZero)

end LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget
