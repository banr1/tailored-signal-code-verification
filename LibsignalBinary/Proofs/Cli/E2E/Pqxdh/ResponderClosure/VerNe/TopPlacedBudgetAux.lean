/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DecDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopMovesDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopSegsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
meta import Lean -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Version-Mismatch Envelopes, Bridges, and Block-`518` Segments

Defines the loop and end-to-end allocation envelopes (`VerNeLoopEnv`, `VerNeTopEnv`), spatial
bridges between `PrevDec` and `VerNe` under `RustCliAllocBudget M`, `VmPreserved`-carrying `memcpy`
and allocator-shim contract adapters, and budget-synchronized Block-`518` proofs for the loop head
(`+0x1e78 → +0x1ee8`) and `memcpy` chain (`+0x2620 → +0x1fd4`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsρ lsmpl)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8)
open CryptoVerification.LibsignalTripleRatchet (rootStack sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (growOneSpeStack)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe (
  hdrP_coro_eq overDecScratchPost overDecScratchPre overDecStackX overPrevElemAt overPrevMovesSS
  prevVecAt prevVecAt_one_eq_elemAt
)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ prostSSGQAt)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
  SeqEnv VmPreserved fitsEvents_append rustAllocEvents
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefsBudget (
  OverPrevDecodeEnv overDecScratchPostBudget overPrevElemAtBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (VerNeS1Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (
  VerNeTailEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  framelessMemcpyBudgetSpec noAllocShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)

local elab "erase_hkdf_arm64_norm" : command => Lean.Elab.Command.liftCoreM do
  for n in [``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
            ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592] do
    Lean.Attribute.erase n `arm64_norm
erase_hkdf_arm64_norm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs

local elab "clear_vm_and_nsp" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let mut g ← Lean.Elab.Tactic.getMainGoal
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut fvars : Array Lean.FVarId := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty := (← Lean.instantiateMVars decl.type).consumeMData
        if ty.isAppOf ``VmPreserved || ty.isAppOf ``ProofLib.NonSyscallPreserved then
          fvars := fvars.push decl.fvarId
    for fv in fvars.reverse do
      g ← g.tryClear fv
    Lean.Elab.Tactic.replaceMainGoal [g]

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  clear_vm_and_nsp
))

/-! ## Allocation envelopes (`VerNeLoopEnv`, `VerNeTopEnv`) and non-vacuity -/

/-- Allocation envelope of the 1-element `previous_sessions` loop (`+0x1e78 → +0x2cfc`):
inlined `SessionStructure::decode` on `enc` (`OverPrevDecodeEnv enc`) followed by free-only
decoded-session drop (`FreeOnlyEvs`). -/
def VerNeLoopEnv (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (OverPrevDecodeEnv enc) FreeOnlyEvs

/-- End-to-end allocation envelope of Stage P3/P4 `VerNe` (`+0x1e04 → s0.readReg64 .x30`):
`VerNeS1Env` (`+0x1e04 → +0x1e78`) followed by `VerNeLoopEnv enc` (`+0x1e78 → +0x2cfc`) followed
by `VerNeTailEnv` (`+0x2cfc → s0.readReg64 .x30`). -/
def VerNeTopEnv (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv VerNeS1Env (SeqEnv (VerNeLoopEnv enc) VerNeTailEnv)

theorem verNeLoopEnv_of_parts {enc : List (BitVec 8)} {evs_dec evs_err : List AllocEvent}
    (hd : OverPrevDecodeEnv enc evs_dec) (he : FreeOnlyEvs evs_err) :
    VerNeLoopEnv enc (evs_dec ++ evs_err) :=
  Or.inr ⟨evs_dec, evs_err, rfl, hd, he⟩

theorem verNeTopEnv_of_parts {enc : List (BitVec 8)} {evs1 evs2 evs3 : List AllocEvent}
    (h1 : VerNeS1Env evs1) (h2 : VerNeLoopEnv enc evs2) (h3 : VerNeTailEnv evs3) :
    VerNeTopEnv enc (evs1 ++ evs2 ++ evs3) := by
  rw [List.append_assoc]
  exact Or.inr ⟨evs1, evs2 ++ evs3, rfl, h1, Or.inr ⟨evs2, evs3, rfl, h2, h3⟩⟩

theorem fits_seq_left {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop}
    (h : FitsEnv M lim st (SeqEnv E₁ E₂)) :
    FitsEnv M lim st E₁ :=
  fun evs h1 => h evs (Or.inl h1)

theorem fits_seq_right {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop}
    (h : FitsEnv M lim st (SeqEnv E₁ E₂)) {evs₁ : List AllocEvent} (h1 : E₁ evs₁) :
    FitsEnv M lim (M.stepEvents evs₁ st) E₂ :=
  fun evs₂ h2 =>
    ((fitsEvents_append M lim evs₁ evs₂ st).mp
      (h (evs₁ ++ evs₂) (Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩))).2

theorem fitsS1_of_fitsTop {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} (h : FitsEnv M lim st0 (VerNeTopEnv enc)) :
    FitsEnv M lim st0 VerNeS1Env :=
  fits_seq_left h

theorem fitsLoop_of_fitsTop {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} {evs1 : List AllocEvent}
    (h : FitsEnv M lim st0 (VerNeTopEnv enc)) (h1 : VerNeS1Env evs1) :
    FitsEnv M lim (M.stepEvents evs1 st0) (VerNeLoopEnv enc) :=
  fits_seq_left (fits_seq_right h h1)

theorem fitsDec_of_fitsLoop {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} (h : FitsEnv M lim st0 (VerNeLoopEnv enc)) :
    FitsEnv M lim st0 (OverPrevDecodeEnv enc) :=
  fits_seq_left h

theorem fitsTail_of_fitsTop {M : AllocCostModel} {lim : BudgetLimits} {st0 : M.σ}
    {enc : List (BitVec 8)} {evs1 evs2 : List AllocEvent}
    (h : FitsEnv M lim st0 (VerNeTopEnv enc))
    (h1 : VerNeS1Env evs1) (h2 : VerNeLoopEnv enc evs2) :
    FitsEnv M lim (M.stepEvents evs2 (M.stepEvents evs1 st0)) VerNeTailEnv :=
  fits_seq_right (fits_seq_right h h1) h2

theorem verNeLoopEnv_nonvacuous (enc : List (BitVec 8)) : VerNeLoopEnv enc [] :=
  Or.inl (BoundedRustEvs.nil _ _)

theorem verNeTopEnv_nonvacuous (enc : List (BitVec 8)) :
    VerNeTopEnv enc (rustAllocEvents 192 8 ++ rustAllocEvents 17 1) :=
  Or.inr ⟨rustAllocEvents 192 8, rustAllocEvents 17 1, rfl, Or.inl rfl,
    Or.inr ⟨[], rustAllocEvents 17 1, rfl, verNeLoopEnv_nonvacuous enc, Or.inl rfl⟩⟩

/-! ## Spatial bridges (`PrevDec` and `VerNe` at `RustCliAllocBudget M`) -/

theorem overDecScratchPre_eq_prevDec_pl (sp : BitVec 64) :
    overDecScratchPre sp =
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecScratchPre sp := by
  have h920 :
      memRegion (sp + 0x920#64) 112 =
        memRegion (sp + 0x920#64) 16 ∗ memRegion (sp + 0x930#64) 96 :=
    ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 16) (k := 96) (b' := sp + 0x930#64)
      rfl (by bv_omega) (by decide)
  have h930 :
      memRegion (sp + 0x930#64) 344 =
        memRegion (sp + 0x930#64) 96 ∗ memRegion (sp + 0x990#64) 248 :=
    ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 96) (k := 248) (b' := sp + 0x990#64)
      rfl (by bv_omega) (by decide)
  have h990 :
      memRegion (sp + 0x990#64) 256 =
        memRegion (sp + 0x990#64) 248 ∗ memRegion (sp + 0xa88#64) 8 :=
    ProofLib.memRegion_split' (b := sp + 0x990#64) (n := 248) (k := 8) (b' := sp + 0xa88#64)
      rfl (by bv_omega) (by decide)
  unfold overDecScratchPre
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecScratchPre
  rw [h920, h930, h990]
  sep_ac_rfl

theorem prevDec_scratchPostBudget_eq_pl {M : AllocCostModel} (A : RustCliAllocBudget M)
    (sp : BitVec 64) (v : SSGQ) :
    overDecScratchPostBudget A sp v =
      prostSSGQAt A.repAlloc (sp + 0x930#64) v ∗ overDecScratchPost sp := by
  unfold overDecScratchPostBudget
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overDecScratchPostExt
    overDecScratchPost
  sep_ac_rfl

theorem overPrevElemAt_eq_exists_prevDecBudget_pl {M : AllocCostModel} (A : RustCliAllocBudget M)
    (prevCap prevPtr : BitVec 64) (enc : List (BitVec 8)) :
    overPrevElemAt A.repAlloc prevCap prevPtr enc =
      ∃∗ encCap : BitVec 64, ∃∗ encPtr : BitVec 64,
        overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc := by
  unfold overPrevElemAt overPrevElemAtBudget
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.overPrevElemAtExt vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem prevDecBudget_elemAt_entails_overPrevElemAt_pl {M : AllocCostModel}
    (A : RustCliAllocBudget M) (prevCap prevPtr encCap encPtr : BitVec 64)
    (enc : List (BitVec 8)) :
    overPrevElemAtBudget A prevCap prevPtr encCap encPtr enc ⊢
      overPrevElemAt A.repAlloc prevCap prevPtr enc := by
  rw [overPrevElemAt_eq_exists_prevDecBudget_pl]
  exact Entails.sepExists_right encCap (Entails.sepExists_right encPtr (Entails.refl _))

theorem prevVecAt_open_eq_top_pl (A : RustAlloc) (coroPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (hcap : prevCap ≠ 0#64) :
    prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] =
      ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
      ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗ overPrevElemAt A prevCap prevPtr enc := by
  rw [prevVecAt_one_eq_elemAt A (coroPtr + 0xe0#64) prevCap prevPtr enc hcap, hdrP_coro_eq]
  sep_ac_rfl

theorem stackAt_sub_eq_top_pl (sp : BitVec 64) (big small : Nat)
    (h1 : small ≤ big := by decide) (h2 : big ≤ 2 ^ 64 := by decide) :
    stackAt sp big = memRegion (sp - BitVec.ofNat 64 big) (big - small) ∗ stackAt sp small := by
  have h := ProofLib.stackAt_split_bottom sp small (big - small) (by omega)
  rwa [Nat.add_sub_of_le h1] at h

theorem loopScratch_to_decPre_top_pl (sp : BitVec 64) :
    memRegion (sp + 0x538#64) 1016 ∗ memRegion (sp + 0x930#64) 48 ∗
    memRegion (sp + 0x960#64) 48 ∗ memRegion (sp + 0x990#64) 256 ∗
    memRegion (sp + 0xa90#64) 344 ∗ memRegion (sp + 0xbe8#64) 136 =
      memRegion (sp + 0x538#64) 40 ∗ memRegion (sp + 0x560#64) 320 ∗
      memRegion (sp + 0x6a0#64) 320 ∗ memRegion (sp + 0x7e0#64) 320 ∗
      overDecScratchPre sp := by
  have h538 :
      memRegion (sp + 0x538#64) 1016 =
        memRegion (sp + 0x538#64) 40 ∗ memRegion (sp + 0x560#64) 320 ∗
        memRegion (sp + 0x6a0#64) 320 ∗ memRegion (sp + 0x7e0#64) 320 ∗
        memRegion (sp + 0x920#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x538#64) (n := 40) (k := 976) (b' := sp + 0x560#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x560#64) (n := 320) (k := 656) (b' := sp + 0x6a0#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x6a0#64) (n := 320) (k := 336) (b' := sp + 0x7e0#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x7e0#64) (n := 320) (k := 16) (b' := sp + 0x920#64)
          rfl (by bv_omega) (by decide)]
  have h990 :
      memRegion (sp + 0x990#64) 256 =
        memRegion (sp + 0x990#64) 248 ∗ memRegion (sp + 0xa88#64) 8 :=
    ProofLib.memRegion_split' (b := sp + 0x990#64) (n := 248) (k := 8) (b' := sp + 0xa88#64)
      rfl (by bv_omega) (by decide)
  have h930 :
      memRegion (sp + 0x930#64) 344 =
        memRegion (sp + 0x930#64) 48 ∗ memRegion (sp + 0x960#64) 48 ∗
        memRegion (sp + 0x990#64) 248 := by
    rw [ProofLib.memRegion_split' (b := sp + 0x930#64) (n := 48) (k := 296) (b' := sp + 0x960#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp + 0x960#64) (n := 48) (k := 248) (b' := sp + 0x990#64)
          rfl (by bv_omega) (by decide)]
  unfold overDecScratchPre; rw [h538, h990, h930]; sep_ac_rfl

theorem decScratchPost_join_930_top_pl (sp : BitVec 64) :
    overDecScratchPost sp ∗ memRegion (sp + 0x930#64) 344 = overDecScratchPre sp := by
  unfold overDecScratchPost overDecScratchPre; sep_ac_rfl

theorem mem920_16_split_top_pl (sp : BitVec 64) :
    memRegion (sp + 0x920#64) 16 =
      ∃∗ u920 : BitVec 64, ((sp + 0x920#64) ↦₆₄ u920) ∗ memRegion (sp + 0x928#64) 8 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 8) (k := 8) (b' := sp + 0x928#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x920#64), sepExists_sepConj_left]

theorem mem920_16_fold_top_pl (sp w : BitVec 64) :
    ((sp + 0x920#64) ↦₆₄ w) ∗ memRegion (sp + 0x928#64) 8 ⊢ memRegion (sp + 0x920#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x920#64) (n := 8) (k := 8) (b' := sp + 0x928#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

theorem slot3e0_344_fold_top_pl (sp w : BitVec 64) :
    ((sp + 0x3e0#64) ↦₆₄ w) ∗ memRegion (sp + 0x3e8#64) 336 ⊢ memRegion (sp + 0x3e0#64) 344 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 8) (k := 336) (b' := sp + 0x3e8#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)

theorem stack_bottom_join_top_pl (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - overDecStackX) ∗
    memRegion (sp - BitVec.ofNat 64 overDecStackX) (overDecStackX - growOneSpeStack) =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) :=
  (ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 rootStack)
    (n := rootStack - overDecStackX)
    (k := overDecStackX - growOneSpeStack)
    (b' := sp - BitVec.ofNat 64 overDecStackX)
    (by decide) (by dsimp only [rootStack, overDecStackX]; bv_omega) (by decide)).symm

/-! ## `VmPreserved`-carrying `memcpy` and shim contract bridges -/

/-- Stack-framed `memcpy` contract with a single pure postcondition atom carrying `VmPreserved`
for `wp_call` + `SepWP.transport_budgetPool`. -/
def verNeMemcpyStackSpec (hookStack : Nat := allocHookStack) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := (sessionMemcpySpec hookStack).pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack

theorem subroutine_ok_verNeMemcpy_of_sessionMemcpyBudget {P : Program} {a : BitVec 64}
    {hookStack : Nat} (h : subroutine_ok P a (sessionMemcpyBudgetSpec hookStack)) :
    subroutine_ok P a (verNeMemcpyStackSpec hookStack) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun ⟨dst, src, bs⟩ R s0 sf hq => ?_)
  dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec, verNeMemcpyStackSpec] at hq ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.2.1.1, hq.2.1.2, hq.1⟩, hq.2.2⟩

theorem hookSat_verNeMemcpy_of_frameless {H : String → Option (State → State)}
    {sym : String} (hookStack : Nat) (h : HookSat H sym framelessMemcpyBudgetSpec) :
    HookSat H sym (verNeMemcpyStackSpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [verNeMemcpyStackSpec, sessionMemcpySpec, libcMemcpySpec,
      framelessMemcpyBudgetSpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [verNeMemcpyStackSpec, framelessMemcpyBudgetSpec] at hpost ⊢
    ac_nf at hpost ⊢

theorem hookSat_noAllocShimBudget_of_rustAllocShimVm {H : String → Option (State → State)}
    {sym : String} (h : HookSat H sym rustAllocShimVmSpec) :
    HookSat H sym noAllocShimBudgetSpec := by
  obtain ⟨f, hf, hsat⟩ := h
  refine ⟨f, hf, fun _ R s0 hrun hpre hal => ?_⟩
  obtain ⟨hret, hcc, hout⟩ := hsat () R s0 hrun hpre hal
  refine ⟨hret, hcc, ?_⟩
  rcases hout with ⟨h1, h2, hpost⟩ | hrest
  · refine Or.inl ⟨h1, h2, ?_⟩
    dsimp only [rustAllocShimVmSpec, noAllocShimBudgetSpec] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.1.2.1, hpost.1.2⟩, hpost.2⟩
  · exact Or.inr hrest

/-! ## Budget-synchronized Block-`518` loop head and `memcpy` chain -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded loop head (`(blkPl_518).base + 0x1e78 → (blkPl_518).base + 0x1ee8`) on
`lsProg_518 ext` when `len = 1#64`, transporting `A.pool lim st s` to `A.pool lim st s1`. -/
theorem overPrevLoop_head_cli_placed_budget_wp [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (st : M.σ) (s : State) (coroPtr prevCap prevPtr u3e0 wd0 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1e78#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ee8#64) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0) ∗
       A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64)) ∗
          A.pool lim st s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.sp + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x27 = prevPtr ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1ee8#64)
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨Entails.of_eq (by sep_ac_rfl),
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

private theorem entails_replace_sub_mv_pl {P A A' F Q : SepProp}
    (hA : A ⊢ A') (hP : P = A ∗ F) (hQ : Q = A' ∗ F) : P ⊢ Q := by
  rw [hP, hQ]; exact sepConj_mono_left hA

private theorem cmn_1_ne_zero_pl {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    (w0 + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; bv_omega

private theorem cmn_2_ne_zero_pl {w0 : BitVec 64} (hw0 : w0.toNat < 2 ^ 63) :
    (w0 + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; bv_omega

private theorem ss320_bytes_eq_pl (sp : BitVec 64) (r1 r2 : List (BitVec 8))
    (hr1 : r1.length = 304) :
    (((sp + 0x948#64) ↦ₛ r1) ∗
     ((sp + 0xa78#64) ↦₃₂ 4#32) ∗
     ((sp + 0xa7c#64) ↦ₛ r2)) =
    ((sp + 0x948#64) ↦ₛ (r1 ++ unpack32 4#32 ++ r2)) := by
  have e1 : sp + 0x948#64 + BitVec.ofNat 64 304 = sp + 0xa78#64 := by bv_omega
  have e2 : sp + 0xa78#64 + BitVec.ofNat 64 4 = sp + 0xa7c#64 := by bv_omega
  simp only [List.append_assoc]
  rw [pointsToBytes_append, hr1, e1, pointsToBytes_append, unpack32_length, e2,
      ← pointsTo32_eq_pointsToBytes]

private theorem overPrevMovesSS_eq_cells_pl (sp w0 w1 w2 : BitVec 64) (r1 r2 : List (BitVec 8)) :
    overPrevMovesSS (sp + 0x930#64) w0 w1 w2 r1 r2 =
      (((sp + 0x930#64) ↦₆₄ w0) ∗ ((sp + 0x938#64) ↦₆₄ w1) ∗ ((sp + 0x940#64) ↦₆₄ w2) ∗
       ((sp + 0x948#64) ↦ₛ r1) ∗ ((sp + 0xa78#64) ↦₃₂ 4#32) ∗ ((sp + 0xa7c#64) ↦ₛ r2)) := by
  dsimp only [overPrevMovesSS]
  have e1 : sp + 0x930#64 + 8#64 = sp + 0x938#64 := by bv_omega
  have e2 : sp + 0x930#64 + 0x10#64 = sp + 0x940#64 := by bv_omega
  have e3 : sp + 0x930#64 + 0x18#64 = sp + 0x948#64 := by bv_omega
  have e4 : sp + 0x930#64 + 0x148#64 = sp + 0xa78#64 := by bv_omega
  have e5 : sp + 0x930#64 + 0x14c#64 = sp + 0xa7c#64 := by bv_omega
  rw [e1, e2, e3, e4, e5]

private theorem overPrevMovesSS_merge_eq_pl (sp w0 w1 w2 : BitVec 64) (r1 r2 : List (BitVec 8))
    (hr1 : r1.length = 304) :
    overPrevMovesSS (sp + 0x930#64) w0 w1 w2 r1 r2 =
      (((sp + 0x930#64) ↦₆₄ w0) ∗ ((sp + 0x938#64) ↦₆₄ w1) ∗ ((sp + 0x940#64) ↦₆₄ w2) ∗
       ((sp + 0x948#64) ↦ₛ (r1 ++ unpack32 4#32 ++ r2))) := by
  rw [overPrevMovesSS_eq_cells_pl, ← ss320_bytes_eq_pl sp r1 r2 hr1]

private theorem pointsToBytes_320_entails_memRegion_pl (p : BitVec 64) (bs : List (BitVec 8))
    (hbs : bs.length = 320) :
    (p ↦ₛ bs) ⊢ memRegion p 320 := by
  rw [← hbs]
  exact pointsToBytes_entails_memRegion p bs

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `memcpy` chain & version load
(`(blkPl_518).base + 0x2620 → (blkPl_518).base + 0x1fd4`) on `lsProg_518 ext`, transporting
`A.pool lim st s` to `A.pool lim st sf` across all five `memcpy` calls. -/
theorem overPrevMoves_cli_placed_budget_ok [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ "memcpy") (verNeMemcpyStackSpec allocHookStack))
    (st : M.σ) (s : State) (w0 w1 w2 u920 : BitVec 64) (r1 r2 : List (BitVec 8))
    (hw0 : w0.toNat < 2 ^ 63) (hr1 : r1.length = 304) (hr2 : r2.length = 12)
    (hpc : s.pc = (blkPl_518).base + 0x2620#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx21 : s.readReg64 .x21 = s.sp + 0x930#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1fd4#64) s
      (overPrevMovesSS (s.sp + 0x930#64) w0 w1 w2 r1 r2 ∗
       memRegion (s.sp + 0x560#64) 320 ∗
       memRegion (s.sp + 0x6a0#64) 320 ∗
       memRegion (s.sp + 0x7e0#64) 320 ∗
       ((s.sp + 0x920#64) ↦₆₄ u920) ∗
       A.pool lim st s ∗
       stackAt s.sp allocHookStack)
      (fun sf P_f =>
        (P_f ⊢
          overPrevMovesSS (s.sp + 0x930#64) w0 w1 w2 r1 r2 ∗
          memRegion (s.sp + 0x560#64) 320 ∗
          memRegion (s.sp + 0x6a0#64) 320 ∗
          memRegion (s.sp + 0x7e0#64) 320 ∗
          ((s.sp + 0x920#64) ↦₆₄ s.readReg64 .x26) ∗
          A.pool lim st sf ∗
          stackAt s.sp allocHookStack) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x8 = 4#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  let bs := r1 ++ unpack32 4#32 ++ r2
  have hbs : bs.length = 320 := by
    simp only [bs, List.length_append, hr1, hr2, unpack32_length]
  have hcmn1 : (w0 + 1#64 == 0#64) = false := cmn_1_ne_zero_pl hw0
  have hcmn2 : (w0 + 2#64 == 0#64) = false := cmn_2_ne_zero_pl hw0
  rw [overPrevMovesSS_merge_eq_pl s.sp w0 w1 w2 r1 r2 hr1]
  change SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1fd4#64) s
    ((((s.sp + 0x930#64) ↦₆₄ w0) ∗ ((s.sp + 0x938#64) ↦₆₄ w1) ∗ ((s.sp + 0x940#64) ↦₆₄ w2) ∗
      ((s.sp + 0x948#64) ↦ₛ bs)) ∗
      memRegion (s.sp + 0x560#64) 320 ∗ memRegion (s.sp + 0x6a0#64) 320 ∗
      memRegion (s.sp + 0x7e0#64) 320 ∗ ((s.sp + 0x920#64) ↦₆₄ u920) ∗
      A.pool lim st s ∗ stackAt s.sp allocHookStack) _
  conv => arg 4; rw [← hbs]
  simp only [sepConj_assoc]
  have hx21' : s.readReg64 (Reg.gpr 21#5) = s.sp + 0x930#64 := hx21
  have h948 : s.sp + 0x930#64 + 0x18#64 = s.sp + 0x948#64 := by bv_omega
  have hlen_nat : (0x140#64).toNat = bs.length := hbs.symm
  wp_steps_sync_518 ext (lsρ "memcpy")
  wp_call hmemcpy (s.sp + 0x7e0#64, s.sp + 0x948#64, bs)
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  clear_vm_and_nsp
  wp_steps_sync_518 ext (lsρ "memcpy")
  wp_call hmemcpy (s.sp + 0x6a0#64, s.sp + 0x7e0#64, bs)
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  clear_vm_and_nsp
  wp_steps_sync_518 ext (lsρ "memcpy")
  wp_call hmemcpy (s.sp + 0x560#64, s.sp + 0x6a0#64, bs)
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  clear_vm_and_nsp
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_entails_memRegion (s.sp + 0x7e0#64) bs)
      (by sep_focus) rfl) ?_
  wp_steps_sync_518 ext (lsρ "memcpy")
  wp_call hmemcpy (s.sp + 0x7e0#64, s.sp + 0x560#64, bs)
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  clear_vm_and_nsp
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_entails_memRegion (s.sp + 0x948#64) bs)
      (by sep_focus) rfl) ?_
  wp_steps_sync_518 ext (lsρ "memcpy")
  wp_call hmemcpy (s.sp + 0x948#64, s.sp + 0x7e0#64, bs)
  refine ProofLib.SepWP.transport_budgetPool ‹VmPreserved _ _› (hnext := ?_)
  clear_vm_and_nsp
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (Entails.of_eq (ss320_bytes_eq_pl s.sp r1 r2 hr1).symm)
      (by sep_focus) rfl) ?_
  simp only [sepConj_assoc]
  wp_steps_sync_518 ext ((blkPl_518).base + 0x1fd4#64)
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_320_entails_memRegion_pl (s.sp + 0x560#64) bs hbs)
      (by sep_focus) rfl) ?_
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_320_entails_memRegion_pl (s.sp + 0x6a0#64) bs hbs)
      (by sep_focus) rfl) ?_
  refine SepWP.weaken_pre
    (entails_replace_sub_mv_pl
      (pointsToBytes_320_entails_memRegion_pl (s.sp + 0x7e0#64) bs hbs)
      (by sep_focus) rfl) ?_
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨?_,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm, CalleeSavedPreserved]⟩
  rw [← ss320_bytes_eq_pl s.sp r1 r2 hr1]
  simp_all only [sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TopPlacedBudgetAux
