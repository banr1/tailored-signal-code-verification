/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudgetAux
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived2
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.headerReceived` Arm (Part 2: `+1896..+3068` & Full Arm, Block `427`)

Threads `RustCliAllocBudget` through `Ct1Sampled` state assembly (`+1896 -> +3068`) and
composes the complete `.headerReceived` arm (`+1312 -> +3068`) in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsLogFilterAddr lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (SpqrSendJoinStatePlaced spqrCoinsAfterPlaced spqrCoinsAtPlaced spqrMlkemEncaps1Sym)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Chunk EncoderState EpochSecret MlKem PolyEncoder hkdfExtractBytes
   hkdfToVecUnchecked mlkemEncaps1Spec sckaKeyInfoPrefix spqrAuthApi spqrHkdfWith spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled HeaderReceived)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded)
open CryptoVerification.RustHeap (vecU8Buf)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost authenticatorAt)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (chunkAt polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.EncodeBytes (encodeBytesResult)
open CryptoVerification.SpqrV1.States.Leaves (Relocatable)
open CryptoVerification.SpqrV1.Top.Send
  (authHeapBufs authInlineWordsAt authInlineWordsAt_entails_memRegion
   chunkAt_5632_4192_1360_eq chunkAt_extract_words chunkedCt1SampledTail920At
   chunkedStatesAt_headerReceived_expose chunkedStatesTail920At
   epochBeBytes epochBeBytes_length fold_arm_headerReceived_950 fold_authenticatorAt_of_inline
   fold_chunkedCt1SampledAt_4704 fold_headerReceived_step5_regions memRegion_1408_16_eq_words2
   memRegion_38_eq_chunk_slot memRegion_4064_16_eq_words2 memRegion_4192_merge_400
   memRegion_448_expose_chunk_slot memRegion_4592_48_eq_words6 memRegion_4704_928_split
   memRegion_5152_80_eq_words10 memRegion_5666_1438_split memRegion_5672_32_eq_words4
   polyEncoderTagVal send_ct1_chunk_ok_elim spqrSendCalleeStack
   spqrSendKeySlotAt spqrSendPayloadSlotAt vecU8Rest)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FitsStep FitsTrace FitsTraceOf
   RustCliAllocBudget SeqEnv VmPreserved coarseCostModel fitsEvents_append
   fitsEvents_of_prefix_fitsTrace rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX EncodeBytesPlacedOkX PolyNextChunkPlacedOkX
   spqrLogLevelZeroPlacedAt spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
  (AuthUpdatePlacedOkX HeaderReceived1Env HeaderReceived1aEnv HeaderReceived1bEnv
   HkdfToVecPlacedOkX headerReceived1Env_nonempty headerReceived1aEvents headerReceived1bEnv_nonempty
   spqrRustAllocZeroedSym step_headerReceived_1312_to_1504_sepWP_placed
   step_headerReceived_1504_to_1680_sepWP_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudgetAux
  (HeaderReceived2aEnv HeaderReceived2aPreEnv PolyNextChunkEncEnv call_dealloc_lscro
   call_memcpy_relocate_lscro fitsEnv_seqEnv_of_nonempty headerReceived2aEnv_nonempty
   headerReceived2aPreEnv_nonempty headerReceived2aPreEvents sepWP_lscro_with_vm
   step_headerReceived_1680_to_1896_placed step_headerReceived_1680_to_1896_sepWP_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (finish_sepWP_lscro_plain of_sepWP_lscro_plain spqrSend_dealloc_ok_placed
   spqrSend_session_memcpy_region_ok_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudgetAux
  (HeaderReceived2aEnv PolyNextChunkEncEnv
   step_headerReceived_1680_to_1896_sepWP_placed step_headerReceived_1680_to_1896_placed)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  ] do
    Lean.Attribute.erase nm `arm64_norm

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_setMem_local (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg128_local (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg64_local (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg32_local (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
private theorem mem_writeReg64_setPC (s : State) (r : Reg) (v pc : BitVec 64) :
    ((s.writeReg64 r v).setPC pc).mem = s.mem := by
  cases s; cases r <;> rfl

omit [LibsignalPlacement] in
private theorem vmPreserved_chain_writeReg64_setPC {s₀ s₁ s₂ : State} {r : Reg} {v pc : BitVec 64}
    (h1 : VmPreserved s₀ s₁) (h2 : VmPreserved ((s₁.writeReg64 r v).setPC pc) s₂) :
    VmPreserved s₀ s₂ :=
  h1.trans ((by simp only [wp_norm, arm64_norm] : VmPreserved s₁ ((s₁.writeReg64 r v).setPC pc)).trans h2)

local syntax "by_vm_lscro " term:max ppSpace term:max ppSpace "(" tacticSeq ")" : tactic
local elab_rules : tactic
  | `(tactic| by_vm_lscro $mid:term $hcrl:term ($tac:tacticSeq)) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      refine sepWP_lscro_with_vm (mid := $mid)
        (by first | exact $hcrl | (rw [mem_writeReg64_setPC]; exact $hcrl)) ?_))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let initLCtx ← Lean.getLCtx
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      let mut revData : Array (Lean.MVarId × Nat × Lean.Expr) := #[]
      for r in rem do
        let rLCtx ← r.withContext Lean.getLCtx
        let mut newFVars : Array Lean.FVarId := #[]
        for ldecl in rLCtx do
          if !ldecl.isImplementationDetail && !initLCtx.contains ldecl.fvarId then
            newFVars := newFVars.push ldecl.fvarId
        let (reverted, rRev) ← r.revert newFVars true
        let revTy ← rRev.getType
        revData := revData.push (rRev, reverted.size, revTy)
      let rec instWithDummies :
          List (Lean.MVarId × Nat × Lean.Expr) → Array Lean.Expr →
            Lean.MetaM (Lean.Expr × Array Lean.Expr)
        | [], dummies => do
          let savedMCtx ← Lean.getMCtx
          let prf ← try
            for j in [:revData.size] do
              revData[j]!.1.assign dummies[j]!
            Lean.instantiateMVars g1
          finally
            Lean.setMCtx savedMCtx
          return (prf, dummies)
        | (_, _, revTy) :: rest, dummies =>
          Lean.Meta.withLocalDeclD (`_vm_cont) revTy fun fv =>
            instWithDummies rest (dummies.push fv)
      let (prf1, dummies) ← instWithDummies revData.toList #[]
      let nArgs := e1.getAppNumArgs
      let hk := (e1.getArg! 2).consumeMData
      let e2Fn := e2.getAppFn
      let e2Args := e2.getAppArgs
      let prf2 := prf1.replace fun sub =>
        match dummies.findIdx? (fun d => d == sub) with
        | some j => some (Lean.mkMVar revData[j]!.1)
        | none =>
          if sub.isAppOfArity ``Arm64.Program.withSvc e2Args.size then
            some sub
          else if sub.isAppOfArity ``Arm64.Program.rebase nArgs &&
              (sub.getArg! 2).consumeMData.eqv hk then
            some (Lean.mkAppN e2Fn (e2Args.set! 0 sub))
          else
            none
      g.assign prf2
      let mut newRem : List Lean.MVarId := []
      for (rRev, nRev, _) in revData do
        let (_, rIntro) ← rRev.introNP nRev
        newRem := newRem ++ [rIntro]
      Lean.Elab.Tactic.setGoals (newRem ++ savedGoals.tail!)

/-! ## 1. Exact Allocator Event Sequences & Full-Arm Envelope (`+1896 -> +3068` & `+1312 -> +3068`) -/

/-- Exact allocator event sequence of `.headerReceived` Sub-step 4 (`+1896 -> +3068`):
    `__rust_dealloc(960, 1)` on the temporary `ct1_tmp_ptr` buffer. -/
def headerReceived2bEvents : List AllocEvent :=
  rustDeallocEvents 960 1

/-- Exact allocator event envelope of `.headerReceived` Sub-step 4 (`+1896 -> +3068`). -/
def HeaderReceived2bEnv (evs : List AllocEvent) : Prop :=
  evs = headerReceived2bEvents

theorem headerReceived2bEnv_nonempty : ∃ evs, HeaderReceived2bEnv evs :=
  ⟨headerReceived2bEvents, rfl⟩

@[simp]
theorem fitsEnv_headerReceived2b_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st HeaderReceived2bEnv ↔ FitsEvents M lim st headerReceived2bEvents :=
  FitsEnv.eq_iff

/-- Exact allocator event envelope of `.headerReceived` Sub-step 3 (`+1680 -> +1896`) keyed directly
    by the 960-byte `ct1` ciphertext bytes (`outSt.uc.ct1`). -/
def HeaderReceived2aCt1Env (ct1Bytes : Bytes) (chunk : Chunk) (evs : List AllocEvent) : Prop :=
  match encodeBytesResult ct1Bytes with
  | .ok enc => HeaderReceived2aEnv enc chunk evs
  | .error _ => HeaderReceived2aPreEnv evs

theorem headerReceived2aCt1Env_eq_of_ok {ct1Bytes : Bytes} {enc : PolyEncoder} {chunk : Chunk}
    (henc : encodeBytesResult ct1Bytes = .ok enc) :
    HeaderReceived2aCt1Env ct1Bytes chunk = HeaderReceived2aEnv enc chunk := by
  funext evs
  simp only [HeaderReceived2aCt1Env, henc]

theorem headerReceived2aCt1Env_nonempty (ct1Bytes : Bytes) (chunk : Chunk) :
    ∃ evs, HeaderReceived2aCt1Env ct1Bytes chunk evs := by
  unfold HeaderReceived2aCt1Env
  cases encodeBytesResult ct1Bytes with
  | ok enc => exact headerReceived2aEnv_nonempty enc chunk
  | error _ => exact headerReceived2aPreEnv_nonempty

/-- Combined allocator event envelope of `.headerReceived` Part 2 (`+1680 -> +3068`). -/
def HeaderReceived2Ct1Env (ct1Bytes : Bytes) (chunk : Chunk) : List AllocEvent → Prop :=
  SeqEnv (HeaderReceived2aCt1Env ct1Bytes chunk) HeaderReceived2bEnv

theorem headerReceived2Ct1Env_nonempty (ct1Bytes : Bytes) (chunk : Chunk) :
    ∃ evs, HeaderReceived2Ct1Env ct1Bytes chunk evs := by
  obtain ⟨evs2a, he2a⟩ := headerReceived2aCt1Env_nonempty ct1Bytes chunk
  exact ⟨evs2a ++ headerReceived2bEvents, SeqEnv.append he2a rfl⟩

/-- Complete allocator event envelope of the `.headerReceived` arm (`+1312 -> +3068`). -/
def HeaderReceivedArmEnv (rkLen : Nat) (ct1Bytes : Bytes) (chunk : Chunk) :
    List AllocEvent → Prop :=
  SeqEnv (HeaderReceived1Env rkLen) (HeaderReceived2Ct1Env ct1Bytes chunk)

theorem headerReceivedArmEnv_nonempty (g : AuthenticatorGhost) (rkLen : Nat)
    (ct1Bytes : Bytes) (chunk : Chunk) :
    ∃ evs, HeaderReceivedArmEnv rkLen ct1Bytes chunk evs := by
  obtain ⟨evs1, he1⟩ := headerReceived1Env_nonempty g rkLen
  obtain ⟨evs2, he2⟩ := headerReceived2Ct1Env_nonempty ct1Bytes chunk
  exact ⟨evs1 ++ evs2, SeqEnv.append he1 he2⟩

-- Concrete `coarseCostModel` non-vacuity check for `HeaderReceived2bEnv` after allocating 960 B.
example :
    FitsEnv coarseCostModel
      { staticCount := 32, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
      (coarseCostModel.stepEvents (rustAllocEvents 960 1) coarseCostModel.init)
      HeaderReceived2bEnv := by
  rw [fitsEnv_headerReceived2b_iff]
  have htr : FitsTraceOf coarseCostModel
      { staticCount := 32, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
      (rustAllocEvents 960 1 ++ headerReceived2bEvents) := by
    unfold FitsTraceOf FitsTrace FitsStep; decide
  exact fitsEvents_of_prefix_fitsTrace (List.prefix_append _ _) htr

/-! ## 2. Budget-Threaded Sub-Step 4 (`(blkPl_427).base + 1896#64 -> (blkPl_427).base + 3068#64`) -/

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem polyEncoderTagVal_beq_neg1 (es : EncoderState) :
    (polyEncoderTagVal es == 18446744073709551615#64) = false := by
  cases es <;> rfl

set_option maxHeartbeats 1600000 in
/-- Non-panicking (`SepWP`) budget-threaded sub-step 4 (`+1896 -> +3068`) of `.headerReceived` on
    `spqrSendPlacedProg ext`. -/
theorem step_headerReceived_1896_to_3068_sepWP_placed {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ct1_tmp_ptr ct1_ptr secret_cap secret_ptr : BitVec 64)
    (g' : AuthenticatorGhost) (auth' : Authenticator) (hdr : Bytes)
    (ct1 : List.Vector (BitVec 8) 960) (es : List.Vector (BitVec 8) 2080)
    (st_hr : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (huc : outSt.uc = { epoch := epoch, auth := auth', hdr := hdr, es := es.toList, ct1 := ct1.toList })
    (hrek : outSt.receiving_ek = st_hr.receiving_ek) (hct1_ne : ct1_ptr ≠ 0)
    (st : M.σ) (_hfit : FitsEnv M lim st HeaderReceived2bEnv)
    {tgt : BitVec 64} {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1896#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = sp + 2384#64) (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch) (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = ct1_tmp_ptr) (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = ct1_ptr) (hx28 : s.readReg64 .x28 = sp + 4704#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗
      memRegion (sp + 1424#64) 920 ∗ polyDecoderAt A.repAlloc (sp + 2472#64) st_hr.receiving_ek ∗
      memRegion (sp + 4064#64) 16 ∗ authInlineWordsAt g' (sp + 4080#64) auth' ∗
      authHeapBufs A.repAlloc g' auth' ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 352 ∗ memRegion (sp + 4592#64) 48 ∗
      memRegion (sp + 4704#64) 928 ∗ chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 1438 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A.repAlloc hdr_cap hdr_ptr hdr ∗
      vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      polyEncoderAt A.repAlloc (sp + 7536#64) outSt.sending_ct1 ∗
      spqrLogLevelZeroPlacedAt ∗ A.pool lim st s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 3068#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = polyEncoderTagVal outSt.sending_ct1.s →
      sf.readReg64 .x21 = secret_cap → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x24 = 5#64 → sf.readReg64 .x25 = sp + 1360#64 →
      sf.readReg64 .x26 = sp + 4704#64 → sf.readReg64 .x27 = secret_ptr →
      sf.readReg64 .x28 = sp + 4192#64 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          memRegion (sp + 400#64) 920 ∗ chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ∗
          ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ epoch) ∗
          chunkedCt1SampledTail920At A.repAlloc (sp + 1424#64) outSt ∗
          memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
          memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7536#64) 400 ∗
          spqrLogLevelZeroPlacedAt ∗
          A.pool lim (M.stepEvents headerReceived2bEvents st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hdealloc := spqrSend_dealloc_ok_placed hA
  have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length _
  let st' := M.stepEvents headerReceived2bEvents st
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hmemcpy hdealloc ⊢
  subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28]
    at hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28
  rw [← sepConj_assoc (memRegion (sp + 4192#64) 48) (memRegion (sp + 4240#64) 352),
      memRegion_4192_merge_400 sp, memRegion_4704_928_split sp, memRegion_5666_1438_split sp]
  by_vm_lscro (lsρ "memcpy") hinv (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_m1 hvm_m1 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_m1]
  refine call_memcpy_relocate_lscro A lim hmemcpy (Relocatable.of_polyEncoderAt A.repAlloc outSt.sending_ct1)
    (sp + 4192#64) (sp + 7536#64) st (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      polyDecoderAt A.repAlloc (sp + 2472#64) st_hr.receiving_ek ∗ memRegion (sp + 4064#64) 16 ∗
      authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A.repAlloc g' auth' ∗
      memRegion (sp + 4592#64) 48 ∗
      memRegion (sp + 4704#64) 448 ∗ memRegion (sp + 5152#64) 80 ∗ memRegion (sp + 5232#64) 400 ∗
      chunkAt (sp + 5632#64) chunk ∗
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5672#64) 32 ∗ memRegion (sp + 5704#64) 1400 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A.repAlloc hdr_cap hdr_ptr hdr ∗
      vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      spqrLogLevelZeroPlacedAt ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    hcrl_m1 (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (ret_pc := (blkPl_427).base + 1920#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
    (by sep_ac_rfl) ?_
  intro sf1 hcrl1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 _ hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1
  simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1
  rw [memRegion_4592_48_eq_words6 sp]
  by_vm_lscro (lsρ "memcpy") hcrl1 (
    wp_conv_pre =>
      dsimp only [authInlineWordsAt]
      simp only [BitVec.add_assoc, arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right]
    iterate 6 (apply SepWP.exists_elim; intro _)
    wp_steps
    have hfold_4080_4592 :
        (((sp + 4080#64) ↦₆₄ g'.rootKey.cap) ∗ ((sp + 4088#64) ↦₆₄ g'.rootKey.ptr) ∗
         ((sp + 4096#64) ↦₆₄ BitVec.ofNat 64 auth'.rootKey.length) ∗
         ((sp + 4104#64) ↦₆₄ g'.macKey.cap) ∗ ((sp + 4112#64) ↦₆₄ g'.macKey.ptr) ∗
         ((sp + 4120#64) ↦₆₄ BitVec.ofNat 64 auth'.macKey.length)) ∗
        (((sp + 4592#64) ↦₆₄ g'.rootKey.cap) ∗ ((sp + 4600#64) ↦₆₄ g'.rootKey.ptr) ∗
         ((sp + 4608#64) ↦₆₄ BitVec.ofNat 64 auth'.rootKey.length) ∗
         ((sp + 4616#64) ↦₆₄ g'.macKey.cap) ∗ ((sp + 4624#64) ↦₆₄ g'.macKey.ptr) ∗
         ((sp + 4632#64) ↦₆₄ BitVec.ofNat 64 auth'.macKey.length) ∗
         authHeapBufs A.repAlloc g' auth') ⊢
        memRegion (sp + 4080#64) 48 ∗ authenticatorAt A.repAlloc ((sp + 4192#64) + 400#64) auth' := by
      have h1 := authInlineWordsAt_entails_memRegion g' (sp + 4080#64) auth'
      have h2 := fold_authenticatorAt_of_inline (A := A.repAlloc) g' (sp + 4592#64) auth'
      dsimp only [authInlineWordsAt] at h1 h2; simp only [BitVec.add_assoc, arm64_norm] at h1 h2
      rw [show (sp + 4192#64) + 400#64 = sp + 4592#64 by bv_omega]; exact sepConj_mono h1 h2
    refine SepWP.fold hfold_4080_4592 (by sep_focus) ?_; clear hfold_4080_4592
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_m2 hvm_m2 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_m2]
  refine call_memcpy_relocate_lscro A lim hmemcpy (Relocatable.of_polyDecoderAt A.repAlloc st_hr.receiving_ek)
    (sp + 5232#64) (sp + 2472#64) st (s0 := s0) (sp_call := sp)
    (Frame := memRegion (sp + 4080#64) 48 ∗
      polyEncoderAt A.repAlloc (sp + 4192#64) outSt.sending_ct1 ∗
      authenticatorAt A.repAlloc ((sp + 4192#64) + 400#64) auth' ∗ memRegion (sp + 7536#64) 400 ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4704#64) 448 ∗ memRegion (sp + 5152#64) 80 ∗
      chunkAt (sp + 5632#64) chunk ∗
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5672#64) 32 ∗ memRegion (sp + 5704#64) 1400 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A.repAlloc hdr_cap hdr_ptr hdr ∗
      vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      spqrLogLevelZeroPlacedAt ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    hcrl_m2 (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (ret_pc := (blkPl_427).base + 1960#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
    (by sep_ac_rfl) ?_
  intro sf2 hcrl2 hpc2 hrun2 hsp2 htr2 hx19_2 _ hx21_2 hx22_2 _ hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
  simp only [wp_norm, arm64_norm, *] at hx19_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
  by_vm_lscro (lsρ "memcpy") hcrl2 (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_m3 hvm_m3 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_m3]
  refine call_memcpy_relocate_lscro A lim hmemcpy
    (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_polyEncoder_and_auth A.repAlloc outSt.sending_ct1 auth')
    (sp + 4704#64) (sp + 4192#64) st (s0 := s0) (sp_call := sp)
    (Frame := polyDecoderAt A.repAlloc (sp + 5232#64) st_hr.receiving_ek ∗
      memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 7536#64) 400 ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 5152#64) 80 ∗ chunkAt (sp + 5632#64) chunk ∗
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5672#64) 32 ∗ memRegion (sp + 5704#64) 1400 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A.repAlloc hdr_cap hdr_ptr hdr ∗
      vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      spqrLogLevelZeroPlacedAt ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    hcrl_m3 (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (ret_pc := (blkPl_427).base + 1984#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
    (by sep_ac_rfl) ?_
  intro sf3 hcrl3 hpc3 hrun3 hsp3 htr3 hx19_3 _ hx21_3 hx22_3 _ hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hvregs_3
  simp only [wp_norm, arm64_norm, *] at hx19_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hvregs_3
  rw [memRegion_5152_80_eq_words10 sp, memRegion_5672_32_eq_words4 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWP.exists_elim; intro _)
  have hct1_tmp_mem := pointsToBytes_entails_memRegion ct1_tmp_ptr ct1.toList
  rw [hct1_len] at hct1_tmp_mem
  refine SepWP.fold hct1_tmp_mem (by sep_focus) ?_
  by_vm_lscro (lsρ spqrRustDeallocSym) hcrl3 (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_d0 hvm_d0 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_d0]
  refine call_dealloc_lscro hdealloc ct1_tmp_ptr 960 1 st
    (s0 := s0) (sp_call := sp) hcrl_d0
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_ac_rfl)
    fun sf_d hcrl_d hpc_d hrun_d hsp_d hcs_d htr_d => ?_
  rcases hcs_d with
    ⟨hx19_d, hx20_d, hx21_d, hx22_d, hx23_d, hx24_d, hx25_d, hx26_d, hx27_d, hx28_d, _, hvregs_d⟩
  simp only [Reg.lr, wp_norm, arm64_norm, *]
    at hpc_d hx19_d hx20_d hx21_d hx22_d hx23_d hx24_d hx25_d hx26_d hx27_d hx28_d hvregs_d
  rw [show (sp + 4704#64 : BitVec 64) + 400#64 = sp + 5104#64 by rw [BitVec.add_assoc]; rfl,
      show A.live ct1_ptr 960 1 = A.repAlloc.live ct1_ptr 960 1 from rfl]
  refine SepWP.fold
    (fold_chunkedCt1SampledAt_4704 sp epoch hdr_cap hdr_ptr es_ptr ct1_ptr
      auth' hdr es ct1 st_hr outSt huc hrek hct1_ne)
    (by sep_focus) ?_
  by_vm_lscro (lsρ "memcpy") hcrl_d (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_m4 hvm_m4 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_m4]
  refine call_memcpy_relocate_lscro A lim hmemcpy (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedCt1SampledTail920At A.repAlloc outSt)
    (sp + 400#64) (sp + 4712#64) st' (s0 := s0) (sp_call := sp)
    (Frame := stackAt sp spqrSendCalleeStack ∗
      ((sp + 4704#64) ↦₆₄ polyEncoderTagVal outSt.sending_ct1.s) ∗
      ((sp + 5672#64) ↦₆₄ secret_cap) ∗ ((sp + 5680#64) ↦₆₄ secret_ptr) ∗
      ((sp + 5688#64) ↦₆₄ 32#64) ∗ ((sp + 5696#64) ↦₆₄ epoch) ∗ memRegion (sp + 4192#64) 448 ∗
      memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 7536#64) 400 ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      memRegion (sp + 4064#64) 16 ∗ chunkAt (sp + 5632#64) chunk ∗
      memRegion (sp + 5666#64) 6 ∗ memRegion (sp + 5704#64) 1400 ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      spqrLogLevelZeroPlacedAt ∗ Frame)
    hcrl_m4 (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (ret_pc := (blkPl_427).base + 2096#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
    (by sep_ac_rfl) ?_
  intro sf4 hcrl4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 _ hx22_4 _ _ _ hx26_4 _ hx28_4 hvregs_4
  simp only [wp_norm, arm64_norm, *] at hx19_4 hx20_4 hx22_4 hx26_4 hx28_4 hvregs_4
  obtain ⟨cw0, cw1, cw2, cw3, hchunk⟩ := chunkAt_extract_words chunk
  obtain ⟨hchunk_5632, hchunk_4192, hchunk_1360⟩ := chunkAt_5632_4192_1360_eq sp chunk cw0 cw1 cw2 cw3 hchunk
  rw [hchunk_5632, memRegion_448_expose_chunk_slot sp, memRegion_38_eq_chunk_slot sp,
      memRegion_4064_16_eq_words2 sp, memRegion_1408_16_eq_words2 sp]
  wp_conv_pre =>
    dsimp only [spqrLogLevelZeroPlacedAt, lsLogFilterAddr]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWP.exists_elim; intro _)
  by_vm_lscro ((blkPl_427).base + 2136#64) hcrl4 (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_2136 hvm_2136 => ?_⟩)
  wp_step
  by_vm_lscro (lsρ "memcpy") hcrl_2136 (
    wp_steps
    have hfold_step5 :
        (((sp + 1360#64) ↦₆₄ cw0) ∗ ((sp + 1368#64) ↦₆₄ cw1) ∗ ((sp + 1376#64) ↦₆₄ cw2) ∗
         ((sp + 1384#64) ↦₆₄ cw3) ∗ ((sp + 1392#64) ↦₁₆ chunk.index)) ∗
        (((sp + 4064#64) ↦₆₄ 32#64) ∗ ((sp + 4072#64) ↦₆₄ epoch)) ∗
        ((((sp + 4192#64) ↦₆₄ cw0) ∗ ((sp + 4200#64) ↦₆₄ cw1) ∗ ((sp + 4208#64) ↦₆₄ cw2) ∗
          ((sp + 4216#64) ↦₆₄ cw3) ∗ ((sp + 4224#64) ↦₁₆ chunk.index)) ∗ memRegion (sp + 4226#64) 414) ∗
        (((sp + 4704#64) ↦₆₄ polyEncoderTagVal outSt.sending_ct1.s) ∗ memRegion (sp + 4712#64) 920 ∗
         (((sp + 5632#64) ↦₆₄ cw0) ∗ ((sp + 5640#64) ↦₆₄ cw1) ∗ ((sp + 5648#64) ↦₆₄ cw2) ∗
          ((sp + 5656#64) ↦₆₄ cw3) ∗ ((sp + 5664#64) ↦₁₆ chunk.index)) ∗ memRegion (sp + 5666#64) 6 ∗
         (((sp + 5672#64) ↦₆₄ secret_cap) ∗ ((sp + 5680#64) ↦₆₄ secret_ptr) ∗
          ((sp + 5688#64) ↦₆₄ 32#64) ∗ ((sp + 5696#64) ↦₆₄ epoch)) ∗ memRegion (sp + 5704#64) 1400) ∗
        (((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64)) ⊢
        chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 4064#64) 16 ∗
        memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 := by
      rw [← hchunk_1360, ← hchunk_4192, ← hchunk_5632]
      exact sepConj_mono_right (fold_headerReceived_step5_regions sp chunk
        (polyEncoderTagVal outSt.sending_ct1.s) 32#64 epoch secret_cap secret_ptr 32#64 epoch
        secret_cap secret_ptr 32#64)
    refine SepWP.fold hfold_step5 (by sep_focus) ?_; clear hfold_step5
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_m5 hvm_m5 => ?_⟩)
  rw [← A.pool_of_vmPreserved (vmPreserved_chain_writeReg64_setPC hvm_2136 hvm_m5)]
  refine call_memcpy_relocate_lscro A lim hmemcpy (CryptoVerification.SpqrV1.Top.Send.Relocatable.of_chunkedCt1SampledTail920At A.repAlloc outSt)
    (sp + 1424#64) (sp + 400#64) st' (s0 := s0) (sp_call := sp)
    (Frame := chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4192#64) 448 ∗
      memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 ∗
      ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ epoch) ∗ memRegion (sp + 1394#64) 4 ∗
      stackAt sp spqrSendCalleeStack ∗
      memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 7536#64) 400 ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      spqrLogLevelZeroPlacedAt ∗ Frame)
    hcrl_m5 (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (ret_pc := (blkPl_427).base + 2344#64) (by simp only [Reg.lr, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
    (by dsimp only [spqrLogLevelZeroPlacedAt, lsLogFilterAddr]; sep_ac_rfl) ?_
  intro sf5 hcrl5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hx22_5 _ _ hx25_5 hx26_5 hx27_5 _ hvregs_5
  simp only [wp_norm, arm64_norm, *] at hx19_5 hx20_5 hx21_5 hx22_5 hx25_5 hx26_5 hx27_5 hvregs_5
  by_vm_lscro ((blkPl_427).base + 3068#64) hcrl5 (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_f hvm_f => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_f]
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 3068#64) hcrl_f
  exact finish_sepWP_lscro_plain (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (fun hinv_f => hnext _ hinv_f
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) (by simp only [Reg.x19, arm64_norm, *])
      (by simp only [Reg.x20, arm64_norm, *]) (by simp only [Reg.x21, arm64_norm, *])
      (by simp only [Reg.x22, arm64_norm, *]) (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x25, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x27, arm64_norm, *]) (by simp only [Reg.x28, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]))
    (Entails.of_eq (by sep_ac_rfl))

/-- Panic-aware (`SepWPp`) wrapper for `step_headerReceived_1896_to_3068_sepWP_placed`,
    generalized over arbitrary `post` and `Qp`. -/
theorem step_headerReceived_1896_to_3068_placed {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ct1_tmp_ptr ct1_ptr secret_cap secret_ptr : BitVec 64)
    (g' : AuthenticatorGhost) (auth' : Authenticator) (hdr : Bytes)
    (ct1 : List.Vector (BitVec 8) 960) (es : List.Vector (BitVec 8) 2080)
    (st_hr : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (huc : outSt.uc = { epoch := epoch, auth := auth', hdr := hdr, es := es.toList, ct1 := ct1.toList })
    (hrek : outSt.receiving_ek = st_hr.receiving_ek) (hct1_ne : ct1_ptr ≠ 0)
    (st : M.σ) (hfit : FitsEnv M lim st HeaderReceived2bEnv)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1896#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = sp + 2384#64) (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch) (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = ct1_tmp_ptr) (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = ct1_ptr) (hx28 : s.readReg64 .x28 = sp + 4704#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗
      memRegion (sp + 1424#64) 920 ∗ polyDecoderAt A.repAlloc (sp + 2472#64) st_hr.receiving_ek ∗
      memRegion (sp + 4064#64) 16 ∗ authInlineWordsAt g' (sp + 4080#64) auth' ∗
      authHeapBufs A.repAlloc g' auth' ∗
      memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4240#64) 352 ∗ memRegion (sp + 4592#64) 48 ∗
      memRegion (sp + 4704#64) 928 ∗ chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 1438 ∗
      (hdr_ptr ↦ₛ hdr) ∗ vecU8Rest A.repAlloc hdr_cap hdr_ptr hdr ∗
      vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      polyEncoderAt A.repAlloc (sp + 7536#64) outSt.sending_ct1 ∗
      spqrLogLevelZeroPlacedAt ∗ A.pool lim st s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 3068#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = polyEncoderTagVal outSt.sending_ct1.s →
      sf.readReg64 .x21 = secret_cap → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x24 = 5#64 → sf.readReg64 .x25 = sp + 1360#64 →
      sf.readReg64 .x26 = sp + 4704#64 → sf.readReg64 .x27 = secret_ptr →
      sf.readReg64 .x28 = sp + 4192#64 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          memRegion (sp + 400#64) 920 ∗ chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ∗
          ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ epoch) ∗
          chunkedCt1SampledTail920At A.repAlloc (sp + 1424#64) outSt ∗
          memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
          memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7536#64) 400 ∗
          spqrLogLevelZeroPlacedAt ∗
          A.pool lim (M.stepEvents headerReceived2bEvents st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 3068#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_headerReceived_1896_to_3068_sepWP_placed hA
    sp epoch hdr_cap hdr_ptr es_ptr ct1_tmp_ptr ct1_ptr secret_cap secret_ptr
    g' auth' hdr ct1 es st_hr outSt chunk huc hrek hct1_ne st hfit
    hinv hsp_align hpc hrun hsp hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 htrace hP
    fun sf hcrl_sf hpc_sf hrun_sf hsp_sf hx19 hx20' hx21' hx22' hx24' hx25' hx26' hx27' hx28' htr hvregs =>
      SepWP.done hpc_sf hrun_sf fun _ =>
        hnext sf hcrl_sf hpc_sf hrun_sf hsp_sf
          hx19 hx20' hx21' hx22' hx24' hx25' hx26' hx27' hx28' htr hvregs

/-! ## 3. Budget-Threaded Top-Level `.headerReceived` Arm (`(blkPl_427).base + 1312#64 -> +3068#64`) -/

set_option maxHeartbeats 1600000 in
/-- Non-panicking (`SepWP`) budget-threaded top-level arm theorem for `.headerReceived st`
    (`(blkPl_427).base + 1312#64 -> (blkPl_427).base + 3068#64`). -/
theorem step_send_arm_headerReceived_sepWP_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (hhkdf : HkdfToVecPlacedOkX M A lim (spqrHkdfWith F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (henc : EncodeBytesPlacedOkX A lim ext)
    (hnextChunk : PolyNextChunkPlacedOkX M A lim ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk) (ek : EpochSecret)
    (hroot_len : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st.send_ct1_chunk K tape = .ok (outSt, chunk, ek, tape'))
    (st_b : M.σ) (hfit : FitsEnv M lim st_b (HeaderReceivedArmEnv st.uc.auth.rootKey.length outSt.uc.ct1 chunk))
    {tgt : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st_b s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl cur tape ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
      memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 0x1260#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      HeaderReceivedArmEnv st.uc.auth.rootKey.length outSt.uc.ct1 chunk evs →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
          memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
          memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 0x1260#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) (some ek) ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have hhkdf' : HkdfToVecPlacedOkX M A lim (hkdfToVecUnchecked F) ext := hhkdf
  obtain ⟨h32, ct1, es, ss, sending_ct1, hencaps, henc_res, hnext_chunk, huc, hrek, hek, htape'⟩ :=
    send_ct1_chunk_ok_elim K st hsend
  have hct1_uc : outSt.uc.ct1 = ct1.toList := by rw [huc]
  let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
  subst hP
  apply of_sepWP_lscro_plain (mid := spqrSendPlacedEntry + 1312#64) hinv
  refine SepWP.fold (chunkedStatesAt_headerReceived_expose sp st) (by sep_focus) ?_
  rw [ProofLib.memRegion_eight (sp + 4056#64),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 48) (k := 400) (b' := sp + 4240#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 4240#64) (n := 352) (k := 48) (b' := sp + 4592#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 961) (k := 1439) (b' := sp + 5665#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7136#64) (n := 32) (k := 368) (b' := sp + 7168#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 32) (k := 368) (b' := sp + 7568#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide),
      show (sp + 0x550#64 : BitVec 64) = sp + 1360#64 from rfl,
      show (sp + 0x580#64 : BitVec 64) = sp + 1408#64 from rfl,
      show (sp + 0x590#64 : BitVec 64) = sp + 1424#64 from rfl,
      show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro d4056; apply SepWP.exists_elim; intro g
  apply SepWP.exists_elim; intro hdr_cap; apply SepWP.exists_elim; intro hdr_ptr
  refine SepWP.fold (Entails.refl ⌜st.uc.hdr.length < 2 ^ 63⌝) (by sep_focus) ?_
  refine SepWP.pure_elim fun hhdr_lt => ?_
  apply SepWP.done hpc hrun; intro hinv0
  rcases fitsEnv_seqEnv_of_nonempty (headerReceived2Ct1Env_nonempty outSt.uc.ct1 chunk) hfit with
    ⟨hfit_1, hfit_2_all⟩
  rcases fitsEnv_seqEnv_of_nonempty (headerReceived1bEnv_nonempty g st.uc.auth.rootKey.length) hfit_1 with
    ⟨hfit_1a, hfit_1b_all⟩
  have hfit_1b : FitsEnv M lim (M.stepEvents headerReceived1aEvents st_b)
      (HeaderReceived1bEnv st.uc.auth.rootKey.length) :=
    hfit_1b_all headerReceived1aEvents rfl
  refine step_headerReceived_1312_to_1504_sepWP_placed hA hZero hcoinsFill henc1 g st.uc.auth st.uc.epoch
    hdr_cap hdr_ptr st.uc.hdr hhdr_lt sp cur tape h32 rand rfl hencaps d4056 st_b hfit_1a
    (Frame := tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗ memRegion (sp + 1424#64) 920 ∗
      memRegion (sp + 2872#64) 440 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4240#64) 352 ∗ memRegion (sp + 4592#64) 48 ∗ memRegion (sp + 5665#64) 1439 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7168#64) 368 ∗ memRegion (sp + 7568#64) 368 ∗
      ((sp + 0x950#64) ↦₆₄ 8#64) ∗ polyDecoderAt A.repAlloc (sp + 2472#64) st.receiving_ek ∗
      vecU8Rest A.repAlloc hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hinv0 hsp_align hpc hrun hsp hx24 hx26 hx28 htr (by sep_ac_rfl) ?_
  intro s1 es_ptr ss_ptr hinv1 hes_ne hes_b hss_ne hss_b hpc1 hrun1 hsp1
    hx19_1 hx20_1 hx21_1 hx22_1 _ hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 htr1 hvregs1
  refine step_headerReceived_1504_to_1680_sepWP_placed hA hhkdf' hupd
    sp st.uc.epoch hdr_cap hdr_ptr es_ptr ss_ptr g st.uc.auth st.uc.hdr ct1 ss hroot_len
    (M.stepEvents headerReceived1aEvents st_b) hfit_1b
    (Frame := authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ (hdr_ptr ↦ₛ st.uc.hdr) ∗
      ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗ memRegion (sp + 7136#64) 32 ∗
      spqrCoinsAfterPlaced ctl cur tape 32 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 1408#64) 16 ∗
      memRegion (sp + 1424#64) 920 ∗ memRegion (sp + 2872#64) 440 ∗
      memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4240#64) 352 ∗ memRegion (sp + 4592#64) 48 ∗ memRegion (sp + 5665#64) 1439 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7168#64) 368 ∗ memRegion (sp + 7568#64) 368 ∗
      ((sp + 0x950#64) ↦₆₄ 8#64) ∗ polyDecoderAt A.repAlloc (sp + 2472#64) st.receiving_ek ∗
      vecU8Rest A.repAlloc hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hinv1 hsp_align hpc1 hrun1 hsp1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 htr1
    (by sep_ac_rfl) ?_
  intro s2 ct1_ptr info_ptr secret_cap secret_ptr evs1b info secret auth' hinv2 hevs1b
    hct1_ne hct1_b hinfo_ne hinfo_b hsec_ne hsec_b hsec_ge hsec_lt
    hpc2 hrun2 hsp2 hx19_2 hx20_2 hx21_2 hx22_2 _ hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2 hvregs2
  let evs1 := headerReceived1aEvents ++ evs1b
  have hevs1 : HeaderReceived1Env st.uc.auth.rootKey.length evs1 := SeqEnv.append rfl hevs1b
  have hstep1_eq :
      M.stepEvents evs1b (M.stepEvents headerReceived1aEvents st_b) = M.stepEvents evs1 st_b :=
    (M.stepEvents_append headerReceived1aEvents evs1b st_b).symm
  rw [hstep1_eq]
  have hfit_2 : FitsEnv M lim (M.stepEvents evs1 st_b) (HeaderReceived2Ct1Env outSt.uc.ct1 chunk) :=
    hfit_2_all evs1 hevs1
  rcases fitsEnv_seqEnv_of_nonempty headerReceived2bEnv_nonempty hfit_2 with ⟨hfit_2a_ct1, hfit_2b_all⟩
  have hfit_2a : FitsEnv M lim (M.stepEvents evs1 st_b) (HeaderReceived2aEnv sending_ct1 chunk) := by
    rwa [hct1_uc, headerReceived2aCt1Env_eq_of_ok henc_res] at hfit_2a_ct1
  have hinfo_len : info.length = 41 := by
    dsimp only [info]; rw [List.length_append, epochBeBytes_length]; rfl
  have hsec_len : secret.length = 32 := by
    change (List.take 32 (CryptoGames.HKDF.hkdfBlocks F (hkdfExtractBytes F (List.replicate 32 0#8) ss.toList) info 1).flatten).length = 32
    dsimp only [CryptoGames.HKDF.hkdfBlocks, List.nil_append, List.flatten_cons, List.flatten_nil]
    rw [List.length_take, List.append_nil, CryptoVerification.LibsignalSpqrV1.length_hmacWith]; rfl
  have hmerge_7136 : memRegion (sp + 7136#64) 32 ∗ memRegion (sp + 7168#64) 368 = memRegion (sp + 7136#64) 400 :=
    (ProofLib.memRegion_split' (b := sp + 7136#64) (n := 32) (k := 368) (b' := sp + 7168#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)).symm
  refine step_headerReceived_1680_to_1896_sepWP_placed hA henc hnextChunk
    sp st.uc.epoch hdr_cap hdr_ptr es_ptr ct1_ptr info_ptr ss_ptr secret_cap secret_ptr
    auth' st.uc.hdr info secret ct1 ss sending_ct1 outSt chunk hinfo_len henc_res hnext_chunk
    (M.stepEvents evs1 st_b) hfit_2a
    (Frame := spqrLogLevelZeroPlacedAt ∗ memRegion (sp + 1360#64) 38 ∗ memRegion (sp + 4064#64) 16 ∗
      memRegion (sp + 4240#64) 352 ∗ memRegion (sp + 4592#64) 48 ∗
      authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ (hdr_ptr ↦ₛ st.uc.hdr) ∗
      ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗ spqrCoinsAfterPlaced ctl cur tape 32 ∗
      memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1408#64) 16 ∗
      memRegion (sp + 1424#64) 920 ∗ memRegion (sp + 2872#64) 440 ∗
      ((sp + 0x950#64) ↦₆₄ 8#64) ∗ polyDecoderAt A.repAlloc (sp + 2472#64) st.receiving_ek ∗
      vecU8Rest A.repAlloc hdr_cap hdr_ptr st.uc.hdr ∗ Frame)
    hinv2 hsp_align hpc2 hrun2 hsp2 hx20_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 htr2
    (by rw [← hmerge_7136]; sep_ac_rfl) ?_
  intro s3 g' ct1_ptr' evs2a hinv3 hevs2a hct1'_ne hct1'_b
    hpc3 hrun3 hsp3 hx19_3 hx20_3 hx21_3 hx22_3 _ hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3 hvregs3
  have hevs2a_ct1 : HeaderReceived2aCt1Env outSt.uc.ct1 chunk evs2a := by
    rwa [hct1_uc, headerReceived2aCt1Env_eq_of_ok henc_res]
  have hfit_2b : FitsEnv M lim (M.stepEvents evs2a (M.stepEvents evs1 st_b)) HeaderReceived2bEnv :=
    hfit_2b_all evs2a hevs2a_ct1
  refine step_headerReceived_1896_to_3068_sepWP_placed hA
    sp st.uc.epoch hdr_cap hdr_ptr es_ptr ct1_ptr ct1_ptr' secret_cap secret_ptr
    g' auth' st.uc.hdr ct1 es st outSt chunk huc hrek hct1'_ne
    (M.stepEvents evs2a (M.stepEvents evs1 st_b)) hfit_2b
    (Frame := A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
      memRegion (sp + 7136#64) 400 ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      spqrCoinsAfterPlaced ctl cur tape 32 ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗
      authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗
      memRegion (sp + 2872#64) 440 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)
    hinv3 hsp_align hpc3 hrun3 hsp3 hx20_3 hx21_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3
    (by sep_ac_rfl) ?_
  intro sf hinv_f hpc_f hrun_f hsp_f hx19_f hx20_f hx21_f hx22_f hx24_f hx25_f hx26_f hx27_f hx28_f htr_f hvregs_f
  have htape_sub : tape.length - tape'.length = 32 := by rw [htape', List.length_drop]; omega
  let evs_arm := evs1 ++ (evs2a ++ headerReceived2bEvents)
  have hevs_arm : HeaderReceivedArmEnv st.uc.auth.rootKey.length outSt.uc.ct1 chunk evs_arm :=
    SeqEnv.append hevs1 (SeqEnv.append hevs2a_ct1 rfl)
  have hstep_arm :
      M.stepEvents headerReceived2bEvents (M.stepEvents evs2a (M.stepEvents evs1 st_b)) =
        M.stepEvents evs_arm st_b :=
    (M.stepEvents_append evs2a headerReceived2bEvents (M.stepEvents evs1 st_b)).symm.trans
      (M.stepEvents_append evs1 (evs2a ++ headerReceived2bEvents) st_b).symm
  rw [hstep_arm]
  refine SepWP.weaken_pre ?_
    (hnext sf evs_arm hinv_f hevs_arm ⟨hpc_f, hrun_f, hsp_f, htr_f,
      by rw [hx19_f, hx19_3, hx19_2, hx19_1, hx19], hx20_f, hx22_f, hx25_f, hx26_f,
      by rw [hx28_f, ← show sp + 0x1060#64 = sp + 4192#64 from rfl, ← hx28, hx28_0],
      by rw [hvregs_f, hvregs3, hvregs2, hvregs1, hvregs]⟩)
  rw [htape_sub, hx24_f, hx21_f, hx27_f]
  have h32_16 : ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ⊢
      memRegion (sp + 32#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp + 32#64) (n := 8) (k := 8) (b' := sp + 40#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _) (ProofLib.pointsTo64_entails_memRegion _ _)
  have h4056 := ProofLib.pointsTo64_entails_memRegion (sp + 4056#64) st.uc.epoch
  have h950 := fold_arm_headerReceived_950 sp hdr_cap hdr_ptr g st
  have hpay : chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ⊢
      spqrSendPayloadSlotAt sp ((5#64 : BitVec 64).setWidth 8) (.ct1 chunk) := by
    dsimp only [spqrSendPayloadSlotAt]
    rw [show (sp + 0x550#64 : BitVec 64) = sp + 1360#64 from rfl,
        show (sp + 0x572#64 : BitVec 64) = sp + 1394#64 from rfl]
    exact Entails.pure_right rfl (Entails.refl _)
  have hkey : A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
      ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ st.uc.epoch) ⊢
      spqrSendKeySlotAt A.repAlloc sp secret_cap secret_ptr (some ek) := by
    have hek_sec : ek.secret = secret := by rw [hek]
    have hek_ep : ek.epoch = st.uc.epoch := by rw [hek]
    have hc : secret_cap ≠ 0 := by intro h0; rw [h0] at hsec_b; contradiction
    dsimp only [spqrSendKeySlotAt, vecU8Buf]
    rw [hek_sec, hek_ep, hsec_len, show (sp + 0x580#64 : BitVec 64) = sp + 1408#64 from rfl,
        show (sp + 0x588#64 : BitVec 64) = sp + 1416#64 from rfl]
    simp only [hc, ↓reduceIte, show BitVec.ofNat 64 32 = 32#64 from rfl]
    refine Entails.pure_right hsec_lt ?_; rw [sepConj_assoc]
    exact Entails.pure_right ⟨hsec_ge, hsec_lt, hsec_ne⟩ (Entails.of_eq (by sep_ac_rfl))
  have hrearr :
      (((sp + 32#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
       memRegion (sp + 400#64) 920 ∗ chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4 ∗
       ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ st.uc.epoch) ∗
       chunkedCt1SampledTail920At A.repAlloc (sp + 1424#64) outSt ∗
       memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
       memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7104#64) 24 ∗
       memRegion (sp + 7536#64) 400 ∗
       spqrLogLevelZeroPlacedAt ∗ A.pool lim (M.stepEvents evs_arm st_b) sf ∗ stackAt sp spqrSendCalleeStack) ∗
      (A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
       memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
       memRegion (sp + 7136#64) 400 ∗ ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗ spqrCoinsAfterPlaced ctl cur tape 32 ∗
       ((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
       ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 2464#64) ↦₆₄ st.uc.epoch) ∗
       authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗ ((sp + 0x950#64) ↦₆₄ 8#64) ∗
       memRegion (sp + 2872#64) 440 ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) =
      (((sp + 32#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap)) ∗
      ((sp + 4056#64) ↦₆₄ st.uc.epoch) ∗
      (((sp + 0x950#64) ↦₆₄ 8#64) ∗ authInlineWordsAt g (sp + 2392#64) st.uc.auth ∗
       (((sp + 2440#64) ↦₆₄ hdr_cap) ∗ ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
        ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 st.uc.hdr.length) ∗ ((sp + 2464#64) ↦₆₄ st.uc.epoch)) ∗
       memRegion (sp + 2472#64) 400 ∗ memRegion (sp + 2872#64) 440) ∗
      (chunkAt (sp + 1360#64) chunk ∗ memRegion (sp + 1394#64) 4) ∗
      (A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
       memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
       ((sp + 1408#64) ↦₆₄ 32#64) ∗ ((sp + 1416#64) ↦₆₄ st.uc.epoch)) ∗
      (stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs_arm st_b) sf ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
       spqrCoinsAfterPlaced ctl cur tape 32 ∗ memRegion (sp + 400#64) 920 ∗
       memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
       memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4704#64) 2400 ∗
       memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
       chunkedCt1SampledTail920At A.repAlloc (sp + 1424#64) outSt ∗ Frame) := by sep_ac_rfl
  rw [hrearr]
  refine Entails.trans (sepConj_mono h32_16 (sepConj_mono h4056 (sepConj_mono h950
    (sepConj_mono hpay (sepConj_mono hkey (Entails.refl _)))))) ?_
  dsimp only [chunkedStatesTail920At]
  rw [show (sp + 0x590#64 : BitVec 64) = sp + 1424#64 from rfl,
      show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Panic-aware (`SepWPp`) top-level arm theorem for `.headerReceived st`
    (`(blkPl_427).base + 1312#64 -> (blkPl_427).base + 3068#64`), generalized over arbitrary
    `post` and `Qp`. -/
theorem step_send_arm_headerReceived_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (hhkdf : HkdfToVecPlacedOkX M A lim (spqrHkdfWith F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (henc : EncodeBytesPlacedOkX A lim ext)
    (hnextChunk : PolyNextChunkPlacedOkX M A lim ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (st : HeaderReceived spqrPolyApi (spqrAuthApi F))
    (outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F)) (chunk : Chunk) (ek : EpochSecret)
    (hroot_len : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st.send_ct1_chunk K tape = .ok (outSt, chunk, ek, tape'))
    (st_b : M.σ) (hfit : FitsEnv M lim st_b (HeaderReceivedArmEnv st.uc.auth.rootKey.length outSt.uc.ct1 chunk))
    {ret : BitVec 64} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool lim st_b s ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl cur tape ∗
      chunkedStatesAt A.repAlloc (sp + 0x950#64) (.headerReceived st) ∗
      memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
      memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 0x1260#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      HeaderReceivedArmEnv st.uc.auth.rootKey.length outSt.uc.ct1 chunk evs →
      SpqrSendJoinStatePlaced sp ext s0 sf { epoch := st.uc.epoch, payload := .ct1 chunk } (.ct1Sampled outSt) →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((stackAt sp spqrSendCalleeStack ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          spqrLogLevelZeroPlacedAt ∗ spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
          memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 32#64) 16 ∗ memRegion (sp + 400#64) 920 ∗
          memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗ memRegion (sp + 4080#64) 48 ∗
          memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 0x1260#64) 2400 ∗
          memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
          spqrSendPayloadSlotAt sp ((sf.readReg64 .x24).setWidth 8) (.ct1 chunk) ∗
          spqrSendKeySlotAt A.repAlloc sp (sf.readReg64 .x21) (sf.readReg64 .x27) (some ek) ∗
          chunkedStatesTail920At A.repAlloc (sp + 0x590#64) (.ct1Sampled outSt)) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 3068#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_send_arm_headerReceived_sepWP_placed A lim ext hA hZero hcoinsFill henc1 hhkdf hupd
    henc hnextChunk sp cur tape tape' st outSt chunk ek hroot_len hsend st_b hfit
    hinv hpc hrun hsp hsp_align htr hx19 hx24 hx26 hx28 hx28_0 hvregs hP
    fun sf evs hcrl_sf hevs hjoin =>
      SepWP.done hjoin.pc hjoin.run fun _ => hnext sf evs hcrl_sf hevs hjoin

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudget
