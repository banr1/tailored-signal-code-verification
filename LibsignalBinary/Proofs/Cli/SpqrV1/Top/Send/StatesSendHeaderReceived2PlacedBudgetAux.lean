/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived2
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.headerReceived` Sub-Step 3 (`+1680..+1896`, Block `427`)

Threads `RustCliAllocBudget` through 960-byte `ct1` allocation, `info` / `ss` deallocation,
`PolyEncoder::encode_bytes`, and `PolyEncoder::next_chunk` (`+1680..+1896`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudgetAux

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Chunk PolyEncoder spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sepWP_seq_lscro sessionMemcpyRegionSpec withLsCodeRoLoaded)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost authenticatorAt)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt chunkSize polyEncoderAt polyEncoderSize resultPolyEncoderAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (EncodeBytesGhost encodeBytesResult encodeBytesStackX)
open CryptoVerification.SpqrV1.Poly.NextChunk (PolyNextChunkGhost polyNextChunkStack)
open CryptoVerification.SpqrV1.States.Leaves (Relocatable polyEncoderAt_split_tag)
open CryptoVerification.SpqrV1.Top.Send
  (authHeapBufs authInlineWordsAt authInlineWordsAt_entails_memRegion
   authenticatorAt_entails_exists_inline_heap fold_4080_and_4704 fold_7536_to_memRegion_400
   memRegion_4080_48_eq_words6 memRegion_7104_24_eq_words3 memRegion_961_split_48_913
   spqrSendCalleeStack stackAt_spqrSendCallee_from_allocHook stackAt_spqrSendCallee_to_allocHook)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FitsStep FitsTrace FitsTraceOf
   RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved coarseCostModel fitsEvents_append
   fitsEvents_of_prefix_fitsTrace rustAllocEvents rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
   rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced EncodeBytesPlacedOkX PolyNextChunkPlacedOkX spqrSendPlacedEntry
   spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled2PlacedBudget
  (polyNextChunkPlaced_onPanic_false_of_ok)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (call_lscro_calleeStack_evs_sepWP call_lscro_calleeStack_sepWP finish_sepWP_lscro_plain
   of_sepWP_lscro_plain spqrSend_allocNoOom_ok_placed spqrSend_dealloc_ok_placed
   spqrSend_session_memcpy_region_ok_placed spqrSend_shim_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1PlacedBudget
  (call_memcpy_relocate_vm)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents encodeBytesSpecX encodeBytesSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
  (PolyNextChunkEnv polyNextChunkEnv_nonempty polyNextChunkPlacedSpec polyNextChunkPlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
  (call_memcpy_bytes_budget call_rustAllocNoOom_budget call_rustDealloc_budget
   call_sessionShim_budget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)

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

/-! ## 1. Exact Allocator Event Sequences & Envelopes (`+1680 -> +1896`) -/

/-- Exact deterministic allocator event prefix of `.headerReceived` Sub-step 3 (`+1680 -> +1872`)
    before `<PolyEncoder as Encoder>::next_chunk`:
    `__rust_alloc(960, 1)` (`ct1_ptr`), `__rust_dealloc(41, 1)` (`info`),
    `__rust_dealloc(32, 1)` (`ss`), and `PolyEncoder::encode_bytes` on 960-byte `ct1`. -/
def headerReceived2aPreEvents : List AllocEvent :=
  rustAllocEvents 960 1 ++
    (rustDeallocEvents 41 1 ++ (rustDeallocEvents 32 1 ++ encodeBytesAllocEvents 960))

/-- Exact deterministic envelope for the pre-`next_chunk` prefix of Sub-step 3 (`+1680 -> +1872`). -/
def HeaderReceived2aPreEnv (evs : List AllocEvent) : Prop :=
  evs = headerReceived2aPreEvents

theorem headerReceived2aPreEnv_nonempty : ∃ evs, HeaderReceived2aPreEnv evs :=
  ⟨headerReceived2aPreEvents, rfl⟩

@[simp]
theorem fitsEnv_headerReceived2aPre_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st HeaderReceived2aPreEnv ↔ FitsEvents M lim st headerReceived2aPreEvents :=
  FitsEnv.eq_iff

/-- Address-independent projection of `PolyNextChunkEnv` depending only on `(enc, chunk)`. -/
def PolyNextChunkEncEnv (enc : PolyEncoder) (chunk : Chunk) (evs : List AllocEvent) : Prop :=
  PolyNextChunkEnv { outA := 0#64, encA := 0#64, enc := enc, enc' := enc, chunk := chunk } evs

theorem polyNextChunkEnv_eq_enc (x : PolyNextChunkGhost) :
    PolyNextChunkEnv x = PolyNextChunkEncEnv x.enc x.chunk :=
  rfl

theorem polyNextChunkEncEnv_nonempty (enc : PolyEncoder) (chunk : Chunk) :
    ∃ evs, PolyNextChunkEncEnv enc chunk evs :=
  polyNextChunkEnv_nonempty { outA := 0#64, encA := 0#64, enc := enc, enc' := enc, chunk := chunk }

/-- Exact allocator event envelope for `.headerReceived` Sub-step 3 (`+1680 -> +1896`). -/
def HeaderReceived2aEnv (sending_ct1 : PolyEncoder) (chunk : Chunk) : List AllocEvent → Prop :=
  SeqEnv HeaderReceived2aPreEnv (PolyNextChunkEncEnv sending_ct1 chunk)

theorem headerReceived2aEnv_nonempty (sending_ct1 : PolyEncoder) (chunk : Chunk) :
    ∃ evs, HeaderReceived2aEnv sending_ct1 chunk evs := by
  obtain ⟨evs2, he2⟩ := polyNextChunkEncEnv_nonempty sending_ct1 chunk
  exact ⟨headerReceived2aPreEvents ++ evs2, SeqEnv.append rfl he2⟩

omit [LibsignalPlacement] in
theorem fitsEnv_seqEnv_of_nonempty {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop} (hne₂ : ∃ evs₂, E₂ evs₂)
    (h : FitsEnv M lim st (SeqEnv E₁ E₂)) :
    FitsEnv M lim st E₁ ∧ ∀ evs₁, E₁ evs₁ → FitsEnv M lim (M.stepEvents evs₁ st) E₂ := by
  refine ⟨fun evs₁ he₁ => ?_, fun evs₁ he₁ evs₂ he₂ => ?_⟩
  · obtain ⟨evs₂, he₂⟩ := hne₂
    exact ((fitsEvents_append M lim evs₁ evs₂ st).mp (h _ (SeqEnv.append he₁ he₂))).1
  · exact ((fitsEvents_append M lim evs₁ evs₂ st).mp (h _ (SeqEnv.append he₁ he₂))).2

theorem fitsEnv_headerReceived2a_split {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {sending_ct1 : PolyEncoder} {chunk : Chunk}
    (h : FitsEnv M lim st (HeaderReceived2aEnv sending_ct1 chunk)) :
    let st1 := M.stepEvents (rustAllocEvents 960 1) st
    let st2 := M.stepEvents (rustDeallocEvents 41 1) st1
    let st3 := M.stepEvents (rustDeallocEvents 32 1) st2
    let st4 := M.stepEvents (encodeBytesAllocEvents 960) st3
    FitsEvents M lim st (rustAllocEvents 960 1) ∧
    FitsEnv M lim st3 (EncodeBytesEnv 960) ∧
    FitsEnv M lim st4 (PolyNextChunkEncEnv sending_ct1 chunk) ∧
    (∀ evs_nc, PolyNextChunkEncEnv sending_ct1 chunk evs_nc →
      HeaderReceived2aEnv sending_ct1 chunk (headerReceived2aPreEvents ++ evs_nc) ∧
      M.stepEvents evs_nc st4 = M.stepEvents (headerReceived2aPreEvents ++ evs_nc) st) := by
  rcases fitsEnv_seqEnv_of_nonempty (polyNextChunkEncEnv_nonempty sending_ct1 chunk) h with
    ⟨hpre_env, hnc_env⟩
  have hpre : FitsEvents M lim st headerReceived2aPreEvents :=
    fitsEnv_headerReceived2aPre_iff.mp hpre_env
  unfold headerReceived2aPreEvents at hpre
  rcases (fitsEvents_append M lim _ _ st).mp hpre with ⟨h960, hrest1⟩
  rcases (fitsEvents_append M lim _ _ _).mp hrest1 with ⟨_, hrest2⟩
  rcases (fitsEvents_append M lim _ _ _).mp hrest2 with ⟨_, henc⟩
  have hstep_pre :
      M.stepEvents headerReceived2aPreEvents st =
        M.stepEvents (encodeBytesAllocEvents 960)
          (M.stepEvents (rustDeallocEvents 32 1)
            (M.stepEvents (rustDeallocEvents 41 1)
              (M.stepEvents (rustAllocEvents 960 1) st))) := by
    unfold headerReceived2aPreEvents
    rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  refine ⟨h960, FitsEnv.eq_iff.mpr henc, ?_, fun evs_nc hnc => ⟨SeqEnv.append rfl hnc, ?_⟩⟩
  · simpa only [hstep_pre] using hnc_env headerReceived2aPreEvents rfl
  · rw [M.stepEvents_append, hstep_pre]

-- Concrete `coarseCostModel` non-vacuity check for `headerReceived2aPreEvents` under an initial
-- live state carrying `info` (41 B) and `ss` (32 B).
example :
    FitsEnv coarseCostModel
      { staticCount := 32, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
      (coarseCostModel.stepEvents (rustAllocEvents 41 1 ++ rustAllocEvents 32 1) coarseCostModel.init)
      HeaderReceived2aPreEnv := by
  rw [fitsEnv_headerReceived2aPre_iff]
  have htr : FitsTraceOf coarseCostModel
      { staticCount := 32, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
      ((rustAllocEvents 41 1 ++ rustAllocEvents 32 1) ++ headerReceived2aPreEvents) := by
    unfold FitsTraceOf FitsTrace FitsStep; decide
  exact fitsEvents_of_prefix_fitsTrace (List.prefix_append _ _) htr

/-! ## 2. Low-RSS VM Stepper & `LibsignalCodeRoLoaded` Budget Call Helpers -/

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem tpidrEl0_setMem_local (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem tpidrEl0_writeVReg128_local (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem tpidrEl0_writeVReg64_local (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem tpidrEl0_writeVReg32_local (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

/-- Step a basic-block segment on `((P.rebase b trapHooks).withSvc noSyscalls)` to `mid`,
    simultaneously propagating `LibsignalCodeRoLoaded lsmpl sm.mem` and `VmPreserved s sm` to the
    real-hook continuation on `P.rebase b Hk` without scanning the full block text. -/
theorem sepWP_lscro_with_vm {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid tgt : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (LibsignalCodeRoLoaded lsmpl sm.mem → VmPreserved s sm → SepWP (P.rebase b Hk) tgt sm Pm post))) :
    SepWP (P.rebase b Hk) tgt s Pre post :=
  sepWP_seq_lscro hcrl
    (SepWP.mono (sepWP_rebase_vmPreserved h) fun _ _ _ _ ⟨hvm, hp⟩ hcrl_m => hp hcrl_m hvm)

local syntax "by_vm_lscro " term:max ppSpace term:max ppSpace "(" tacticSeq ")" : tactic
local elab_rules : tactic
  | `(tactic| by_vm_lscro $mid:term $hcrl:term ($tac:tacticSeq)) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_lscro_with_vm (mid := $mid) $hcrl))
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

theorem call_shim_lscro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry sessionShimBudgetSpec)
    (st : M.σ) {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hsplit : P = A.pool lim st s ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog tgt sf (A.pool lim st sf ∗ Frame) post) :
    SepWP prog tgt s P post := by
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  exact call_sessionShim_budget (A := A) (lim := lim) hcall st hpc hrun hsp hsp_align hlr htrace hsplit
    fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf =>
      SepWP.done hpc_sf hrun_sf fun hcrl1 => hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf htr_sf

theorem call_allocNoOom_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliAllocNoOomSpec M A lim false))
    (size : Nat) (st : M.σ) (hlay : RustLayoutOk size 1)
    (hfit : FitsEvents M lim st (rustAllocEvents size 1))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 .x0).toNat = size) (hx1 : (s.readReg64 .x1).toNat = 1)
    (hsplit : P = (A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 → (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false →
      sf.trace = s0.trace →
      SepWP prog tgt sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗ memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp_call) (by sep_focus) ?_
  refine call_rustAllocNoOom_budget hcall size 1 st hlay hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 (by sep_focus)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf hne0 => ?_) hlr_ls
  simp only [Reg.x0] at hne0 ⊢
  refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
  exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
    SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf hne0 (beq_false_of_ne hne0) htr_sf)

theorem call_dealloc_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim))
    (p : BitVec 64) (size align : Nat) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = p) (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hsplit : P = (A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗
      stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog tgt sf
        ((A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp_call) (by sep_focus) ?_
  refine call_rustDealloc_budget hcall p size align st
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 (by sep_ac_rfl)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf => ?_) hlr_ls
  refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
  exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
    SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf htr_sf)

theorem call_memcpy_bytes_lscro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    (dst src : BitVec 64) (bs : Bytes) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hsplit : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog tgt sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sf) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  exact call_memcpy_bytes_budget (A := A) (lim := lim) hcall dst src bs st hpc hrun hsp hsp_align hlr htrace
    hx0 hx1 hx2 hsplit
    fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf =>
      SepWP.done hpc_sf hrun_sf fun hcrl1 => hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf htr_sf

theorem call_memcpy_relocate_lscro {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    {n : Nat} {Rel : BitVec 64 → SepProp} (hrel : Relocatable n Rel) (dst src : BitVec 64)
    (st : M.σ) {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ Rel src) ∗ (A.pool lim st s ∗ Frame))
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP prog tgt sf ((Rel dst ∗ memRegion src n) ∗ (A.pool lim st sf ∗ Frame)) post) :
    SepWP prog tgt s P post := by
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine call_memcpy_relocate_vm hcall hrel dst src (s0 := s0) (sp_call := sp_call)
    (Frame := A.pool lim st s ∗ Frame)
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2 hsplit
    fun sf hpc_sf hrun_sf hsp_sf htr_sf hvm_sf
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs => ?_
  rw [← A.pool_of_vmPreserved hvm_sf]
  exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
    hnext sf hcrl1 hpc_sf hrun_sf hsp_sf htr_sf
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs

/-! ## 3. Budget-Threaded Sub-Step 3 (`(blkPl_427).base + 1680#64 -> (blkPl_427).base + 1896#64`) -/

set_option maxHeartbeats 1600000 in
/-- Non-panicking (`SepWP`) budget-threaded sub-step 3 (`+1680 -> +1896`) of `.headerReceived` on
    `spqrSendPlacedProg ext`. -/
theorem step_headerReceived_1680_to_1896_sepWP_placed {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ct1_tmp_ptr info_ptr ss_ptr secret_cap secret_ptr : BitVec 64)
    (auth' : Authenticator) (hdr info secret : Bytes)
    (ct1 : List.Vector (BitVec 8) 960) (ss : List.Vector (BitVec 8) 32)
    (sending_ct1 : PolyEncoder) (outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (hinfo_len : info.length = 41)
    (henc_res : encodeBytesResult ct1.toList = .ok sending_ct1)
    (hnc : sending_ct1.nextChunk = .ok (outSt.sending_ct1, chunk))
    (st : M.σ) (hfit : FitsEnv M lim st (HeaderReceived2aEnv sending_ct1 chunk))
    {tgt : BitVec 64} {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1680#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = ss_ptr) (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch) (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = ct1_tmp_ptr) (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (_hx27 : s.readReg64 .x27 = BitVec.ofNat 64 hdr.length) (hx28 : s.readReg64 .x28 = info_ptr)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      authenticatorAt A.repAlloc (sp + 4192#64) auth' ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4704#64) 961 ∗ memRegion (sp + 5665#64) 1439 ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live info_ptr 41 1 ∗ (info_ptr ↦ₛ info) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗
      ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
      A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
      memRegion (sp + 7560#64) 8 ∗ memRegion (sp + 7568#64) 368 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (g' : AuthenticatorGhost) (ct1_ptr : BitVec 64)
      (evs : List AllocEvent),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      HeaderReceived2aEnv sending_ct1 chunk evs →
      ct1_ptr ≠ 0 → (ct1_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 1896#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = sp + 2384#64 →
      sf.readReg64 .x21 = hdr_ptr → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = ct1_tmp_ptr → sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = ct1_ptr → sf.readReg64 .x28 = sp + 4704#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A.repAlloc g' auth' ∗
          memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 928 ∗
          chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 1438 ∗
          A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
          A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
          ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7136#64) 400 ∗ polyEncoderAt A.repAlloc (sp + 7536#64) outSt.sending_ct1 ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have hshim := spqrSend_shim_ok_placed hA
  have halloc := spqrSend_allocNoOom_ok_placed hA
  have hdealloc := spqrSend_dealloc_ok_placed hA
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have henc_at : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 417) (withLsCodeRoLoaded lsmpl (encodeBytesSpecX A lim)) := henc_call
  have hnc_at : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 416) (withLsCodeRoLoaded lsmpl (polyNextChunkPlacedSpec M A lim)) := hnc_call
  have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length _
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length _
  rcases fitsEnv_headerReceived2a_split hfit with ⟨hfit_960, hfit_enc, hfit_nc, hstep_all⟩
  let st1 := M.stepEvents (rustAllocEvents 960 1) st
  let st2 := M.stepEvents (rustDeallocEvents 41 1) st1
  let st3 := M.stepEvents (rustDeallocEvents 32 1) st2
  let st4 := M.stepEvents (encodeBytesAllocEvents 960) st3
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hshim halloc hdealloc hmemcpy ⊢
  subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x28]
    at hx20 hx21 hx22 hx24 hx25 hx26 hx28
  refine SepWP.fold (authenticatorAt_entails_exists_inline_heap A.repAlloc (sp + 4192#64) auth')
    (by sep_focus) ?_
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro g'
  rw [memRegion_961_split_48_913 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 6 (apply SepWP.exists_elim; intro _)
  by_vm_lscro (lsρ spqrRustNoAllocShimSym) hinv (
    wp_conv_pre => dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_s0 hvm_s0 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_s0]
  refine call_shim_lscro A lim hshim st (s0 := s0) (sp_call := sp) hcrl_s0
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *]) (by sep_ac_rfl)
    fun sf0 hcrl_sf0 hpc_sf0 hrun_sf0 hsp_sf0 hcs_sf0 htr_sf0 => ?_
  rcases hcs_sf0 with
    ⟨hx19_0, hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, _, hvregs_0⟩
  simp only [Reg.lr, wp_norm, arm64_norm, *]
    at hpc_sf0 hx19_0 hx20_0 hx21_0 hx22_0 hx23_0 hx24_0 hx25_0 hx26_0 hx27_0 hx28_0 hvregs_0
  by_vm_lscro (lsρ spqrRustAllocSym) hcrl_sf0 (
    wp_steps
    have hfold_4192 :
        ((sp + 4192#64) ↦₆₄ g'.rootKey.cap) ∗ ((sp + 4200#64) ↦₆₄ g'.rootKey.ptr) ∗
        ((sp + 4208#64) ↦₆₄ BitVec.ofNat 64 auth'.rootKey.length) ∗
        ((sp + 4216#64) ↦₆₄ g'.macKey.cap) ∗ ((sp + 4224#64) ↦₆₄ g'.macKey.ptr) ∗
        ((sp + 4232#64) ↦₆₄ BitVec.ofNat 64 auth'.macKey.length) ⊢ memRegion (sp + 4192#64) 48 := by
      have h := authInlineWordsAt_entails_memRegion g' (sp + 4192#64) auth'
      dsimp only [authInlineWordsAt] at h
      simpa only [BitVec.add_assoc, arm64_norm, sepConj_assoc] using h
    refine SepWP.fold hfold_4192 (by sep_focus) ?_
    clear hfold_4192
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl1 hvm1 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm1]
  refine call_allocNoOom_lscro halloc 960 st ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit_960
    (s0 := s0) (ret_pc := (blkPl_427).base + 1720#64) (sp_call := sp) hcrl1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_ac_rfl)
    fun sf1 hcrl_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_
  rcases hcs1 with
    ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
  simp only [wp_norm, arm64_norm, *]
    at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1
  have hct1_mem : memRegion (sf1.readReg64 (Reg.gpr 0#5)) 960 =
      memRegion (sf1.readReg64 (Reg.gpr 0#5)) ct1.toList.length := by rw [hct1_len]
  rw [memRegion_4080_48_eq_words6 sp, memRegion_7104_24_eq_words3 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 9 (apply SepWP.exists_elim; intro _)
  by_vm_lscro (lsρ "memcpy") hcrl_ok1 (
    wp_conv_pre => rw [hct1_mem]
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_mc0 hvm_mc0 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_mc0]
  refine call_memcpy_bytes_lscro A lim hmemcpy (sf1.readReg64 (Reg.gpr 0#5)) ct1_tmp_ptr ct1.toList st1
    (s0 := s0) (sp_call := sp) hcrl_mc0
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by simp only [hct1_len, Reg.x2, arm64_norm]) (by sep_ac_rfl)
    fun sf_mc hcrl_mc1 hpc_mc hrun_mc hsp_mc hcs_mc htr_mc => ?_
  rcases hcs_mc with
    ⟨hx19_mc, hx20_mc, hx21_mc, hx22_mc, hx23_mc, hx24_mc, hx25_mc, hx26_mc, hx27_mc, hx28_mc, _, hvregs_mc⟩
  simp only [Reg.lr, wp_norm, arm64_norm, *]
    at hpc_mc hx19_mc hx20_mc hx21_mc hx22_mc hx23_mc hx24_mc hx25_mc hx26_mc hx27_mc hx28_mc hvregs_mc
  have hinfo_mem := pointsToBytes_entails_memRegion info_ptr info
  rw [hinfo_len] at hinfo_mem
  have hss_mem := pointsToBytes_entails_memRegion ss_ptr ss.toList
  rw [hss_len] at hss_mem
  refine SepWP.fold hinfo_mem (by sep_focus) ?_
  refine SepWP.fold hss_mem (by sep_focus) ?_
  by_vm_lscro (lsρ spqrRustDeallocSym) hcrl_mc1 (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_d0 hvm_d0 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_d0]
  refine call_dealloc_lscro hdealloc info_ptr 41 1 st1
    (s0 := s0) (sp_call := sp) hcrl_d0
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_ac_rfl)
    fun sf_d1 hcrl_d1 hpc_d1 hrun_d1 hsp_d1 hcs_d1 htr_d1 => ?_
  rcases hcs_d1 with
    ⟨hx19_d1, hx20_d1, hx21_d1, hx22_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, hx27_d1, hx28_d1, _, hvregs_d1⟩
  simp only [Reg.lr, wp_norm, arm64_norm, *]
    at hpc_d1 hx19_d1 hx20_d1 hx21_d1 hx22_d1 hx23_d1 hx24_d1 hx25_d1 hx26_d1 hx27_d1 hx28_d1 hvregs_d1
  by_vm_lscro (lsρ spqrRustDeallocSym) hcrl_d1 (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_d2 hvm_d2 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm_d2]
  refine call_dealloc_lscro hdealloc ss_ptr 32 1 st2
    (s0 := s0) (sp_call := sp) hcrl_d2
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm])
    (by simp only [Reg.x2, arm64_norm]) (by sep_ac_rfl)
    fun sf_d2 hcrl_d3 hpc_d2 hrun_d2 hsp_d2 hcs_d2 htr_d2 => ?_
  rcases hcs_d2 with
    ⟨hx19_d2, hx20_d2, hx21_d2, hx22_d2, hx23_d2, hx24_d2, hx25_d2, hx26_d2, hx27_d2, hx28_d2, _, hvregs_d2⟩
  simp only [Reg.lr, wp_norm, arm64_norm, *]
    at hpc_d2 hx19_d2 hx20_d2 hx21_d2 hx22_d2 hx23_d2 hx24_d2 hx25_d2 hx26_d2 hx27_d2 hx28_d2 hvregs_d2
  refine SepWP.fold (fold_7536_to_memRegion_400 sp secret_cap secret_ptr 32#64) (by sep_focus) ?_
  refine SepWP.fold (fold_4080_and_4704 sp g' auth') (by sep_focus) ?_
  by_vm_lscro (lsmpl.base 417) hcrl_d3 (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl2 hvm2 => ?_⟩)
  rw [← A.pool_of_vmPreserved hvm2]
  refine call_lscro_calleeStack_evs_sepWP
    (x := (({
      out := sp + 7136#64, msgRO := false, msgA := ct1_tmp_ptr,
      msg := ct1.toList } : EncodeBytesGhost), st3))
    sp encodeBytesStackX (by decide)
    (T_pre := memRegion (sp + 7136#64) polyEncoderSize ∗
      (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.pool lim st3 _)
    (T_post := fun evs_enc sf => ⌜sf.trace = _⌝ ∗
      polyEncoderAt A.repAlloc (sp + 7136#64) sending_ct1 ∗
      (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.pool lim (M.stepEvents evs_enc st3) sf)
    (F := ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A.repAlloc g' auth' ∗
      memRegion (sp + 4192#64) 48 ∗
      memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 ∗
      A.live ct1_tmp_ptr 960 1 ∗
      A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
      ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
      A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
      memRegion (sp + 7536#64) 400 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)
    (φ_pre := _) (φ_post := fun evs_enc _ => EncodeBytesEnv 960 evs_enc) henc_at hcrl2
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (ret_pc := (blkPl_427).base + 1832#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
    (by
      dsimp only [encodeBytesSpecX, encodeBytesSpecXOfEnv,
        CryptoVerification.SpqrV1.Poly.EncodeBytes.bytesAt]
      simp only [Bool.false_eq_true, ↓reduceIte]
      sep_ac_rfl)
    (by
      refine ⟨by simp only [Reg.x8, wp_norm, arm64_norm, *],
        by simp only [Reg.x0, wp_norm, arm64_norm, *],
        by simp only [hct1_len, Reg.x1, wp_norm, arm64_norm, *],
        by rw [hct1_len]; decide, ?_⟩
      simpa only [hct1_len] using hfit_enc)
    (by dsimp only [polyEncoderSize, authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; sep_ac_rfl)
    (fun _ _ => rfl)
    (fun _ => Entails.refl ⌜False⌝)
    (by
      intro sf
      dsimp only [encodeBytesSpecX, encodeBytesSpecXOfEnv,
        CryptoVerification.SpqrV1.Poly.EncodeBytes.bytesAt]
      rw [henc_res, resultPolyEncoderAt, hct1_len]
      simp only [Bool.false_eq_true, ↓reduceIte, sepExists_sepConj_left, sepExists_sepConj_right]
      exact sepExists_congr fun _ => by sep_ac_rfl) ?_
  intro sm1 evs_enc hpc_sm1 hrun_sm1 hsp_sm1 hevs_enc hcrl_sm1
    hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
  rcases hevs_enc with rfl
  change SepWP _ _ _
    ((stackAt sp spqrSendCalleeStack ∗
      (⌜sm1.trace = _⌝ ∗ polyEncoderAt A.repAlloc (sp + 7136#64) sending_ct1 ∗
       (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.pool lim st4 sm1)) ∗ _) _
  rw [sepConj_left_comm (stackAt sp spqrSendCalleeStack), sepConj_assoc]
  refine SepWP.pure_elim fun htr_sm1 => ?_
  simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
    wp_norm, arm64_norm, *]
    at htr_sm1 hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
  have h1868 : ∀ s_m : State,
      LibsignalCodeRoLoaded lsmpl s_m.mem →
      s_m.pc = lsρ "memcpy" → s_m.status = .Running → s_m.sp = sp → s_m.trace = s0.trace →
      calleeSavedVRegs s_m = calleeSavedVRegs s →
      s_m.readReg64 Reg.lr = (blkPl_427).base + 1872#64 →
      s_m.readReg64 Reg.x0 = sp + 7536#64 → s_m.readReg64 Reg.x1 = sp + 7136#64 →
      (s_m.readReg64 Reg.x2).toNat = 400 →
      s_m.readReg64 .x19 = s.readReg64 .x19 → s_m.readReg64 .x20 = sp + 2384#64 →
      s_m.readReg64 .x21 = hdr_ptr → s_m.readReg64 .x22 = epoch →
      s_m.readReg64 .x23 = s.readReg64 .x23 → s_m.readReg64 .x24 = es_ptr →
      s_m.readReg64 .x25 = ct1_tmp_ptr → s_m.readReg64 .x26 = sp + 4704#64 →
      s_m.readReg64 .x27 = sf1.readReg64 (Reg.gpr 0#5) →
      SepWP ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext)) tgt s_m
        ((stackAt sp spqrSendCalleeStack ∗
          (polyEncoderAt A.repAlloc (sp + 7136#64) sending_ct1 ∗
           (ct1_tmp_ptr ↦ₛ ct1.toList) ∗ A.pool lim st4 s_m)) ∗
         ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
         authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A.repAlloc g' auth' ∗
         memRegion (sp + 4192#64) 48 ∗
         memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 ∗
         A.live ct1_tmp_ptr 960 1 ∗
         A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
         ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
         A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
         memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
         memRegion (sp + 7536#64) 400 ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) post := by
    intro s_m hcrlm hpcm hrunm hspm htrm hvregsm hlrm hx0m hx1m hx2m
      hx19m hx20m hx21m hx22m hx23m hx24m hx25m hx26m hx27m
    refine call_memcpy_relocate_lscro A lim hmemcpy (Relocatable.of_polyEncoderAt A.repAlloc sending_ct1)
      (sp + 7536#64) (sp + 7136#64) st4 (s0 := s0) (sp_call := sp)
      (Frame := stackAt sp spqrSendCalleeStack ∗
        (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
        ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
        authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A.repAlloc g' auth' ∗
        memRegion (sp + 4192#64) 48 ∗
        memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5632#64) 34 ∗ memRegion (sp + 5666#64) 1438 ∗
        A.live ct1_tmp_ptr 960 1 ∗
        A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
        ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
        A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
        memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)
      hcrlm hpcm hrunm hspm hsp_align hlrm htrm hx0m hx1m hx2m
      (by sep_ac_rfl) ?_
    intro sf2 hcrl_sf2 hpc_sf2 hrun_sf2 hsp_sf2 htr_sf2
      hx19_sf2 hx20_sf2 hx21_sf2 hx22_sf2 hx23_sf2 hx24_sf2 hx25_sf2 hx26_sf2 hx27_sf2 _ hvregs_sf2
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      wp_norm, arm64_norm, *]
      at hx19_sf2 hx20_sf2 hx21_sf2 hx22_sf2 hx23_sf2 hx24_sf2 hx25_sf2 hx26_sf2 hx27_sf2 hvregs_sf2
    by_vm_lscro (lsmpl.base 416) hcrl_sf2 (
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl3 hvm3 => ?_⟩)
    rw [← A.pool_of_vmPreserved hvm3]
    refine call_lscro_calleeStack_evs_sepWP
      (x := (({
        outA := sp + 5632#64, encA := sp + 7536#64,
        enc := sending_ct1, enc' := outSt.sending_ct1, chunk := chunk } : PolyNextChunkGhost), st4))
      sp polyNextChunkStack (by decide)
      (T_pre := memRegion (sp + 5632#64) chunkSize ∗
        polyEncoderAt A.repAlloc (sp + 7536#64) sending_ct1 ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st4 _)
      (T_post := fun evs_nc sf => polyEncoderAt A.repAlloc (sp + 7536#64) outSt.sending_ct1 ∗
        chunkAt (sp + 5632#64) chunk ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim (M.stepEvents evs_nc st4) sf)
      (F := memRegion (sp + 7136#64) 400 ∗
        (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
        ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
        authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A.repAlloc g' auth' ∗
        memRegion (sp + 4192#64) 48 ∗
        memRegion (sp + 4704#64) 928 ∗ memRegion (sp + 5666#64) 1438 ∗
        A.live ct1_tmp_ptr 960 1 ∗
        A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
        ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
        A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
        memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗ Frame)
      (φ_pre := _) (φ_post := _) hnc_at hcrl3
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align
      (ret_pc := (blkPl_427).base + 1896#64) (by simp only [Reg.lr, wp_norm, arm64_norm, *])
      (by dsimp only [polyNextChunkPlacedSpec, polyNextChunkPlacedSpecOfEnv]; sep_ac_rfl)
      (by
        refine ⟨by simp only [Reg.x8, wp_norm, arm64_norm, *],
          by simp only [Reg.x0, wp_norm, arm64_norm, *], hnc, ?_⟩
        rw [polyNextChunkEnv_eq_enc]
        exact hfit_nc)
      (by dsimp only [polyEncoderSize, chunkSize]; sep_ac_rfl)
      (fun _ _ => rfl)
      (fun sf => Entails.of_eq (polyNextChunkPlaced_onPanic_false_of_ok _ st4 hnc _ sf))
      (by
        intro sf
        dsimp only [polyNextChunkPlacedSpec, polyNextChunkPlacedSpecOfEnv]
        exact sepExists_congr fun _ => by sep_ac_rfl) ?_
    intro sm2 evs_nc hpc_sm2 hrun_sm2 hsp_sm2 ⟨hevs_nc, htr_sm2⟩ hcrl_sm2
      hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      wp_norm, arm64_norm, *]
      at htr_sm2 hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
    have hevs_enc : PolyNextChunkEncEnv sending_ct1 chunk evs_nc := hevs_nc
    rcases hstep_all evs_nc hevs_enc with ⟨hevs2a, hstep_eq⟩
    rw [hstep_eq]
    apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 1896#64) hcrl_sm2
    exact finish_sepWP_lscro_plain hpc_sm2 hrun_sm2
      (fun hcrl4 => hnext sm2 g' (sf1.readReg64 (Reg.gpr 0#5))
        (headerReceived2aPreEvents ++ evs_nc) hcrl4 hevs2a hne0_1 h0b_1
        hpc_sm2 hrun_sm2 hsp_sm2
        hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2
        htr_sm2 hvregs_sm2)
      (Entails.of_eq (by sep_ac_rfl))
  obtain ⟨tag, htag01, encRest, henc_split⟩ :=
    polyEncoderAt_split_tag A.repAlloc (sp + 7136#64) sending_ct1
  rcases htag01 with rfl | rfl
  · by_vm_lscro (lsρ "memcpy") hcrl_sm1 (
      wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_t0 hvm_t0 => ?_⟩)
    rw [← A.pool_of_vmPreserved hvm_t0]
    exact h1868 _ hcrl_t0 (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x25, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x27, arm64_norm, *])
  · by_vm_lscro (lsρ "memcpy") hcrl_sm1 (
      wp_conv_pre => rw [henc_split]
      wp_steps
      wp_conv_pre => rw [← henc_split]
      refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], fun hcrl_t1 hvm_t1 => ?_⟩)
    rw [← A.pool_of_vmPreserved hvm_t1]
    exact h1868 _ hcrl_t1 (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
      (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm])
      (by simp only [Reg.x19, arm64_norm, *]) (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *]) (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *]) (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x25, arm64_norm, *]) (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x27, arm64_norm, *])

/-- Panic-aware (`SepWPp`) wrapper for `step_headerReceived_1680_to_1896_sepWP_placed`,
    generalized over arbitrary `post` and `Qp`. -/
theorem step_headerReceived_1680_to_1896_placed {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (henc_call : EncodeBytesPlacedOkX A lim ext)
    (hnc_call : PolyNextChunkPlacedOkX M A lim ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ct1_tmp_ptr info_ptr ss_ptr secret_cap secret_ptr : BitVec 64)
    (auth' : Authenticator) (hdr info secret : Bytes)
    (ct1 : List.Vector (BitVec 8) 960) (ss : List.Vector (BitVec 8) 32)
    (sending_ct1 : PolyEncoder) (outSt : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk) (hinfo_len : info.length = 41)
    (henc_res : encodeBytesResult ct1.toList = .ok sending_ct1)
    (hnc : sending_ct1.nextChunk = .ok (outSt.sending_ct1, chunk))
    (st : M.σ) (hfit : FitsEnv M lim st (HeaderReceived2aEnv sending_ct1 chunk))
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1680#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = ss_ptr) (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch) (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = ct1_tmp_ptr) (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 hdr.length) (hx28 : s.readReg64 .x28 = info_ptr)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      authenticatorAt A.repAlloc (sp + 4192#64) auth' ∗ memRegion (sp + 4080#64) 48 ∗
      memRegion (sp + 4704#64) 961 ∗ memRegion (sp + 5665#64) 1439 ∗
      A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
      A.live info_ptr 41 1 ∗ (info_ptr ↦ₛ info) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗
      ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
      A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
      memRegion (sp + 7560#64) 8 ∗ memRegion (sp + 7568#64) 368 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      A.pool lim st s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (g' : AuthenticatorGhost) (ct1_ptr : BitVec 64)
      (evs : List AllocEvent),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      HeaderReceived2aEnv sending_ct1 chunk evs →
      ct1_ptr ≠ 0 → (ct1_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 1896#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = sp + 2384#64 →
      sf.readReg64 .x21 = hdr_ptr → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = ct1_tmp_ptr → sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = ct1_ptr → sf.readReg64 .x28 = sp + 4704#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g' (sp + 4080#64) auth' ∗ authHeapBufs A.repAlloc g' auth' ∗
          memRegion (sp + 4192#64) 48 ∗ memRegion (sp + 4704#64) 928 ∗
          chunkAt (sp + 5632#64) chunk ∗ memRegion (sp + 5666#64) 1438 ∗
          A.live ct1_tmp_ptr 960 1 ∗ (ct1_tmp_ptr ↦ₛ ct1.toList) ∗
          A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
          ((sp + 7104#64) ↦₆₄ secret_cap) ∗ ((sp + 7112#64) ↦₆₄ secret_ptr) ∗ ((sp + 7120#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7136#64) 400 ∗ polyEncoderAt A.repAlloc (sp + 7536#64) outSt.sending_ct1 ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 1896#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_headerReceived_1680_to_1896_sepWP_placed hA henc_call hnc_call
    sp epoch hdr_cap hdr_ptr es_ptr ct1_tmp_ptr info_ptr ss_ptr secret_cap secret_ptr
    auth' hdr info secret ct1 ss sending_ct1 outSt chunk hinfo_len henc_res hnc st hfit
    hinv hsp_align hpc hrun hsp hx20 hx21 hx22 hx24 hx25 hx26 hx27 hx28 htrace hP
    fun sf g' ct1_ptr evs hcrl_sf hevs hne h0b hpc_sf hrun_sf hsp_sf
      hx19 hx20' hx21' hx22' hx23 hx24' hx25' hx26' hx27' hx28' htr hvregs =>
      SepWP.done hpc_sf hrun_sf fun _ =>
        hnext sf g' ct1_ptr evs hcrl_sf hevs hne h0b hpc_sf hrun_sf hsp_sf
          hx19 hx20' hx21' hx22' hx23 hx24' hx25' hx26' hx27' hx28' htr hvregs

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2PlacedBudgetAux
