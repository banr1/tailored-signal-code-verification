/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1DispatchPlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1FromPbPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Dispatch
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 1c: `<States>::from_pb`, Error Path, & Dispatch (Block `427`)

Threads `RustCliAllocBudget` and `VmPreserved` through `<States>::from_pb` pre-call setup,
error-path deallocation (`+248 -> +904`), and `Ok(st0)` 11-arm jump-table dispatch.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1DispatchPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sessionMemcpyRegionSpec spqrSendResultAt spqrSendStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1
  (ChainPB Error States V1State VersionNegotiationPB spqrAuthApi spqrPolyApi)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt)
open CryptoVerification.SpqrV1.Poly (polyEncoderPointsTag polyEncoderPolysTag)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (align_pre)
open CryptoVerification.SpqrV1.ProtoRepr (optChainPBAt)
open CryptoVerification.SpqrV1.States.FromPb (resultChunkedStatesAt)
open CryptoVerification.SpqrV1.States.Leaves (relocatedHeap)
open CryptoVerification.SpqrV1.Top.DecodeState (optVersionNegotiationPBTailAt)
open CryptoVerification.SpqrV1.Top.Send
  (bv_add_add_lit1 bv_add_add_lit2 chunkedStatesAt_1260_entails_reloc chunkedStatesTail920At
   chunkedStatesWord0 err_ret_entails_sendResultAt_none memRegion_b0_to_1260_split_930
   memRegion_rejoin_30_48 memRegion_ret_72_split_err memRegion_sp_930_split_24
   memRegion_sp_950_split_4words_896 optVersionNegotiationPBTail_cleanup_entails polyEncoderTagVal
   reassemble_1260_after_memcpy reassemble_chunkedStatesAt_950 rejoin_b0_to_1f20_after_states_err
   resultChunkedStatesAt_err_entails_head32_896 slt_one_false_iff slt_one_true_iff
   sp_add_1260_add_16 sp_add_1260_add_24 sp_add_1260_add_32 sp_add_1260_add_8
   sp_add_1268_add_16 sp_add_1268_add_24 sp_add_1268_add_8 sp_add_30_add_80
   sp_add_4096_add_608 sp_add_4096_add_640 sp_add_4096_add_96
   sp_add_930_add_16 sp_add_930_add_8
   sp_add_950_add_16 sp_add_950_add_24 sp_add_950_add_32 sp_add_950_add_8
   sp_add_958_add_16 sp_add_958_add_24 sp_add_958_add_8
   spqrSendCalleeStack spqrSendName spqrSendSavedRegs spqrSendStatesJumpTableWordsAt
   statesSendArmOffset words3_930_entails_memRegion_24)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg spqrSendRoSym
   spqrSendStatesJumpTablePlacedAt spqrSendStatesJumpTablePlacedAt_eq_words)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1FromPbPlacedBudget (seq_lscro)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
  (seq_vm_lscro spqr_send_chain_drop_epilogue_4608_placed
   spqr_send_vn_chain_drop_epilogue_904_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlacedBudget
  (spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

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
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp] do
    Lean.Attribute.erase nm `arm64_norm
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero bv_add_add_lit1 bv_add_add_lit2
  sp_add_30_add_80 sp_add_1260_add_8 sp_add_1260_add_16 sp_add_1260_add_24 sp_add_1260_add_32
  sp_add_1268_add_8 sp_add_1268_add_16 sp_add_1268_add_24
  sp_add_930_add_8 sp_add_930_add_16
  sp_add_950_add_8 sp_add_950_add_16 sp_add_950_add_24 sp_add_950_add_32
  sp_add_958_add_8 sp_add_958_add_16 sp_add_958_add_24
  sp_add_4096_add_608 sp_add_4096_add_640 sp_add_4096_add_96
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm, local wp_norm]
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg

omit [LibsignalPlacement] in
@[local arm64_norm, local wp_norm]
private theorem bv_add_add_lit_p1dpb (x : BitVec 64) (a b : Nat) :
    (x + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## 1. VM-Preserving Pre-Call Step (`+224 -> lsmpl.base 333`) -/

/-- VM-preserving relocatable pre-call setup (`+224 -> lsmpl.base 333`):
    computes `x8 = sp + 0x1260`, `x0 = sp + 0xb0`, `x21 = sp + 0x1260`, and branches with link
    (`x30 = spqrSendPlacedEntry + 248#64`) to `<States>::from_pb` (Block `333`), preserving
    `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
theorem spqr_send_pre_states_from_pb_224_placed_vm
    {ext : String → Option (State → State)}
    {s0 s : State} {sp : BitVec 64} (P : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = sp + 0x30#64) :
    SepWP (spqrSendPlacedProg ext) (lsmpl.base 333) s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        Pf = P ∧
        sf.sp = sp ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x0 = sp + 0xb0#64 ∧
        sf.readReg64 .x8 = sp + 0x1260#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = sp + 0x30#64 ∧
        sf.readReg64 .x21 = sp + 0x1260#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        sf.readReg64 .x30 = spqrSendPlacedEntry + 248#64) := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_steps
    refine ProofLib.SepWP.done
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        rfl,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩,
        by simp only [wp_norm, arm64_norm, *]⟩)

/-- Continuation-passing wrapper for `spqr_send_pre_states_from_pb_224_placed_vm`
    (`+224 -> lsmpl.base 333`), supplying `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
theorem spqr_send_pre_states_from_pb_224_placed
    {ext : String → Option (State → State)}
    {s0 s : State} {sp : BitVec 64} {P : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = sp + 0x30#64)
    (hnext : ∀ sf : State,
      VmPreserved s sf →
      AllocCallPreserved s sf →
      sf.pc = lsmpl.base 333 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = sp + 0xb0#64 →
      sf.readReg64 .x8 = sp + 0x1260#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = sp + 0x30#64 →
      sf.readReg64 .x21 = sp + 0x1260#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) →
      sf.readReg64 .x30 = spqrSendPlacedEntry + 248#64 →
      SepWP (spqrSendPlacedProg ext) (lsmpl.base 333) sf P post) :
    SepWP (spqrSendPlacedProg ext) (lsmpl.base 333) s P post := by
  refine SepWP.seq
    (spqr_send_pre_states_from_pb_224_placed_vm P hpc hrun hsp hsp_align htrace hx20) ?_
  rintro sf Pf hpc_f hrun_f
    ⟨hvm, hacp, rfl, hsp_f, htr_f, hx0_f, hx8_f, hx19_f, hx20_f, hx21_f,
     hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hx30_f⟩
  exact hnext sf hvm hacp hpc_f hrun_f hsp_f htr_f hx0_f hx8_f hx19_f hx20_f hx21_f
    hx22_f hx23_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f

/-- Pool-threading corollary of `spqr_send_pre_states_from_pb_224_placed`, transporting
    `A.pool lim st s` to `A.pool lim st sf` across `VmPreserved s sf`. -/
theorem spqr_send_pre_states_from_pb_224_placed_pool
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {s0 s : State} {st : M.σ} {sp : BitVec 64} {Rest : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = sp + 0x30#64)
    (hnext : ∀ sf : State,
      VmPreserved s sf →
      AllocCallPreserved s sf →
      sf.pc = lsmpl.base 333 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = sp + 0xb0#64 →
      sf.readReg64 .x8 = sp + 0x1260#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = sp + 0x30#64 →
      sf.readReg64 .x21 = sp + 0x1260#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) →
      sf.readReg64 .x30 = spqrSendPlacedEntry + 248#64 →
      SepWP (spqrSendPlacedProg ext) (lsmpl.base 333) sf (A.pool lim st sf ∗ Rest) post) :
    SepWP (spqrSendPlacedProg ext) (lsmpl.base 333) s (A.pool lim st s ∗ Rest) post := by
  refine spqr_send_pre_states_from_pb_224_placed hpc hrun hsp hsp_align htrace hx20 ?_
  intro sf hvm hacp hpc_f hrun_f hsp_f htr_f hx0_f hx8_f hx19_f hx20_f hx21_f
    hx22_f hx23_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f
  rw [← A.pool_transport lim st s sf hvm]
  exact hnext sf hvm hacp hpc_f hrun_f hsp_f htr_f hx0_f hx8_f hx19_f hx20_f hx21_f
    hx22_f hx23_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f

/-! ## 2. Budget-Threaded `States.from_pb = .error (.err err)` Path (`+248 -> +872 -> +4608/+904 -> s0.lr`) -/

/-- Budget-threaded relocatable `States.from_pb = .error (.err err)` path
    (`+248 -> +872 -> +4608/+904 -> s0.lr`):
    copies the `Err` header from `sp + 0x1260..0x1280` via `sp + 0x930..0x948` to `ret` (`x19`),
    drops `pq.versionNegotiation` (if `some`) and `pq.chain` with `FreeOnlyEvs evs`, and returns
    to `s0.lr` preserving `AllocCallPreserved s sf`. -/
theorem spqr_send_states_from_pb_err_step_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 s : State) (st : M.σ) (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB)
    (err : Error) (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1260 - 0xb0) ∗
        resultChunkedStatesAt A.repAlloc (F := F)
          ((s0.sp - 0x1f80#64) + 0x1260#64) (.error (.err err)) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
        memRegion ret 72 ∗
        A.pool lim st s ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          (Pf ⊢
            spqrSendResultAt A.repAlloc ret none ∗
            A.pool lim (M.stepEvents evs st) sf ∗
            stackAt s0.sp spqrSendStack ∗
            Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  by_cases hslt : BitVec.slt w0 1#64 = true
  · have hge_false := slt_one_true_iff hslt
    refine seq_vm_lscro hcrl
      (mid := spqrSendPlacedEntry + 4608#64)
      (P_mid :=
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗
        (spqrSendResultAt A.repAlloc ret none ∗ Rest))
      (Q := fun sm =>
        AllocCallPreserved s sm ∧
        sm.sp = s0.sp - 0x1f80#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
      have herr_split :=
        resultChunkedStatesAt_err_entails_head32_896 A.repAlloc (F := F) (fsp + 4704#64) err
      have ha1268 : (fsp + 4704#64) + 8#64 = fsp + 4712#64 := by bv_omega
      have ha1270 : (fsp + 4704#64) + 16#64 = fsp + 4720#64 := by bv_omega
      have ha1278 : (fsp + 4704#64) + 24#64 = fsp + 4728#64 := by bv_omega
      have ha1280 : (fsp + 4704#64) + 32#64 = fsp + 4736#64 := by bv_omega
      rw [ha1268, ha1270, ha1278, ha1280] at herr_split
      by_vm_steps (
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono (memRegion_b0_to_1260_split_930 fsp)
                (sepConj_mono herr_split
                  (sepConj_mono_right (sepConj_mono_left (memRegion_ret_72_split_err ret))))))))))) ?_
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply ProofLib.SepWP.exists_left; intro r0
        apply ProofLib.SepWP.exists_left; intro rw8
        apply ProofLib.SepWP.exists_left; intro rw16
        apply ProofLib.SepWP.exists_left; intro rw24
        apply ProofLib.SepWP.exists_left; intro ew1
        apply ProofLib.SepWP.exists_left; intro ew2
        apply ProofLib.SepWP.exists_left; intro ew3
        apply ProofLib.SepWP.exists_left; intro s0_930
        apply ProofLib.SepWP.exists_left; intro s1_938
        apply ProofLib.SepWP.exists_left; intro s2_940
        wp_steps
        refine ProofLib.SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *], ?_,
            by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *],
            by simp only [wp_norm, arm64_norm, *]⟩
        have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A.repAlloc (fsp + 48#64) w0 w1 vn
        have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
        have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
        rw [ha56, ha64, hslt] at hvn_drop
        simp only [↓reduceIte] at hvn_drop
        have h60 : memRegion fsp 48 ∗ memRegion (fsp + 48#64) 48 ⊢ memRegion fsp 96 := by
          rw [memRegion_rejoin_30_48 fsp]
          exact Entails.refl _
        have hb0 := rejoin_b0_to_1f20_after_states_err fsp noneCap ew1 ew2 ew3
        have hret := err_ret_entails_sendResultAt_none A.repAlloc ret ew1 ew2 ew3
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion fsp 48 ∗
             (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
              optVersionNegotiationPBTailAt A.repAlloc w0 w1 (fsp + 64#64) vn)) ∗
            (memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
             ((fsp + 2352#64) ↦₆₄ ew1) ∗
             ((fsp + 2360#64) ↦₆₄ ew2) ∗
             ((fsp + 2368#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
             ((fsp + 4704#64) ↦₆₄ noneCap) ∗
             ((fsp + 4712#64) ↦₆₄ ew1) ∗
             ((fsp + 4720#64) ↦₆₄ ew2) ∗
             ((fsp + 4728#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 4736#64) 896 ∗
             memRegion (fsp + 5632#64) (0x1f20 - 0x1600)) ∗
            ((ret ↦₆₄ 18446744073709551615#64) ∗
             ((ret + 8#64) ↦₆₄ ew1) ∗
             ((ret + 16#64) ↦₆₄ ew2) ∗
             ((ret + 24#64) ↦₆₄ ew3) ∗
             memRegion (ret + 32#64) 40) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             optChainPBAt A.repAlloc (fsp + 96#64) chain ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool lim st s ∗ Rest) by sep_ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono (Entails.trans (sepConj_mono_right hvn_drop) h60)
            (sepConj_mono hb0 (sepConj_mono_left hret))) ?_
        exact Entails.of_eq (by sep_ac_rfl))
    · intro s2 hpc2 hrun2 hcrl2 hvm2 ⟨hacp2, hsp2, htr2, hvregs2⟩
      rw [← A.pool_transport lim st s s2 hvm2]
      have hep := spqr_send_chain_drop_epilogue_4608_placed hdropChain s0 s2 st chain
        (spqrSendResultAt A.repAlloc ret none ∗ Rest)
        hcrl2 hsp0_align hpc2 hrun2 hsp2 hvregs2
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨evs, hevs, hacp_f, hPf, hsp_f, hcc_f, htr_f⟩
      exact ⟨evs, hevs, hacp2.trans hacp_f,
        Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩
  · have hslt_f : BitVec.slt w0 1#64 = false := Bool.eq_false_iff.mpr hslt
    have hge_true := slt_one_false_iff hslt_f
    refine seq_lscro hcrl
      (mid := spqrSendPlacedEntry + 904#64)
      (Mid := fun s1 P1 =>
        VmPreserved s s1 ∧
        AllocCallPreserved s s1 ∧
        0 < w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
          A.live w1 w0.toNat 1 ∗
          memRegion w1 w0.toNat ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim st s ∗
          (spqrSendResultAt A.repAlloc ret none ∗ Rest)) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x23 = w0 ∧
        s1.trace = s.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
      have herr_split :=
        resultChunkedStatesAt_err_entails_head32_896 A.repAlloc (F := F) (fsp + 4704#64) err
      have ha1268 : (fsp + 4704#64) + 8#64 = fsp + 4712#64 := by bv_omega
      have ha1270 : (fsp + 4704#64) + 16#64 = fsp + 4720#64 := by bv_omega
      have ha1278 : (fsp + 4704#64) + 24#64 = fsp + 4728#64 := by bv_omega
      have ha1280 : (fsp + 4704#64) + 32#64 = fsp + 4736#64 := by bv_omega
      rw [ha1268, ha1270, ha1278, ha1280] at herr_split
      have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A.repAlloc (fsp + 48#64) w0 w1 vn
      have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
      have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
      rw [ha56, ha64, hslt_f] at hvn_drop
      simp only [Bool.false_eq_true, ↓reduceIte] at hvn_drop
      dsimp only [RustCliAllocBudget.repAlloc] at hvn_drop
      by_vm_steps (
        refine SepWP.weaken_pre
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono (memRegion_b0_to_1260_split_930 fsp)
                (sepConj_mono herr_split
                  (sepConj_mono_right (sepConj_mono_left (memRegion_ret_72_split_err ret))))))))))) ?_
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        apply ProofLib.SepWP.exists_left; intro r0
        apply ProofLib.SepWP.exists_left; intro rw8
        apply ProofLib.SepWP.exists_left; intro rw16
        apply ProofLib.SepWP.exists_left; intro rw24
        apply ProofLib.SepWP.exists_left; intro ew1
        apply ProofLib.SepWP.exists_left; intro ew2
        apply ProofLib.SepWP.exists_left; intro ew3
        apply ProofLib.SepWP.exists_left; intro s0_930
        apply ProofLib.SepWP.exists_left; intro s1_938
        apply ProofLib.SepWP.exists_left; intro s2_940
        wp_steps
        refine SepWP.weaken_pre
          (Entails.trans
            (Entails.of_eq (show _ =
              (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
               optVersionNegotiationPBTailAt A.repAlloc w0 w1 (fsp + 64#64) vn) ∗
              (stackAt fsp spqrSendCalleeStack ∗
               memRegion fsp 48 ∗
               optChainPBAt A.repAlloc (fsp + 96#64) chain ∗
               memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
               ((fsp + 2352#64) ↦₆₄ ew1) ∗
               ((fsp + 2360#64) ↦₆₄ ew2) ∗
               ((fsp + 2368#64) ↦₆₄ ew3) ∗
               memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
               ((fsp + 4704#64) ↦₆₄ noneCap) ∗
               ((fsp + 4712#64) ↦₆₄ ew1) ∗
               ((fsp + 4720#64) ↦₆₄ ew2) ∗
               ((fsp + 4728#64) ↦₆₄ ew3) ∗
               memRegion (fsp + 4736#64) 896 ∗
               memRegion (fsp + 5632#64) (0x1f20 - 0x1600) ∗
               (ret ↦₆₄ 18446744073709551615#64) ∗
               ((ret + 8#64) ↦₆₄ ew1) ∗
               ((ret + 16#64) ↦₆₄ ew2) ∗
               ((ret + 24#64) ↦₆₄ ew3) ∗
               memRegion (ret + 32#64) 40 ∗
               A.pool lim st s ∗
               spqrSendSavedRegs fsp s0 ∗
               Rest) by sep_ac_rfl))
            (sepConj_mono_left hvn_drop)) ?_
        wp_focus_pure; rintro ⟨hw0_pos, hw0_lt, hw1_ne⟩
        refine ProofLib.SepWP.done
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) ?_
        refine ⟨by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          hw0_pos, hw0_lt, hw1_ne, ?_,
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *]⟩
        have hb0 := rejoin_b0_to_1f20_after_states_err fsp noneCap ew1 ew2 ew3
        have hret := err_ret_entails_sendResultAt_none A.repAlloc ret ew1 ew2 ew3
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
             ((fsp + 2352#64) ↦₆₄ ew1) ∗
             ((fsp + 2360#64) ↦₆₄ ew2) ∗
             ((fsp + 2368#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
             ((fsp + 4704#64) ↦₆₄ noneCap) ∗
             ((fsp + 4712#64) ↦₆₄ ew1) ∗
             ((fsp + 4720#64) ↦₆₄ ew2) ∗
             ((fsp + 4728#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 4736#64) 896 ∗
             memRegion (fsp + 5632#64) (0x1f20 - 0x1600)) ∗
            ((ret ↦₆₄ 18446744073709551615#64) ∗
             ((ret + 8#64) ↦₆₄ ew1) ∗
             ((ret + 16#64) ↦₆₄ ew2) ∗
             ((ret + 24#64) ↦₆₄ ew3) ∗
             memRegion (ret + 32#64) 40) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 48 ∗
             memRegion (fsp + 48#64) 8 ∗
             ((fsp + 56#64) ↦₆₄ w1) ∗
             memRegion (fsp + 64#64) 32 ∗
             A.live w1 w0.toNat 1 ∗
             memRegion w1 w0.toNat ∗
             optChainPBAt A.repAlloc (fsp + 96#64) chain ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool lim st s ∗ Rest) by sep_ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hb0 (sepConj_mono_left hret)) ?_
        exact Entails.of_eq (by sep_ac_rfl))
    · intro s1 P1 hpc1 hrun1 hcrl1
        ⟨hvm1, hacp1, hw0_pos, hw0_lt, hw1_ne, hP1, hsp1, hx23_1, htr1, hvregs1⟩
      rw [← A.pool_transport lim st s s1 hvm1] at hP1
      refine SepWP.weaken_pre hP1 ?_
      have hep := spqr_send_vn_chain_drop_epilogue_904_placed hA hdropChain s0 s1 st w0 w1 chain
        (spqrSendResultAt A.repAlloc ret none ∗ Rest)
        hcrl1 hsp0_align hpc1 hrun1 hsp1 hx23_1 hw0_pos hw0_lt hw1_ne hvregs1
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨evs, hevs, hacp_f, hPf, hsp_f, hcc_f, htr_f⟩
      exact ⟨evs, hevs, hacp1.trans hacp_f,
        Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f, hcc_f, htr_f.trans htr1⟩

/-! ## 3. VM-Preserving `States.from_pb = .ok st0` Relocation & Jump-Table 1 Dispatch (`+248 -> +336 -> arm`) -/

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem chunkedStatesWord0_beq_neg1 {F : ShaCompress}
    (st0 : States spqrPolyApi (spqrAuthApi F)) :
    (chunkedStatesWord0 st0 == 18446744073709551615#64) = false := by
  cases st0 with
  | ct1Sampled s => dsimp only [chunkedStatesWord0]; cases s.sending_ct1.s <;> rfl
  | _ => rfl

omit [LibsignalPlacement] in
private theorem sepWP_with_vm {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (h : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP (P.rebase b Hk) mid s Pre post :=
  SepWP.mono (sepWP_rebase_vmPreserved h) fun _ _ _ _ ⟨hvm, hp⟩ => hp hvm

omit [LibsignalPlacement] in
private theorem sepWP_cut_here {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun _ _ _ _ h => h

omit [LibsignalPlacement] in
private theorem sepWP_trans_vm {prog : Program} {target : BitVec 64} {s0 s1 : State}
    {P : SepProp} {rest : State → SepProp → Prop}
    (h01 : VmPreserved s0 s1)
    (hwp : SepWP prog target s1 P (fun sf Pf => VmPreserved s1 sf ∧ rest sf Pf)) :
    SepWP prog target s1 P (fun sf Pf => VmPreserved s0 sf ∧ rest sf Pf) :=
  SepWP.mono hwp fun _ _ _ _ ⟨h1f, hr⟩ => ⟨h01.trans h1f, hr⟩

omit [LibsignalPlacement] in
private theorem vmPreserved_of_same_vm_mem {s s₁ s₂ : State}
    (h : VmPreserved s s₁)
    (hbs : s₂.brkStart = s₁.brkStart)
    (hb : s₂.brk = s₁.brk)
    (htp : s₂.tpidrEl0 = s₁.tpidrEl0)
    (hph : s₂.physMemAvail = s₁.physMemAvail)
    (hm : s₂.mem = s₁.mem)
    (hfs : s₂.fs = s₁.fs) :
    VmPreserved s s₂ :=
  h.trans ⟨⟨hbs, hb, htp⟩, hph, fun _ => by rw [hm], LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩

local syntax "by_vm_open " tacticSeq : tactic
local elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

/-- VM-preserving relocatable `States.from_pb = .ok st0` relocation + jump-table 1 dispatch
    (`+248 -> spqrSendPlacedEntry + statesSendArmOffset st0`):
    relocates `chunkedStatesAt A_rep (sp + 0x1260) st0` to `chunkedStatesAt A_rep (sp + 0x950) st0`
    via `sessionMemcpyRegionBudgetSpec` and dispatches across all 11 `States` variants to
    `spqrSendPlacedEntry + statesSendArmOffset st0`, preserving `VmPreserved s sf`. -/
theorem spqr_send_states_from_pb_ok_to_arm_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {A_rep : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    {s0 s : State} {sp : BitVec 64}
    {v1 : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)} (Frame : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = sp + 0x1260#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + statesSendArmOffset st0) s
      ((resultChunkedStatesAt A_rep (F := F) (sp + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTablePlacedAt) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          (chunkedStatesAt A_rep (sp + 0x950#64) st0 ∗
            memRegion (sp + 0x930#64) 24 ∗
            memRegion (sp + 0x1260#64) 928 ∗
            spqrSendStatesJumpTablePlacedAt) ∗ Frame) ∧
        sf.sp = sp ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = chunkedStatesWord0 st0 ∧
        sf.readReg64 .x21 = sp + 0x1260#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = sp + 0x950#64 ∧
        sf.readReg64 .x25 = sp + 0x550#64 ∧
        sf.readReg64 .x26 = sp + 0x1260#64 ∧
        sf.readReg64 .x28 = sp + 0x1060#64 ∧
        (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)) := by
  rw [hfrom]
  dsimp only [resultChunkedStatesAt]
  have hsplit_ok :
      ((chunkedStatesAt A_rep (sp + 0x1260#64) st0 ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTablePlacedAt) ∗ Frame) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        (((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
         ((sp + 0x1268#64) ↦₆₄ w1) ∗
         ((sp + 0x1270#64) ↦₆₄ w2) ∗
         ((sp + 0x1278#64) ↦₆₄ w3) ∗
         ((sp + 0x1280#64) ↦ₛ bs896) ∗
         relocatedHeap (fun dst => chunkedStatesTail920At A_rep dst st0) bs ∗
         memRegion (sp + 0x930#64) 24 ∗
         memRegion (sp + 0x950#64) 928 ∗
         spqrSendStatesJumpTablePlacedAt ∗ Frame) := by
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_left (chunkedStatesAt_1260_entails_reloc A_rep sp st0))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w1
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w2
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w3
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs896
    refine Entails.sepExists_right bs (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_))))
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hsplit_ok ?_
  apply ProofLib.SepWP.exists_left; intro bs
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro bs896
  refine SepWP.pure_elim fun ⟨hbs, hlen896⟩ => ?_
  wp_conv_pre => rw [memRegion_sp_930_split_24 sp, memRegion_sp_950_split_4words_896 sp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d3_968
  apply ProofLib.SepWP.exists_left; intro d2_960
  apply ProofLib.SepWP.exists_left; intro d1_958
  apply ProofLib.SepWP.exists_left; intro d0_950
  apply ProofLib.SepWP.exists_left; intro s2_940
  apply ProofLib.SepWP.exists_left; intro s1_938
  apply ProofLib.SepWP.exists_left; intro s0_930
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName, spqrSendRoSym,
    BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  refine SepWP.seq
    (mid := lsρ "memcpy")
    (Mid := fun s1 P1 =>
      VmPreserved s s1 ∧
      s1.sp = sp ∧
      s1.readReg64 .x30 = (blkPl_427).base + 308#64 ∧
      s1.readReg64 .x0 = sp + 0x970#64 ∧
      s1.readReg64 .x1 = sp + 0x1280#64 ∧
      s1.readReg64 .x2 = 896#64 ∧
      s1.readReg64 .x19 = s.readReg64 .x19 ∧
      s1.readReg64 .x20 = chunkedStatesWord0 st0 ∧
      s1.readReg64 .x21 = sp + 0x1260#64 ∧
      s1.readReg64 .x22 = s.readReg64 .x22 ∧
      s1.readReg64 .x23 = s.readReg64 .x23 ∧
      s1.readReg64 .x24 = sp + 0x950#64 ∧
      s1.readReg64 .x25 = sp + 0x550#64 ∧
      s1.readReg64 .x26 = sp + 0x1260#64 ∧
      s1.readReg64 .x28 = sp + 0x1060#64 ∧
      s1.readReg64 .x29 = s.readReg64 .x29 ∧
      calleeSavedVRegs s1 = calleeSavedVRegs s ∧
      s1.trace = s0.trace ∧
      (P1 ⊢
        memRegion (sp + 0x970#64) 896 ∗
        ((sp + 0x1280#64) ↦ₛ bs896) ∗
        ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
        ((sp + 0x1268#64) ↦₆₄ w1) ∗
        ((sp + 0x1270#64) ↦₆₄ w2) ∗
        ((sp + 0x1278#64) ↦₆₄ w3) ∗
        relocatedHeap (fun dst => chunkedStatesTail920At A_rep dst st0) bs ∗
        ((sp + 0x930#64) ↦₆₄ w1) ∗
        ((sp + 0x938#64) ↦₆₄ w2) ∗
        ((sp + 0x940#64) ↦₆₄ w3) ∗
        ((sp + 0x950#64) ↦₆₄ d0_950) ∗
        ((sp + 0x958#64) ↦₆₄ d1_958) ∗
        ((sp + 0x960#64) ↦₆₄ d2_960) ∗
        ((sp + 0x968#64) ↦₆₄ d3_968) ∗
        spqrSendStatesJumpTablePlacedAt ∗ Frame))
    ?_ ?_
  · by_vm_steps (
      wp_steps
      refine ProofLib.SepWP.done
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by sep_ac_rfl)⟩)
  · intro s1 P1 hpc1 hrun1
      ⟨hvm1, hsp1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1,
       hx24_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs1, htr1, hP1⟩
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.call_subroutine_frame hmemcpy
      (x := (sp + 0x970#64, sp + 0x1280#64, bs896))
      (F := ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
        ((sp + 0x1268#64) ↦₆₄ w1) ∗
        ((sp + 0x1270#64) ↦₆₄ w2) ∗
        ((sp + 0x1278#64) ↦₆₄ w3) ∗
        relocatedHeap (fun dst => chunkedStatesTail920At A_rep dst st0) bs ∗
        ((sp + 0x930#64) ↦₆₄ w1) ∗
        ((sp + 0x938#64) ↦₆₄ w2) ∗
        ((sp + 0x940#64) ↦₆₄ w3) ∗
        ((sp + 0x950#64) ↦₆₄ d0_950) ∗
        ((sp + 0x958#64) ↦₆₄ d1_958) ∗
        ((sp + 0x960#64) ↦₆₄ d2_960) ∗
        ((sp + 0x968#64) ↦₆₄ d3_968) ∗
        spqrSendStatesJumpTablePlacedAt ∗ Frame)
      (ret_pc := (blkPl_427).base + 308#64)
      hpc1 hrun1
      (by unfold State.spAligned; rw [hsp1]; exact hsp_align)
      hlr1
      ?_
      (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
      (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
      ?_
    · intro R hm
      dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
      rw [hlen896, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *]⟩, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    · intro s2 hpc2 hrun2 hsp2 hcc2
      dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun hvm2 => ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨_, htr2⟩ => ?_
      have hsp2' : s2.sp = sp := hsp2.trans hsp1
      have htr2' : s2.trace = s0.trace := htr2.trans htr1
      have hx19_2 : s2.readReg64 .x19 = s.readReg64 .x19 := hcc2.1.trans hx19_1
      have hx20_2 : s2.readReg64 .x20 = chunkedStatesWord0 st0 := hcc2.2.1.trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = sp + 0x1260#64 := hcc2.2.2.1.trans hx21_1
      have hx22_2 : s2.readReg64 .x22 = s.readReg64 .x22 := hcc2.2.2.2.1.trans hx22_1
      have hx23_2 : s2.readReg64 .x23 = s.readReg64 .x23 := hcc2.2.2.2.2.1.trans hx23_1
      have hx24_2 : s2.readReg64 .x24 = sp + 0x950#64 := hcc2.2.2.2.2.2.1.trans hx24_1
      have hx25_2 : s2.readReg64 .x25 = sp + 0x550#64 := hcc2.2.2.2.2.2.2.1.trans hx25_1
      have hx26_2 : s2.readReg64 .x26 = sp + 0x1260#64 := hcc2.2.2.2.2.2.2.2.1.trans hx26_1
      have hx28_2 : s2.readReg64 .x28 = sp + 0x1060#64 := hcc2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
      have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 :=
        hcc2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1
      have hvregs_2 : calleeSavedVRegs s2 = calleeSavedVRegs s :=
        hcc2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs1
      have hreasm :
          ((sp + 0x970#64) ↦ₛ bs896) ∗
          ((sp + 0x1280#64) ↦ₛ bs896) ∗
          ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
          ((sp + 0x1268#64) ↦₆₄ w1) ∗
          ((sp + 0x1270#64) ↦₆₄ w2) ∗
          ((sp + 0x1278#64) ↦₆₄ w3) ∗
          relocatedHeap (fun dst => chunkedStatesTail920At A_rep dst st0) bs ∗
          ((sp + 0x930#64) ↦₆₄ w1) ∗
          ((sp + 0x938#64) ↦₆₄ w2) ∗
          ((sp + 0x940#64) ↦₆₄ w3) ∗
          ((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
          ((sp + 0x958#64) ↦₆₄ w1) ∗
          ((sp + 0x960#64) ↦₆₄ w2) ∗
          ((sp + 0x968#64) ↦₆₄ w3) ∗
          spqrSendStatesJumpTableWordsAt (lsρ spqrSendRoSym) ∗ Frame ⊢
          (chunkedStatesAt A_rep (sp + 0x950#64) st0 ∗
            memRegion (sp + 0x930#64) 24 ∗
            memRegion (sp + 0x1260#64) 928 ∗
            spqrSendStatesJumpTablePlacedAt) ∗ Frame := by
        rw [← spqrSendStatesJumpTablePlacedAt_eq_words]
        have hst := reassemble_chunkedStatesAt_950 A_rep sp st0 w1 w2 w3 hbs
        have h930 := words3_930_entails_memRegion_24 sp w1 w2 w3
        have h1260 := reassemble_1260_after_memcpy sp (chunkedStatesWord0 st0) w1 w2 w3 hlen896
        have hreord1 :
            ((sp + 0x970#64) ↦ₛ bs896) ∗
            ((sp + 0x1280#64) ↦ₛ bs896) ∗
            ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
            ((sp + 0x1268#64) ↦₆₄ w1) ∗
            ((sp + 0x1270#64) ↦₆₄ w2) ∗
            ((sp + 0x1278#64) ↦₆₄ w3) ∗
            relocatedHeap (fun dst => chunkedStatesTail920At A_rep dst st0) bs ∗
            ((sp + 0x930#64) ↦₆₄ w1) ∗
            ((sp + 0x938#64) ↦₆₄ w2) ∗
            ((sp + 0x940#64) ↦₆₄ w3) ∗
            ((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
            ((sp + 0x958#64) ↦₆₄ w1) ∗
            ((sp + 0x960#64) ↦₆₄ w2) ∗
            ((sp + 0x968#64) ↦₆₄ w3) ∗
            spqrSendStatesJumpTablePlacedAt ∗ Frame =
            ((((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
              ((sp + 0x958#64) ↦₆₄ w1) ∗
              ((sp + 0x960#64) ↦₆₄ w2) ∗
              ((sp + 0x968#64) ↦₆₄ w3) ∗
              ((sp + 0x970#64) ↦ₛ bs896) ∗
              relocatedHeap (fun dst => chunkedStatesTail920At A_rep dst st0) bs) ∗
             (((sp + 0x930#64) ↦₆₄ w1) ∗
              ((sp + 0x938#64) ↦₆₄ w2) ∗
              ((sp + 0x940#64) ↦₆₄ w3)) ∗
             (((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
              ((sp + 0x1268#64) ↦₆₄ w1) ∗
              ((sp + 0x1270#64) ↦₆₄ w2) ∗
              ((sp + 0x1278#64) ↦₆₄ w3) ∗
              ((sp + 0x1280#64) ↦ₛ bs896)) ∗
             spqrSendStatesJumpTablePlacedAt) ∗ Frame := by sep_ac_rfl
        rw [hreord1]
        exact sepConj_mono_left (sepConj_mono hst (sepConj_mono h930 (sepConj_mono_left h1260)))
      wp_conv_pre =>
        rw [spqrSendStatesJumpTablePlacedAt_eq_words]
        dsimp only [spqrSendStatesJumpTableWordsAt, spqrSendRoSym, BitVec.ofNat_eq_ofNat]
      dsimp only [spqrSendStatesJumpTableWordsAt, spqrSendRoSym,
        BitVec.ofNat_eq_ofNat] at hreasm
      have hro_comm (k : BitVec 64) :
          k + lsρ "libsignal_cli_ratchet:.rodata.spqr::send::<libsignal_cli_ratchet::Coins>" =
            lsρ "libsignal_cli_ratchet:.rodata.spqr::send::<libsignal_cli_ratchet::Coins>" + k :=
        BitVec.add_comm k _
      refine SepWP.mono ?_ (fun sf Pf _ _ (h : VmPreserved s2 sf ∧ _) =>
        ⟨(hvm1.trans hvm2).trans h.1, h.2⟩)
      cases st0 with
      | ct1Sampled st =>
        dsimp only [chunkedStatesWord0, statesSendArmOffset,
          BitVec.ofNat_eq_ofNat] at hx20_2 hreasm ⊢
        cases hs : st.sending_ct1.s <;>
          { rw [hs] at hx20_2 hreasm
            dsimp only [polyEncoderTagVal, polyEncoderPointsTag, polyEncoderPolysTag,
              BitVec.ofNat_eq_ofNat] at hx20_2 hreasm ⊢
            apply sepWP_cut_here (mid := (blkPl_427).base + 340#64)
            by_vm_open (
              wp_steps
              refine ProofLib.SepWP.done
                (by simp only [wp_norm, arm64_norm, *])
                (by simp only [wp_norm, arm64_norm, *])
                ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_a => ?_⟩
              wp_steps 1
              apply sepWP_trans_vm
              · refine vmPreserved_of_same_vm_mem hvm_a ?_ ?_ ?_ ?_ ?_ ?_ <;>
                  (generalize s2 = s_tmp; cases s_tmp; rfl)
              · by_vm_steps (
                  wp_steps 16
                  wp_conv_pre => simp only [hro_comm]
                  refine SepWP.weaken_pre (Entails.trans ?_ hreasm) ?_
                  · exact Entails.of_eq (by sep_ac_rfl)
                  · refine ProofLib.SepWP.done
                      (by simp only [wp_norm, arm64_norm, *])
                      (by simp only [wp_norm, arm64_norm, *])
                      ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq rfl,
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, polyEncoderTagVal,
                          polyEncoderPointsTag, polyEncoderPolysTag, *],
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, *],
                        by simp only [wp_norm, arm64_norm, *],
                        ⟨by simp only [wp_norm, arm64_norm, *],
                         by simp only [wp_norm, arm64_norm, *]⟩⟩)) }
      | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _
      | ekSentCt1Received _ | noHeaderReceived _ | headerReceived _
      | ekReceivedCt1Sampled _ | ct1Acknowledged _ | ct2Sampled _ =>
        dsimp only [chunkedStatesWord0, statesSendArmOffset,
          BitVec.ofNat_eq_ofNat] at hx20_2 hreasm ⊢
        apply sepWP_cut_here (mid := (blkPl_427).base + 340#64)
        by_vm_open (
          wp_steps
          refine ProofLib.SepWP.done
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], fun hvm_a => ?_⟩
          wp_steps 1
          apply sepWP_trans_vm
          · refine vmPreserved_of_same_vm_mem hvm_a ?_ ?_ ?_ ?_ ?_ ?_ <;>
              (generalize s2 = s_tmp; cases s_tmp; rfl)
          · by_vm_steps (
              wp_steps 16
              wp_conv_pre => simp only [hro_comm]
              refine SepWP.weaken_pre (Entails.trans ?_ hreasm) ?_
              · exact Entails.of_eq (by sep_ac_rfl)
              · refine ProofLib.SepWP.done
                  (by simp only [wp_norm, arm64_norm, *])
                  (by simp only [wp_norm, arm64_norm, *])
                  ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq rfl,
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    ⟨by simp only [wp_norm, arm64_norm, *],
                     by simp only [wp_norm, arm64_norm, *]⟩⟩))

/-- Pool-threading corollary of `spqr_send_states_from_pb_ok_to_arm_placed`, transporting
    `A.pool lim st s` to `A.pool lim st sf` across `VmPreserved s sf`. -/
theorem spqr_send_states_from_pb_ok_to_arm_placed_pool
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    {s0 s : State} (st : M.σ) {sp : BitVec 64}
    {v1 : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)} (Rest : SepProp)
    (hpc : s.pc = spqrSendPlacedEntry + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = sp + 0x1260#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + statesSendArmOffset st0) s
      ((resultChunkedStatesAt A.repAlloc (F := F) (sp + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTablePlacedAt) ∗ (A.pool lim st s ∗ Rest))
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          (chunkedStatesAt A.repAlloc (sp + 0x950#64) st0 ∗
            memRegion (sp + 0x930#64) 24 ∗
            memRegion (sp + 0x1260#64) 928 ∗
            spqrSendStatesJumpTablePlacedAt) ∗ (A.pool lim st sf ∗ Rest)) ∧
        sf.sp = sp ∧
        sf.trace = s0.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = chunkedStatesWord0 st0 ∧
        sf.readReg64 .x21 = sp + 0x1260#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = sp + 0x950#64 ∧
        sf.readReg64 .x25 = sp + 0x550#64 ∧
        sf.readReg64 .x26 = sp + 0x1260#64 ∧
        sf.readReg64 .x28 = sp + 0x1060#64 ∧
        (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)) := by
  have hok := spqr_send_states_from_pb_ok_to_arm_placed (A_rep := A.repAlloc)
    hA (A.pool lim st s ∗ Rest) hpc hrun hsp hsp_align htrace hx21 hx26 hfrom
  refine SepWP.mono hok ?_
  rintro sf Pf _ _
    ⟨hvm, hPf, hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f,
     hx24_f, hx25_f, hx26_f, hx28_f, hx29_f⟩
  refine ⟨hvm, ?_, hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f,
    hx24_f, hx25_f, hx26_f, hx28_f, hx29_f⟩
  rw [A.pool_transport lim st s sf hvm]
  exact hPf

/-- Continuation-passing wrapper for `spqr_send_states_from_pb_ok_to_arm_placed`
    (`+248 -> spqrSendPlacedEntry + statesSendArmOffset st0`), supplying `VmPreserved s sf`. -/
theorem spqr_send_states_from_pb_ok_step_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {A_rep : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    {s0 s : State} {sp : BitVec 64}
    {v1 : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)} {Frame : SepProp}
    {target_pc : BitVec 64} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = sp + 0x1260#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hnext : ∀ sf : State,
      VmPreserved s sf →
      sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = chunkedStatesWord0 st0 →
      sf.readReg64 .x21 = sp + 0x1260#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 0x950#64 →
      sf.readReg64 .x25 = sp + 0x550#64 →
      sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x28 = sp + 0x1060#64 →
      (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) →
      SepWP (spqrSendPlacedProg ext) target_pc sf
        ((chunkedStatesAt A_rep (sp + 0x950#64) st0 ∗
          memRegion (sp + 0x930#64) 24 ∗
          memRegion (sp + 0x1260#64) 928 ∗
          spqrSendStatesJumpTablePlacedAt) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) target_pc s
      ((resultChunkedStatesAt A_rep (F := F) (sp + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTablePlacedAt) ∗ Frame) post := by
  refine SepWP.seq
    (spqr_send_states_from_pb_ok_to_arm_placed (A_rep := A_rep)
      hA Frame hpc hrun hsp hsp_align htrace hx21 hx26 hfrom) ?_
  rintro sf Pf hpc_f hrun_f
    ⟨hvm, hPf, hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f,
     hx24_f, hx25_f, hx26_f, hx28_f, hx29_f⟩
  exact SepWP.weaken_pre hPf
    (hnext sf hvm hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f
      hx24_f hx25_f hx26_f hx28_f hx29_f)

/-- Pool-threading continuation wrapper for `spqr_send_states_from_pb_ok_step_placed`,
    transporting `A.pool lim st s` to `A.pool lim st sf` inside `hnext`. -/
theorem spqr_send_states_from_pb_ok_step_placed_pool
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    {s0 s : State} {st : M.σ} {sp : BitVec 64}
    {v1 : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)} {Rest : SepProp}
    {target_pc : BitVec 64} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = sp + 0x1260#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hnext : ∀ sf : State,
      VmPreserved s sf →
      sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = chunkedStatesWord0 st0 →
      sf.readReg64 .x21 = sp + 0x1260#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 0x950#64 →
      sf.readReg64 .x25 = sp + 0x550#64 →
      sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x28 = sp + 0x1060#64 →
      (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) →
      SepWP (spqrSendPlacedProg ext) target_pc sf
        ((chunkedStatesAt A.repAlloc (sp + 0x950#64) st0 ∗
          memRegion (sp + 0x930#64) 24 ∗
          memRegion (sp + 0x1260#64) 928 ∗
          spqrSendStatesJumpTablePlacedAt) ∗ (A.pool lim st sf ∗ Rest)) post) :
    SepWP (spqrSendPlacedProg ext) target_pc s
      ((resultChunkedStatesAt A.repAlloc (F := F) (sp + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTablePlacedAt) ∗ (A.pool lim st s ∗ Rest)) post := by
  refine spqr_send_states_from_pb_ok_step_placed (A_rep := A.repAlloc)
    hA hpc hrun hsp hsp_align htrace hx21 hx26 hfrom ?_
  intro sf hvm hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f
    hx24_f hx25_f hx26_f hx28_f hx29_f
  rw [← A.pool_transport lim st s sf hvm]
  exact hnext sf hvm hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx21_f hx22_f hx23_f
    hx24_f hx25_f hx26_f hx28_f hx29_f

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1DispatchPlacedBudget
