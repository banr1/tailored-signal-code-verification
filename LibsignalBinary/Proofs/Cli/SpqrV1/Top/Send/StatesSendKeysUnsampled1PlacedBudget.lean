/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.keysUnsampled` Sub-Steps (`+372..+684`, Block `427`)

Threads `RustCliAllocBudget` through `signal_session_coins_fill`, ML-KEM key generation,
and the 64-byte `hdr`, 1152-byte `ek`, and 2400-byte `dk` allocations (`+372..+684`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8Buf)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes MlKem MlkemFromSeedCall MlkemKpRefCall
   mlkemEncaps1Spec mlkemFromSeedSpec mlkemPk1Spec mlkemPk2Spec pk1Off pk2Off)
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth (AuthenticatorGhost authenticatorPinAt)
open CryptoVerification.SpqrV1.Top.Send
  (authHeapBufs authInlineWordsAt authenticatorPinAt_eq_inline_heap exists_words8_of_len64
   live_pointsTo_entails_vecU8Buf memRegion_48_eq_words6 memRegion_64_eq_words8
   pointsToBytes_2400_expose_pk1 pointsToBytes_2400_expose_pk2 spqrSendCalleeStack
   stackAt_spqrSendCallee_from_allocHook stackAt_spqrSendCallee_from_extHook
   stackAt_spqrSendCallee_to_allocHook stackAt_spqrSendCallee_to_extHook
   words8At words8At_entails_memRegion)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrCoinsAfterPlaced spqrCoinsAtPlaced spqrCoinsAtPlaced_entails_after_zero
   spqrMlkemEncaps1Sym spqrMlkemFromSeedSym spqrMlkemPk1Sym spqrMlkemPk2Sym)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget RustLayoutOk
   VmPreserved fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomSpec
   rustCliDeallocBudgetSpec subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget (seq_vm_lscro)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (spqrCoinsFillAtPlaced_of_after0_cro spqrCoinsFillAtSpecPlaced)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (call_lscro_calleeStack_sepWP of_sepWP_lscro_plain
   spqrSend_allocNoOom_ok_placed spqrSend_alloc_ok_placed spqrSend_dealloc_ok_placed
   spqrSend_handle_error_extern spqrSend_noAllocShim_ok_placed
   spqrSend_session_memcpy_region_ok_placed spqrSend_shim_ok_placed)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
  (call_memcpy_bytes_budget call_rustAllocNoOom_budget call_sessionShim_budget)
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

/-! ## 1. Re-Exports & `withVmPreserved` Hook Extractors on `spqrSendPlacedProg` -/

export CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrMlkemFromSeedSym spqrMlkemPk1Sym spqrMlkemPk2Sym spqrMlkemEncaps1Sym)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (spqrSend_shim_ok_placed spqrSend_noAllocShim_ok_placed spqrSend_alloc_ok_placed
   spqrSend_allocNoOom_ok_placed)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (spqrSend_dealloc_ok_placed spqrSend_session_memcpy_region_ok_placed
   spqrSend_handle_error_extern)

abbrev spqrSend_handle_error_placed := @spqrSend_handle_error_extern

theorem spqrSend_mlkemFromSeed_ok_placed {K : MlKem} {ext : String → Option (State → State)}
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K))) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemFromSeedSym)
      (withVmPreserved (mlkemFromSeedSpec K)) :=
  spqr_hook_ok_of_mem hseed

theorem spqrSend_mlkemPk1_ok_placed {ext : String → Option (State → State)}
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemPk1Sym)
      (withVmPreserved mlkemPk1Spec) :=
  spqr_hook_ok_of_mem hpk1

theorem spqrSend_mlkemPk2_ok_placed {ext : String → Option (State → State)}
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemPk2Sym)
      (withVmPreserved mlkemPk2Spec) :=
  spqr_hook_ok_of_mem hpk2

theorem spqrSend_encapsulate1_ok_placed {K : MlKem} {ext : String → Option (State → State)}
    (henc : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K))) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrMlkemEncaps1Sym)
      (withVmPreserved (mlkemEncaps1Spec K)) :=
  spqr_hook_ok_of_mem henc

/-! ## 2. Exact Allocator Event Sequence & Envelope (`+512 -> +684`) -/

def keysUnsampledAllocEvents : List AllocEvent :=
  rustAllocEvents 64 1 ++ (rustAllocEvents 1152 1 ++ rustAllocEvents 2400 1)

def KeysUnsampledAllocEnv (evs : List AllocEvent) : Prop :=
  evs = keysUnsampledAllocEvents

theorem keysUnsampledAllocEnv_nonempty : ∃ evs, KeysUnsampledAllocEnv evs :=
  ⟨keysUnsampledAllocEvents, rfl⟩

@[simp]
theorem fitsEnv_keysUnsampledAlloc_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st KeysUnsampledAllocEnv ↔ FitsEvents M lim st keysUnsampledAllocEvents :=
  FitsEnv.eq_iff

theorem fitsEvents_keysUnsampledAllocEvents_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (h : FitsEvents M lim st keysUnsampledAllocEvents) :
    FitsEvents M lim st (rustAllocEvents 64 1) ∧
    FitsEvents M lim (M.stepEvents (rustAllocEvents 64 1) st) (rustAllocEvents 1152 1) ∧
    FitsEvents M lim
      (M.stepEvents (rustAllocEvents 1152 1) (M.stepEvents (rustAllocEvents 64 1) st))
      (rustAllocEvents 2400 1) ∧
    M.stepEvents keysUnsampledAllocEvents st =
      M.stepEvents (rustAllocEvents 2400 1)
        (M.stepEvents (rustAllocEvents 1152 1) (M.stepEvents (rustAllocEvents 64 1) st)) := by
  unfold keysUnsampledAllocEvents at h
  rcases (fitsEvents_append M lim _ _ st).mp h with ⟨h64, hrest⟩
  rcases (fitsEvents_append M lim _ _ _).mp hrest with ⟨h1152, h2400⟩
  refine ⟨h64, h1152, h2400, ?_⟩
  unfold keysUnsampledAllocEvents
  rw [M.stepEvents_append, M.stepEvents_append]

/-! ## 3. Private Callee & Register-Frame Helpers -/

private structure CallStateAt (s0 s : State) (sp lr : BitVec 64)
    (v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 : BitVec 64) (sm : State) : Prop where
  sp_eq : sm.sp = sp
  lr_eq : sm.readReg64 (Reg.gpr 30#5) = lr
  tr_eq : sm.trace = s0.trace
  x19_eq : sm.readReg64 (Reg.gpr 19#5) = v19
  x20_eq : sm.readReg64 (Reg.gpr 20#5) = v20
  x21_eq : sm.readReg64 (Reg.gpr 21#5) = v21
  x22_eq : sm.readReg64 (Reg.gpr 22#5) = v22
  x23_eq : sm.readReg64 (Reg.gpr 23#5) = v23
  x24_eq : sm.readReg64 (Reg.gpr 24#5) = v24
  x25_eq : sm.readReg64 (Reg.gpr 25#5) = v25
  x26_eq : sm.readReg64 (Reg.gpr 26#5) = v26
  x27_eq : sm.readReg64 (Reg.gpr 27#5) = v27
  x28_eq : sm.readReg64 (Reg.gpr 28#5) = v28
  vregs_eq : calleeSavedVRegs sm = calleeSavedVRegs s

private theorem CallStateAt.of_cs {s0 s sm sf : State}
    {sp lr v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 : BitVec 64}
    (h : CallStateAt s0 s sp lr v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 sm)
    (hsp : sf.sp = sp) (htr : sf.trace = s0.trace)
    (hcs : CalleeSavedPreserved sm sf) :
    CallStateAt s0 s sp (sf.readReg64 (Reg.gpr 30#5))
      v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 sf := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, _, hv⟩
  exact ⟨hsp, rfl, htr,
    h19.trans h.x19_eq, h20.trans h.x20_eq, h21.trans h.x21_eq, h22.trans h.x22_eq,
    h23.trans h.x23_eq, h24.trans h.x24_eq, h25.trans h.x25_eq, h26.trans h.x26_eq,
    h27.trans h.x27_eq, h28.trans h.x28_eq, hv.trans h.vregs_eq⟩

local macro "close_reg_val" : tactic =>
  `(tactic| (
    simp only [State.sp, Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x8,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      BitVec.add_assoc, wp_norm, arm64_norm, *]))

local macro "mk_call_state" : tactic =>
  `(tactic| refine ⟨by close_reg_val, by close_reg_val, by simp only [wp_norm, arm64_norm, *],
    by close_reg_val, by close_reg_val, by close_reg_val, by close_reg_val,
    by close_reg_val, by close_reg_val, by close_reg_val, by close_reg_val,
    by close_reg_val, by close_reg_val, by simp only [wp_norm, arm64_norm, *]⟩)

private theorem kp_add_pk1Off (sp : BitVec 64) :
    (sp + 4704#64) + BitVec.ofNat 64 pk1Off = sp + 7008#64 := by
  change (sp + 4704#64) + 2304#64 = sp + 7008#64; bv_omega

private theorem kp_add_pk2Off (sp : BitVec 64) :
    (sp + 4704#64) + BitVec.ofNat 64 pk2Off = sp + 5856#64 := by
  change (sp + 4704#64) + 1152#64 = sp + 5856#64; bv_omega

private theorem call_mlkemFromSeed_lscro {K : MlKem} {prog : Program}
    {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved (mlkemFromSeedSpec K)))
    (seedA kpA : BitVec 64) (seed : List.Vector (BitVec 8) 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hvm0 : VmPreserved s0 s)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = seedA) (hx8 : s.readReg64 .x8 = kpA)
    (hsplit : P = ((seedA ↦ₛ seed.toList) ∗ memRegion kpA 2400 ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem → VmPreserved s0 sf →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog tgt sf
        (((seedA ↦ₛ seed.toList) ∗ (kpA ↦ₛ (K.fromSeed seed).2.2.toList) ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp_call) (by sep_focus) ?_
  refine SepWP.call_subroutine_frame hcall
    (x := ({ seedA := seedA, kpA := kpA, seed := seed } : MlkemFromSeedCall))
    (F := memRegion (sp_call - 123008#64) 106624 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, mlkemFromSeedSpec]
    rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx8⟩, by ac_nf at hm ⊢⟩
  · dsimp only [withVmPreserved, mlkemFromSeedSpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm1 => SepWP.pure_elim fun htr1 => ?_
    refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp_call) (by sep_focus) ?_
    exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hcrl1 (hvm0.trans hvm1) hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr1.trans htrace))

private theorem call_mlkemPk1_lscro {prog : Program}
    {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved mlkemPk1Spec))
    (kpA : BitVec 64) (kp : List.Vector (BitVec 8) 2400)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hvm0 : VmPreserved s0 s)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = kpA)
    (hsplit : P = ((kpA ↦ₛ kp.toList) ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem → VmPreserved s0 sf →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = kpA + BitVec.ofNat 64 pk1Off → sf.trace = s0.trace →
      SepWP prog tgt sf (((kpA ↦ₛ kp.toList) ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp_call) (by sep_focus) ?_
  refine SepWP.call_subroutine_frame hcall
    (x := ({ kpA := kpA, kp := kp } : MlkemKpRefCall))
    (F := memRegion (sp_call - 123008#64) 106624 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, mlkemPk1Spec]
    rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨hx0, by ac_nf at hm ⊢⟩
  · dsimp only [withVmPreserved, mlkemPk1Spec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm1 => SepWP.pure_elim fun ⟨hx0_sf, htr1⟩ => ?_
    refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp_call) (by sep_focus) ?_
    exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hcrl1 (hvm0.trans hvm1) hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hx0_sf (htr1.trans htrace))

private theorem call_mlkemPk2_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved mlkemPk2Spec))
    (kpA : BitVec 64) (kp : List.Vector (BitVec 8) 2400) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = kpA)
    (hsplit : P = ((kpA ↦ₛ kp.toList) ∗ A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = kpA + BitVec.ofNat 64 pk2Off → sf.trace = s0.trace →
      SepWP prog tgt sf
        (((kpA ↦ₛ kp.toList) ∗ A.pool lim st sf ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp_call) (by sep_focus) ?_
  refine SepWP.call_subroutine_frame hcall
    (x := ({ kpA := kpA, kp := kp } : MlkemKpRefCall))
    (F := memRegion (sp_call - 123008#64) 106624 ∗ A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, mlkemPk2Spec]
    rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨hx0, by ac_nf at hm ⊢⟩
  · dsimp only [withVmPreserved, mlkemPk2Spec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm1 => SepWP.pure_elim fun ⟨hx0_sf, htr1⟩ => ?_
    rw [← A.pool_of_vmPreserved hvm1]
    refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp_call) (by sep_focus) ?_
    exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hcrl1 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hx0_sf (htr1.trans htrace))

private theorem call_shim_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
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
  exact call_sessionShim_budget hcall st hpc hrun hsp hsp_align hlr htrace hsplit
    fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf =>
      SepWP.done hpc_sf hrun_sf fun hcrl1 => hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf htr_sf

private theorem call_allocNoOom_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
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
      sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 → (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false → sf.trace = s0.trace →
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

private theorem call_memcpy_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
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
  exact call_memcpy_bytes_budget hcall dst src bs st hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
    hsplit fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf =>
      SepWP.done hpc_sf hrun_sf fun hcrl1 => hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf htr_sf

/-! ## 4. Relocatable Sub-Step 1a (`+372 -> +512`, `VmPreserved` & Budget Pool) -/

private theorem fold_keysUnsampled_372_to_512_end
    (RA : RustAlloc) (g : AuthenticatorGhost) (sp : BitVec 64) (auth : Authenticator)
    (epoch : BitVec 64) (seed : List.Vector (BitVec 8) 64)
    (sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 : BitVec 64) :
    authInlineWordsAt g (sp + 7136#64) auth ∗ authHeapBufs RA g auth ∗
    ((sp + 7184#64) ↦₆₄ epoch) ∗ memRegion (sp + 7192#64) 344 ∗
    ((sp + 4192#64) ↦ₛ seed.toList) ∗ memRegion (sp + 4256#64) 440 ∗
    words8At (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ∗
    memRegion (sp + 7600#64) 336 ⊢
    authenticatorPinAt RA g (sp + 7136#64) auth ∗ memRegion (sp + 7184#64) 352 ∗
    memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 7536#64) 400 := by
  rw [authenticatorPinAt_eq_inline_heap RA g (sp + 7136#64) auth,
      ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 7184#64),
      ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by bv_omega) (by decide)]
  have h7184 : ((sp + 7184#64) ↦₆₄ epoch) ⊢ ∃∗ d : BitVec 64, (sp + 7184#64) ↦₆₄ d :=
    Entails.sepExists_right _ (Entails.refl _)
  have h4192 := pointsToBytes_entails_memRegion (sp + 4192#64) seed.toList
  rw [List.Vector.toList_length] at h4192; simp only [sepConj_assoc]
  exact sepConj_mono (Entails.refl _)
    (sepConj_mono (Entails.refl _)
      (sepConj_mono h7184
        (sepConj_mono (Entails.refl _)
          (sepConj_mono h4192
            (sepConj_mono (Entails.refl _)
              (sepConj_mono (words8At_entails_memRegion (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7)
                (Entails.refl _)))))))

set_option maxHeartbeats 1600000 in
theorem step_keysUnsampled_372_to_512_vm_placed
    {K : MlKem} {RA : RustAlloc} {ctl tgt : BitVec 64}
    {ext : String → Option (State → State)}
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch sp cur : BitVec 64)
    (tape : List (BitVec 8)) (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64) (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64)
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64) (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs RA g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
      spqrCoinsAtPlaced ctl cur tape ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      LibsignalCodeRoLoaded lsmpl sf.mem → VmPreserved s sf →
      sf.pc = spqrSendPlacedEntry + 512#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((authenticatorPinAt RA g (sp + 7136#64) auth ∗ memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗ memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ memRegion (sp + 7536#64) 400 ∗
          spqrCoinsAfterPlaced ctl cur tape 64 ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have hrng_call := spqrCoinsFillAtPlaced_of_after0_cro (cur := cur) (rest := tape) hcoinsFill
  have hseed_call := spqrSend_mlkemFromSeed_ok_placed hseed
  have hpk1_call := spqrSend_mlkemPk1_ok_placed hpk1
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hrng_call hseed_call hpk1_call hnext ⊢
  simp only [Reg.x24] at hx24; subst hP
  refine seq_vm_lscro (mid := lsmpl.base 618)
    (P_mid :=
      stackAt sp spqrSendCalleeStack ∗
      (memRegion (sp + 7536#64) 64 ∗ spqrCoinsAfterPlaced 0#64 cur tape 0) ∗
      (authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗
       authHeapBufs RA g auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗
       ((sp + 7184#64) ↦₆₄ epoch) ∗ memRegion (sp + 7192#64) 344 ∗
       memRegion (sp + 4192#64) 64 ∗ memRegion (sp + 4256#64) 440 ∗
       memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7600#64) 336 ∗ Frame))
    (Q := fun sm1 =>
      CallStateAt s0 s sp ((blkPl_427).base + 444#64)
        (s.readReg64 .x19) (s.readReg64 .x20) (s.readReg64 .x21) epoch (s.readReg64 .x23)
        (sp + 2384#64) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sm1 ∧
      sm1.readReg64 .x0 = sp + 7536#64 ∧ (sm1.readReg64 .x1).toNat = 64)
    hcrl ?_ ?_
  · have h4192_sp := ProofLib.memRegion_split' (b := sp + 4192#64) (n := 64) (k := 440) (b' := sp + 4256#64) rfl (by bv_omega) (by decide)
    have h7136_sp := ProofLib.memRegion_split' (b := sp + 7136#64) (n := 48) (k := 352) (b' := sp + 7184#64) rfl (by bv_omega) (by decide)
    have h7184_sp := ProofLib.memRegion_split' (b := sp + 7184#64) (n := 8) (k := 344) (b' := sp + 7192#64) rfl (by bv_omega) (by decide)
    have h7536_sp := ProofLib.memRegion_split' (b := sp + 7536#64) (n := 64) (k := 336) (b' := sp + 7600#64) rfl (by bv_omega) (by decide)
    by_vm_steps (
      wp_conv_pre =>
        rw [h4192_sp, h7136_sp, h7184_sp, ProofLib.memRegion_eight (sp + 7184#64), h7536_sp,
            memRegion_64_eq_words8 (sp + 4192#64), memRegion_48_eq_words6 (sp + 7136#64),
            memRegion_64_eq_words8 (sp + 7536#64)]
        dsimp only [authInlineWordsAt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      iterate 23 (apply SepWP.exists_elim; intro _)
      wp_steps
      refine SepWP.fold (words8At_entails_memRegion (sp + 7536#64) _ _ _ _ _ _ _ _)
        (by dsimp only [words8At]; sep_focus) ?_
      refine SepWP.fold (words8At_entails_memRegion (sp + 4192#64) _ _ _ _ _ _ _ _)
        (by dsimp only [words8At]; sep_focus) ?_
      have hcoins_zero : spqrCoinsAtPlaced ctl cur tape ⊢ spqrCoinsAfterPlaced 0#64 cur tape 0 :=
        spqrCoinsAtPlaced_entails_after_zero 0#64 cur tape
      refine SepWP.fold hcoins_zero (by sep_focus) ?_
      refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *],
          Entails.of_eq (by dsimp only [authInlineWordsAt]; simp (config := { failIfUnchanged := false }) only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl),
          ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *],
           by simp only [Reg.x1, wp_norm, arm64_norm, *]⟩⟩)
  · rintro sm1 hpc_sm1 hrun_sm1 hcrl_sm1 hvm_sm1 ⟨hcs_sm1, hx0_sm1, hx1_sm1⟩
    refine call_lscro_calleeStack_sepWP (x := (sp + 7536#64, 64))
      sp spqrSendCalleeStack (by decide)
      (T_pre := memRegion (sp + 7536#64) 64 ∗ spqrCoinsAfterPlaced 0#64 cur tape 0)
      (T_post := fun sf =>
        ⌜sf.trace = sm1.trace⌝ ∗
        ((sp + 7536#64) ↦ₛ (tape ++ List.replicate 64 0#8).take 64) ∗
        spqrCoinsAfterPlaced 0#64 cur tape (min 64 tape.length))
      (F := authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗
        authHeapBufs RA g auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗
        ((sp + 7184#64) ↦₆₄ epoch) ∗ memRegion (sp + 7192#64) 344 ∗
        memRegion (sp + 4192#64) 64 ∗ memRegion (sp + 4256#64) 440 ∗
        memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7600#64) 336 ∗ Frame)
      (φ_pre := sm1.readReg64 .x0 = sp + 7536#64 ∧ (sm1.readReg64 .x1).toNat = 64)
      (φ_post := fun sf => VmPreserved sm1 sf)
      hrng_call hcrl_sm1 hpc_sm1 hrun_sm1 hcs_sm1.sp_eq hsp_align
      (ret_pc := (blkPl_427).base + 444#64) hcs_sm1.lr_eq
      (by dsimp only [spqrCoinsFillAtSpecPlaced, CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillAtSpecPlaced, withVmPreserved]; sep_ac_rfl)
      ⟨hx0_sm1, hx1_sm1⟩ (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => Entails.refl _)
      (by intro sf; dsimp only [spqrCoinsFillAtSpecPlaced, CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillAtSpecPlaced, withVmPreserved]; sep_ac_rfl) ?_
    intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 hvm_sm2 hcrl_sm2
      hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28]
      at hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2
    rcases hcs_sm1 with ⟨_, _, htr_sm1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hv_1⟩
    rw [hx19_1] at hx19_sm2; rw [hx20_1] at hx20_sm2; rw [hx21_1] at hx21_sm2; rw [hx22_1] at hx22_sm2
    rw [hx23_1] at hx23_sm2; rw [hx24_1] at hx24_sm2; rw [hx25_1] at hx25_sm2; rw [hx26_1] at hx26_sm2
    rw [hx27_1] at hx27_sm2; rw [hx28_1] at hx28_sm2; rw [hv_1] at hvregs_sm2
    have hcoins_after_ctl : spqrCoinsAfterPlaced 0#64 cur tape 64 = spqrCoinsAfterPlaced ctl cur tape 64 := rfl
    rw [List.take_append_of_le_length h64, Nat.min_eq_left h64, hcoins_after_ctl, ← hseed_val]
    have hpure_tr :
        ((stackAt sp spqrSendCalleeStack ∗
          (⌜sm2.trace = sm1.trace⌝ ∗ ((sp + 7536#64) ↦ₛ seed.toList) ∗
            spqrCoinsAfterPlaced ctl cur tape 64)) ∗
          (authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗
           authHeapBufs RA g auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗
           ((sp + 7184#64) ↦₆₄ epoch) ∗ memRegion (sp + 7192#64) 344 ∗
           memRegion (sp + 4192#64) 64 ∗ memRegion (sp + 4256#64) 440 ∗
           memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7600#64) 336 ∗ Frame)) =
        ⌜sm2.trace = sm1.trace⌝ ∗
          (stackAt sp spqrSendCalleeStack ∗ ((sp + 7536#64) ↦ₛ seed.toList) ∗
           spqrCoinsAfterPlaced ctl cur tape 64 ∗
           authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗
           authHeapBufs RA g auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗
           ((sp + 7184#64) ↦₆₄ epoch) ∗ memRegion (sp + 7192#64) 344 ∗
           memRegion (sp + 4192#64) 64 ∗ memRegion (sp + 4256#64) 440 ∗
           memRegion (sp + 4704#64) 2400 ∗ memRegion (sp + 7600#64) 336 ∗ Frame) := by sep_ac_rfl
    rw [hpure_tr]
    refine SepWP.pure_elim fun htr_sm2_raw => ?_
    have htr_sm2 : sm2.trace = s0.trace := htr_sm2_raw.trans htr_sm1
    obtain ⟨sw0, sw1, sw2, sw3, sw4, sw5, sw6, sw7, hseed_words⟩ :=
      exists_words8_of_len64 seed.toList (List.Vector.toList_length seed)
    have hfold_seed_4192 :
        words8At (sp + 4192#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ⊢ ((sp + 4192#64) ↦ₛ seed.toList) := by
      rw [hseed_words (sp + 4192#64)]; exact Entails.refl _
    refine seq_vm_lscro (mid := lsρ spqrMlkemFromSeedSym)
      (P_mid :=
        (((sp + 4192#64) ↦ₛ seed.toList) ∗ memRegion (sp + 4704#64) 2400 ∗
          stackAt sp spqrSendCalleeStack) ∗
        (words8At (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ∗
         spqrCoinsAfterPlaced ctl cur tape 64 ∗
         authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗
         authHeapBufs RA g auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗
         ((sp + 7184#64) ↦₆₄ epoch) ∗ memRegion (sp + 7192#64) 344 ∗
         memRegion (sp + 4256#64) 440 ∗ memRegion (sp + 7600#64) 336 ∗ Frame))
      (Q := fun sm3 =>
        CallStateAt s0 s sp ((blkPl_427).base + 496#64)
          (s.readReg64 .x19) (s.readReg64 .x20) (s.readReg64 .x21) epoch (s.readReg64 .x23)
          (sp + 2384#64) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sm3 ∧
        sm3.readReg64 .x0 = sp + 4192#64 ∧ sm3.readReg64 .x8 = sp + 4704#64)
      hcrl_sm2 ?_ ?_
    · rw [hseed_words (sp + 7536#64), memRegion_64_eq_words8 (sp + 4192#64)]
      by_vm_steps (
        dsimp only [words8At]; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        iterate 8 (apply SepWP.exists_elim; intro _)
        wp_steps
        refine SepWP.fold hfold_seed_4192 (by dsimp only [words8At]; sep_focus) ?_
        refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *],
            Entails.of_eq (by simp (config := { failIfUnchanged := false }) only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl),
            ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *],
             by simp only [Reg.x8, wp_norm, arm64_norm, *]⟩⟩)
    · rintro sm3 hpc_sm3 hrun_sm3 hcrl_sm3 hvm_sm3 ⟨hcs_sm3, hx0_sm3, hx8_sm3⟩
      refine call_mlkemFromSeed_lscro hseed_call (sp + 4192#64) (sp + 4704#64) seed
        hcrl_sm3 ((hvm_sm1.trans hvm_sm2).trans hvm_sm3) hpc_sm3 hrun_sm3 hcs_sm3.sp_eq hsp_align
        hcs_sm3.lr_eq (hcs_sm3.tr_eq.trans htrace.symm) hx0_sm3 hx8_sm3 rfl
        fun sm4 hcrl_sm4 hvm_sm4 hpc_sm4 hrun_sm4 hsp_sm4 hcs_sm4 htr_sm4 => ?_
      rcases hcs_sm3.of_cs hsp_sm4 (htr_sm4.trans htrace) hcs_sm4 with
        ⟨hsp_m4, hlr_m4, htr_m4, hx19_m4, hx20_m4, hx21_m4, hx22_m4, hx23_m4, hx24_m4, hx25_m4, hx26_m4, hx27_m4, hx28_m4, hv_m4⟩
      refine seq_vm_lscro (mid := lsρ spqrMlkemPk1Sym)
        (P_mid :=
          (((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ stackAt sp spqrSendCalleeStack) ∗
          (((sp + 4192#64) ↦ₛ seed.toList) ∗
           words8At (sp + 7536#64) sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7 ∗
           spqrCoinsAfterPlaced ctl cur tape 64 ∗
           authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗
           authHeapBufs RA g auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗
           ((sp + 7184#64) ↦₆₄ epoch) ∗ memRegion (sp + 7192#64) 344 ∗
           memRegion (sp + 4256#64) 440 ∗ memRegion (sp + 7600#64) 336 ∗ Frame))
        (Q := fun sm5 =>
          CallStateAt s0 s sp ((blkPl_427).base + 508#64)
            (s.readReg64 .x19) (s.readReg64 .x20) (s.readReg64 .x21) epoch (s.readReg64 .x23)
            (sp + 2384#64) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sm5 ∧
          sm5.readReg64 .x0 = sp + 4704#64)
        hcrl_sm4 ?_ ?_
      · by_vm_steps (
          wp_steps
          refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
              ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *]⟩⟩)
      · rintro sm5 hpc_sm5 hrun_sm5 hcrl_sm5 hvm_sm5 ⟨hcs_sm5, hx0_sm5⟩
        refine call_mlkemPk1_lscro hpk1_call (sp + 4704#64) (K.fromSeed seed).2.2
          hcrl_sm5 (hvm_sm4.trans hvm_sm5) hpc_sm5 hrun_sm5 hcs_sm5.sp_eq hsp_align
          hcs_sm5.lr_eq (hcs_sm5.tr_eq.trans htrace.symm) hx0_sm5 rfl
          fun sm6 hcrl_sm6 hvm_sm6 hpc_sm6 hrun_sm6 hsp_sm6 hcs_sm6 hx0_sm6 htr_sm6 => ?_
        rw [kp_add_pk1Off sp] at hx0_sm6; simp only [Reg.x0] at hx0_sm6
        rcases hcs_sm5.of_cs hsp_sm6 (htr_sm6.trans htrace) hcs_sm6 with
          ⟨hsp_m6, hlr_m6, htr_m6, hx19_m6, hx20_m6, hx21_m6, hx22_m6, hx23_m6, hx24_m6, hx25_m6, hx26_m6, hx27_m6, hx28_m6, hv_m6⟩
        have hfold_end := fold_keysUnsampled_372_to_512_end RA g sp auth epoch seed sw0 sw1 sw2 sw3 sw4 sw5 sw6 sw7
        refine seq_vm_lscro (mid := (blkPl_427).base + 512#64)
          (P_mid :=
            (authenticatorPinAt RA g (sp + 7136#64) auth ∗ memRegion (sp + 7184#64) 352 ∗
             authInlineWordsAt g (sp + 2392#64) auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗
             ((sp + 4056#64) ↦₆₄ epoch) ∗ memRegion (sp + 4192#64) 504 ∗
             ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ memRegion (sp + 7536#64) 400 ∗
             spqrCoinsAfterPlaced ctl cur tape 64 ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
          (Q := fun sf =>
            sf.sp = sp ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
            sf.readReg64 .x21 = sp + 7008#64 ∧ sf.readReg64 .x22 = epoch ∧
            sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = sp + 2384#64 ∧
            sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
            sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
          hcrl_sm6 ?_ ?_
        · by_vm_steps (
            wp_steps
            refine SepWP.fold hfold_end (by dsimp only [authInlineWordsAt, words8At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
            refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
              ⟨by simp only [wp_norm, arm64_norm, *],
                Entails.of_eq (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl),
                ⟨by simp only [State.sp, BitVec.add_assoc, wp_norm, arm64_norm, *],
                 by simp only [Reg.x19, BitVec.add_assoc, wp_norm, arm64_norm, *],
                 by simp only [Reg.x21, BitVec.add_assoc, wp_norm, arm64_norm, *],
                 by simp only [Reg.x22, BitVec.add_assoc, wp_norm, arm64_norm, *],
                 by simp only [Reg.x23, BitVec.add_assoc, wp_norm, arm64_norm, *],
                 by simp only [Reg.x24, BitVec.add_assoc, wp_norm, arm64_norm, *],
                 by simp only [Reg.x26, BitVec.add_assoc, wp_norm, arm64_norm, *],
                 by simp only [Reg.x28, BitVec.add_assoc, wp_norm, arm64_norm, *],
                 by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩⟩)
        · rintro sf hpc_sf hrun_sf hcrl_sf hvm_sf
            ⟨hsp_sf, hx19_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf, hx26_sf, hx28_sf, htr_sf, hvregs_sf⟩
          exact hnext sf hcrl_sf (hvm_sm6.trans hvm_sf) hpc_sf hrun_sf hsp_sf
            hx19_sf hx21_sf hx22_sf hx23_sf hx24_sf hx26_sf hx28_sf htr_sf hvregs_sf

theorem step_keysUnsampled_372_to_512_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ctl tgt : BitVec 64}
    {ext : String → Option (State → State)}
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (withVmPreserved (mlkemFromSeedSpec K)))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym (withVmPreserved mlkemPk1Spec))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch sp cur : BitVec 64)
    (tape : List (BitVec 8)) (h64 : 64 ≤ tape.length)
    (seed : List.Vector (BitVec 8) 64) (hseed_val : seed.toList = tape.take 64)
    (d4056 : BitVec 64) (st : M.σ)
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 372#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64) (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗ authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ epoch) ∗ ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 504 ∗ memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400 ∗
      spqrCoinsAtPlaced ctl cur tape ∗ A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State,
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 512#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x21 = sp + 7008#64 →
      sf.readReg64 .x22 = epoch → sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 2384#64 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x28 = s.readReg64 .x28 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗ memRegion (sp + 7184#64) 352 ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗ ((sp + 2440#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗ memRegion (sp + 4192#64) 504 ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ memRegion (sp + 7536#64) 400 ∗
          spqrCoinsAfterPlaced ctl cur tape 64 ∗ A.pool lim st sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  subst hP
  refine step_keysUnsampled_372_to_512_vm_placed hcoinsFill hseed hpk1
    g auth epoch sp cur tape h64 seed hseed_val d4056
    (Frame := A.pool lim st s ∗ Frame)
    hcrl hsp_align hpc hrun hsp hx24 htrace (by sep_ac_rfl)
    fun sf hcrl_sf hvm_sf hpc_sf hrun_sf hsp_sf
      hx19_sf hx21_sf hx22_sf hx23_sf hx24_sf hx26_sf hx28_sf htr_sf hvregs_sf => ?_
  rw [← A.pool_of_vmPreserved hvm_sf]
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext sf hcrl_sf hpc_sf hrun_sf hsp_sf
      hx19_sf hx21_sf hx22_sf hx23_sf hx24_sf hx26_sf hx28_sf htr_sf hvregs_sf)

/-! ## 5. Budget-Threaded Relocatable Sub-Step 1b (`+512 -> +684`) -/

set_option maxHeartbeats 1600000 in
theorem step_keysUnsampled_512_to_684_sepWP_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (sp epoch : BitVec 64) (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    (st : M.σ) (hfit : FitsEnv M lim st KeysUnsampledAllocEnv)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 512#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 7008#64) (hx22 : s.readReg64 .x22 = epoch)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
      A.pool lim st s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr ek_ptr dk_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      hdr_ptr ≠ 0 → (hdr_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 684#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x0 = sp + 7136#64 → sf.readReg64 .x1 = epoch →
      sf.readReg64 .x2 = hdr_ptr → sf.readReg64 .x3 = 64#64 →
      sf.readReg64 .x8 = sp + 4832#64 → sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = hdr_ptr → sf.readReg64 .x21 = ek_ptr →
      sf.readReg64 .x22 = epoch → sf.readReg64 .x23 = dk_ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = 2400#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 → sf.readReg64 .x27 = 64#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) ret sf
        ((A.live hdr_ptr 64 1 ∗ (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          memRegion (sp + 4704#64) 2400 ∗
          A.pool lim (M.stepEvents keysUnsampledAllocEvents st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) ret s P post := by
  have hshim := spqrSend_shim_ok_placed hA
  have halloc := spqrSend_allocNoOom_ok_placed hA
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hpk2_call := spqrSend_mlkemPk2_ok_placed hpk2
  have hek_len : (K.fromSeed seed).2.1.toList.length = 1152 := List.Vector.toList_length _
  have hdk_len : (K.fromSeed seed).2.2.toList.length = 2400 := List.Vector.toList_length _
  rcases fitsEvents_keysUnsampledAllocEvents_split (fitsEnv_keysUnsampledAlloc_iff.mp hfit) with
    ⟨hfit64, hfit1152, hfit2400, hstep_all⟩
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hshim halloc hmemcpy hpk2_call hnext ⊢
  simp only [Reg.x21, Reg.x22] at hx21 hx22; subst hP
  refine seq_vm_lscro (mid := lsρ spqrRustNoAllocShimSym)
    (P_mid := A.pool lim st s ∗ (((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ stackAt sp spqrSendCalleeStack ∗ Frame))
    (Q := fun sa0 =>
      CallStateAt s0 s sp ((blkPl_427).base + 516#64)
        (s.readReg64 .x19) (s.readReg64 .x20) (sp + 7008#64) epoch (s.readReg64 .x23)
        (s.readReg64 .x24) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sa0)
    hcrl ?_ ?_
  · by_vm_steps (
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl), by mk_call_state⟩)
  · rintro sa0 hpc_a0 hrun_a0 hcrl_a0 hvm_a0 hcs_a0
    rw [← A.pool_of_vmPreserved hvm_a0]
    refine call_shim_lscro hshim st hcrl_a0 hpc_a0 hrun_a0 hcs_a0.sp_eq hsp_align hcs_a0.lr_eq hcs_a0.tr_eq rfl
      fun sa1 hcrl_a1 hpc_a1 hrun_a1 hsp_a1 hcs_a1 htr_a1 => ?_
    rcases hcs_a0.of_cs hsp_a1 htr_a1 hcs_a1 with
      ⟨hsp_a1', hlr_a1, htr_a1', hx19_a1, hx20_a1, hx21_a1, hx22_a1, hx23_a1, hx24_a1, hx25_a1, hx26_a1, hx27_a1, hx28_a1, hv_a1⟩
    refine seq_vm_lscro (mid := lsρ spqrRustAllocSym)
      (P_mid := (A.pool lim st sa1 ∗ stackAt sp spqrSendCalleeStack) ∗
        (((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ Frame))
      (Q := fun sa2 =>
        CallStateAt s0 s sp ((blkPl_427).base + 528#64)
          (s.readReg64 .x19) (s.readReg64 .x20) (sp + 7008#64) epoch (s.readReg64 .x23)
          (s.readReg64 .x24) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sa2 ∧
        (sa2.readReg64 .x0).toNat = 64 ∧ (sa2.readReg64 .x1).toNat = 1) hcrl_a1 ?_ ?_
    · by_vm_steps (
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
            ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *], by simp only [Reg.x1, wp_norm, arm64_norm, *]⟩⟩)
    · rintro sa2 hpc_a2 hrun_a2 hcrl_a2 hvm_a2 ⟨hcs_a2, hx0_a2, hx1_a2⟩
      rw [← A.pool_of_vmPreserved hvm_a2]
      refine call_allocNoOom_lscro halloc 64 st ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit64
        hcrl_a2 hpc_a2 hrun_a2 hcs_a2.sp_eq hsp_align hcs_a2.lr_eq hcs_a2.tr_eq hx0_a2 hx1_a2 rfl
        fun sf1 hcrl_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_
      rcases hcs_a2.of_cs hsp1 htr_ok1 hcs1 with
        ⟨hsp_f1, hlr_f1, htr_f1, hx19_f1, hx20_f1, hx21_f1, hx22_f1, hx23_f1, hx24_f1, hx25_f1, hx26_f1, hx27_f1, hx28_f1, hv_f1⟩
      let st1 := M.stepEvents (rustAllocEvents 64 1) st
      obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hpk1_words⟩ :=
        exists_words8_of_len64 (K.fromSeed seed).1.toList (List.Vector.toList_length _)
      have hfold_pk1 :
          words8At (sf1.readReg64 (Reg.gpr 0#5)) hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ∗
          words8At (sp + 7008#64) hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 ∗
          (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 2304)) ∗
           ((sp + 7072#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 2304).drop 64))) ⊢
          ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗
          ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) := by
        rw [← hpk1_words (sf1.readReg64 (Reg.gpr 0#5)), ← hpk1_words (sp + 7008#64),
            pointsToBytes_2400_expose_pk1 sp seed hpk1_slice]
        exact Entails.of_eq (by sep_ac_rfl)
      refine seq_vm_lscro (mid := lsρ spqrMlkemPk2Sym)
        (P_mid := (((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ A.pool lim st1 sf1 ∗ stackAt sp spqrSendCalleeStack) ∗
          (A.live (sf1.readReg64 (Reg.gpr 0#5)) 64 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗ Frame))
        (Q := fun sb0 =>
          CallStateAt s0 s sp ((blkPl_427).base + 564#64)
            (s.readReg64 .x19) (sf1.readReg64 (Reg.gpr 0#5)) (sp + 7008#64) epoch (s.readReg64 .x23)
            (s.readReg64 .x24) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sb0 ∧
          sb0.readReg64 .x0 = sp + 4704#64) hcrl_ok1 ?_ ?_
      · by_vm_steps (
          wp_conv_pre =>
            rw [pointsToBytes_2400_expose_pk1 sp seed hpk1_slice, hpk1_words (sp + 7008#64),
                memRegion_64_eq_words8 (sf1.readReg64 (Reg.gpr 0#5))]
            dsimp only [words8At]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          iterate 8 (apply SepWP.exists_elim; intro _)
          wp_steps
          refine SepWP.fold hfold_pk1 (by dsimp only [words8At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
          refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
              ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *]⟩⟩)
      · rintro sb0 hpc_b0 hrun_b0 hcrl_b0 hvm_b0 ⟨hcs_b0, hx0_b0⟩
        rw [← A.pool_of_vmPreserved hvm_b0]
        refine call_mlkemPk2_lscro hpk2_call (sp + 4704#64) (K.fromSeed seed).2.2 st1
          hcrl_b0 hpc_b0 hrun_b0 hcs_b0.sp_eq hsp_align hcs_b0.lr_eq hcs_b0.tr_eq hx0_b0 rfl
          fun sb1 hcrl_b1 hpc_b1 hrun_b1 hsp_b1 hcs_b1 hx0_b1 htr_b1 => ?_
        rw [kp_add_pk2Off sp] at hx0_b1; simp only [Reg.x0] at hx0_b1
        rcases hcs_b0.of_cs hsp_b1 htr_b1 hcs_b1 with
          ⟨hsp_b1', hlr_b1, htr_b1', hx19_b1, hx20_b1, hx21_b1, hx22_b1, hx23_b1, hx24_b1, hx25_b1, hx26_b1, hx27_b1, hx28_b1, hv_b1⟩
        refine seq_vm_lscro (mid := lsρ spqrRustNoAllocShimSym)
          (P_mid := A.pool lim st1 sb1 ∗ (((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ stackAt sp spqrSendCalleeStack ∗
            A.live (sf1.readReg64 (Reg.gpr 0#5)) 64 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗ Frame))
          (Q := fun sb2 =>
            CallStateAt s0 s sp ((blkPl_427).base + 572#64)
              (s.readReg64 .x19) (sf1.readReg64 (Reg.gpr 0#5)) (sp + 7008#64) epoch (sp + 5856#64)
              (s.readReg64 .x24) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sb2)
          hcrl_b1 ?_ ?_
        · by_vm_steps (
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
              ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl), by mk_call_state⟩)
        · rintro sb2 hpc_b2 hrun_b2 hcrl_b2 hvm_b2 hcs_b2
          rw [← A.pool_of_vmPreserved hvm_b2]
          refine call_shim_lscro hshim st1 hcrl_b2 hpc_b2 hrun_b2 hcs_b2.sp_eq hsp_align hcs_b2.lr_eq hcs_b2.tr_eq rfl
            fun sb3 hcrl_b3 hpc_b3 hrun_b3 hsp_b3 hcs_b3 htr_b3 => ?_
          rcases hcs_b2.of_cs hsp_b3 htr_b3 hcs_b3 with
            ⟨hsp_b3', hlr_b3, htr_b3', hx19_b3, hx20_b3, hx21_b3, hx22_b3, hx23_b3, hx24_b3, hx25_b3, hx26_b3, hx27_b3, hx28_b3, hv_b3⟩
          refine seq_vm_lscro (mid := lsρ spqrRustAllocSym)
            (P_mid := (A.pool lim st1 sb3 ∗ stackAt sp spqrSendCalleeStack) ∗
              (((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
               A.live (sf1.readReg64 (Reg.gpr 0#5)) 64 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗ Frame))
            (Q := fun sb4 =>
              CallStateAt s0 s sp ((blkPl_427).base + 584#64)
                (s.readReg64 .x19) (sf1.readReg64 (Reg.gpr 0#5)) (sp + 7008#64) epoch (sp + 5856#64)
                (s.readReg64 .x24) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sb4 ∧
              (sb4.readReg64 .x0).toNat = 1152 ∧ (sb4.readReg64 .x1).toNat = 1) hcrl_b3 ?_ ?_
          · by_vm_steps (
              wp_steps
              refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
                ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
                  ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *], by simp only [Reg.x1, wp_norm, arm64_norm, *]⟩⟩)
          · rintro sb4 hpc_b4 hrun_b4 hcrl_b4 hvm_b4 ⟨hcs_b4, hx0_b4, hx1_b4⟩
            rw [← A.pool_of_vmPreserved hvm_b4]
            refine call_allocNoOom_lscro halloc 1152 st1 ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit1152
              hcrl_b4 hpc_b4 hrun_b4 hcs_b4.sp_eq hsp_align hcs_b4.lr_eq hcs_b4.tr_eq hx0_b4 hx1_b4 rfl
              fun sf2 hcrl_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_
            rcases hcs_b4.of_cs hsp2 htr_ok2 hcs2 with
              ⟨hsp_f2, hlr_f2, htr_f2, hx19_f2, hx20_f2, hx21_f2, hx22_f2, hx23_f2, hx24_f2, hx25_f2, hx26_f2, hx27_f2, hx28_f2, hv_f2⟩
            let st2 := M.stepEvents (rustAllocEvents 1152 1) st1
            have hek_mem : memRegion (sf2.readReg64 (Reg.gpr 0#5)) 1152 =
                memRegion (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList.length := by rw [hek_len]
            refine seq_vm_lscro (mid := lsρ "memcpy")
              (P_mid := (memRegion (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList.length ∗
                ((sp + 5856#64) ↦ₛ (K.fromSeed seed).2.1.toList) ∗ A.pool lim st2 sf2) ∗
                (A.live (sf2.readReg64 (Reg.gpr 0#5)) 1152 1 ∗
                 (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 1152)) ∗
                  ((sp + 7008#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 1152).drop 1152))) ∗
                 stackAt sp spqrSendCalleeStack ∗ A.live (sf1.readReg64 (Reg.gpr 0#5)) 64 1 ∗
                 ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗ Frame))
              (Q := fun sc0 =>
                CallStateAt s0 s sp ((blkPl_427).base + 604#64)
                  (s.readReg64 .x19) (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) epoch (sp + 5856#64)
                  (s.readReg64 .x24) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sc0 ∧
                sc0.readReg64 .x0 = sf2.readReg64 (Reg.gpr 0#5) ∧ sc0.readReg64 .x1 = sp + 5856#64 ∧
                (sc0.readReg64 .x2).toNat = (K.fromSeed seed).2.1.toList.length) hcrl_ok2 ?_ ?_
            · rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, hek_mem]
              by_vm_steps (
                wp_steps
                refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
                  ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
                    ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *],
                     by simp only [Reg.x1, wp_norm, arm64_norm, *],
                     by rw [hek_len]; simp only [Reg.x2, wp_norm, arm64_norm, *]⟩⟩)
            · rintro sc0 hpc_c0 hrun_c0 hcrl_c0 hvm_c0 ⟨hcs_c0, hx0_c0, hx1_c0, hx2_c0⟩
              rw [← A.pool_of_vmPreserved hvm_c0]
              refine call_memcpy_lscro hmemcpy (sf2.readReg64 (Reg.gpr 0#5)) (sp + 5856#64)
                (K.fromSeed seed).2.1.toList st2
                hcrl_c0 hpc_c0 hrun_c0 hcs_c0.sp_eq hsp_align hcs_c0.lr_eq hcs_c0.tr_eq hx0_c0 hx1_c0 hx2_c0 rfl
                fun sc1 hcrl_c1 hpc_c1 hrun_c1 hsp_c1 hcs_c1 htr_c1 => ?_
              rcases hcs_c0.of_cs hsp_c1 htr_c1 hcs_c1 with
                ⟨hsp_c1', hlr_c1, htr_c1', hx19_c1, hx20_c1, hx21_c1, hx22_c1, hx23_c1, hx24_c1, hx25_c1, hx26_c1, hx27_c1, hx28_c1, hv_c1⟩
              have hfold_ek :
                  A.live (sf2.readReg64 (Reg.gpr 0#5)) 1152 1 ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
                  ((sp + 5856#64) ↦ₛ (K.fromSeed seed).2.1.toList) ∗
                  (((sp + 4704#64) ↦ₛ ((K.fromSeed seed).2.2.toList.take 1152)) ∗
                   ((sp + 7008#64) ↦ₛ (((K.fromSeed seed).2.2.toList.drop 1152).drop 1152))) ⊢
                  vecU8Buf A.repAlloc 1152#64 (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList ∗
                  ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) := by
                rw [pointsToBytes_2400_expose_pk2 sp seed hpk2_slice, ← sepConj_assoc]
                exact sepConj_mono
                  (live_pointsTo_entails_vecU8Buf (A := A.repAlloc) (sf2.readReg64 (Reg.gpr 0#5))
                    (K.fromSeed seed).2.1.toList 1152 hek_len (by decide) (by decide) hne0_2)
                  (Entails.refl _)
              refine SepWP.fold hfold_ek (by sep_focus) ?_
              refine seq_vm_lscro (mid := lsρ spqrRustNoAllocShimSym)
                (P_mid := A.pool lim st2 sc1 ∗
                  (vecU8Buf A.repAlloc 1152#64 (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList ∗
                   ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ stackAt sp spqrSendCalleeStack ∗
                   A.live (sf1.readReg64 (Reg.gpr 0#5)) 64 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗ Frame))
                (Q := fun sc2 =>
                  CallStateAt s0 s sp ((blkPl_427).base + 608#64)
                    (s.readReg64 .x19) (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) epoch (sp + 5856#64)
                    (s.readReg64 .x24) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sc2)
                hcrl_c1 ?_ ?_
              · by_vm_steps (
                  wp_steps
                  refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
                    ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl), by mk_call_state⟩)
              · rintro sc2 hpc_c2 hrun_c2 hcrl_c2 hvm_c2 hcs_c2
                rw [← A.pool_of_vmPreserved hvm_c2]
                refine call_shim_lscro hshim st2 hcrl_c2 hpc_c2 hrun_c2 hcs_c2.sp_eq hsp_align hcs_c2.lr_eq hcs_c2.tr_eq rfl
                  fun sc3 hcrl_c3 hpc_c3 hrun_c3 hsp_c3 hcs_c3 htr_c3 => ?_
                rcases hcs_c2.of_cs hsp_c3 htr_c3 hcs_c3 with
                  ⟨hsp_c3', hlr_c3, htr_c3', hx19_c3, hx20_c3, hx21_c3, hx22_c3, hx23_c3, hx24_c3, hx25_c3, hx26_c3, hx27_c3, hx28_c3, hv_c3⟩
                refine seq_vm_lscro (mid := lsρ spqrRustAllocSym)
                  (P_mid := (A.pool lim st2 sc3 ∗ stackAt sp spqrSendCalleeStack) ∗
                    (vecU8Buf A.repAlloc 1152#64 (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList ∗
                     ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
                     A.live (sf1.readReg64 (Reg.gpr 0#5)) 64 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗ Frame))
                  (Q := fun sc4 =>
                    CallStateAt s0 s sp ((blkPl_427).base + 620#64)
                      (s.readReg64 .x19) (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) epoch (sp + 5856#64)
                      (s.readReg64 .x24) (s.readReg64 .x25) (s.readReg64 .x26) (s.readReg64 .x27) (s.readReg64 .x28) sc4 ∧
                    (sc4.readReg64 .x0).toNat = 2400 ∧ (sc4.readReg64 .x1).toNat = 1) hcrl_c3 ?_ ?_
                · by_vm_steps (
                    wp_steps
                    refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
                      ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
                        ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *], by simp only [Reg.x1, wp_norm, arm64_norm, *]⟩⟩)
                · rintro sc4 hpc_c4 hrun_c4 hcrl_c4 hvm_c4 ⟨hcs_c4, hx0_c4, hx1_c4⟩
                  rw [← A.pool_of_vmPreserved hvm_c4]
                  refine call_allocNoOom_lscro halloc 2400 st2 ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit2400
                    hcrl_c4 hpc_c4 hrun_c4 hcs_c4.sp_eq hsp_align hcs_c4.lr_eq hcs_c4.tr_eq hx0_c4 hx1_c4 rfl
                    fun sf3 hcrl_ok3 hpc3 hrun3 hsp3 hcs3 hne0_3 h0b_3 htr_ok3 => ?_
                  rcases hcs_c4.of_cs hsp3 htr_ok3 hcs3 with
                    ⟨hsp_f3, hlr_f3, htr_f3, hx19_f3, hx20_f3, hx21_f3, hx22_f3, hx23_f3, hx24_f3, hx25_f3, hx26_f3, hx27_f3, hx28_f3, hv_f3⟩
                  let st3 := M.stepEvents (rustAllocEvents 2400 1) st2
                  have hdk_mem : memRegion (sf3.readReg64 (Reg.gpr 0#5)) 2400 =
                      memRegion (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList.length := by rw [hdk_len]
                  refine seq_vm_lscro (mid := lsρ "memcpy")
                    (P_mid := (memRegion (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList.length ∗
                      ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗ A.pool lim st3 sf3) ∗
                      (A.live (sf3.readReg64 (Reg.gpr 0#5)) 2400 1 ∗
                       vecU8Buf A.repAlloc 1152#64 (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList ∗
                       stackAt sp spqrSendCalleeStack ∗ A.live (sf1.readReg64 (Reg.gpr 0#5)) 64 1 ∗
                       ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗ Frame))
                    (Q := fun sd0 =>
                      CallStateAt s0 s sp ((blkPl_427).base + 656#64)
                        (s.readReg64 .x19) (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) epoch (sf3.readReg64 (Reg.gpr 0#5))
                        (s.readReg64 .x24) 2400#64 (s.readReg64 .x26) (sp + 4704#64) (s.readReg64 .x28) sd0 ∧
                      sd0.readReg64 .x0 = sf3.readReg64 (Reg.gpr 0#5) ∧ sd0.readReg64 .x1 = sp + 4704#64 ∧
                      (sd0.readReg64 .x2).toNat = (K.fromSeed seed).2.2.toList.length) hcrl_ok3 ?_ ?_
                  · rw [hdk_mem]
                    by_vm_steps (
                      wp_steps
                      refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
                        ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
                          ⟨by mk_call_state, by simp only [Reg.x0, wp_norm, arm64_norm, *],
                           by simp only [Reg.x1, wp_norm, arm64_norm, *],
                           by rw [hdk_len]; simp only [Reg.x2, wp_norm, arm64_norm, *]⟩⟩)
                  · rintro sd0 hpc_d0 hrun_d0 hcrl_d0 hvm_d0 ⟨hcs_d0, hx0_d0, hx1_d0, hx2_d0⟩
                    rw [← A.pool_of_vmPreserved hvm_d0]
                    refine call_memcpy_lscro hmemcpy (sf3.readReg64 (Reg.gpr 0#5)) (sp + 4704#64)
                      (K.fromSeed seed).2.2.toList st3
                      hcrl_d0 hpc_d0 hrun_d0 hcs_d0.sp_eq hsp_align hcs_d0.lr_eq hcs_d0.tr_eq hx0_d0 hx1_d0 hx2_d0 rfl
                      fun sd1 hcrl_d1 hpc_d1 hrun_d1 hsp_d1 hcs_d1 htr_d1 => ?_
                    rcases hcs_d0.of_cs hsp_d1 htr_d1 hcs_d1 with
                      ⟨hsp_d1', hlr_d1, htr_d1', hx19_d1, hx20_d1, hx21_d1, hx22_d1, hx23_d1, hx24_d1, hx25_d1, hx26_d1, hx27_d1, hx28_d1, hv_d1⟩
                    have hfold_dk :
                        A.live (sf3.readReg64 (Reg.gpr 0#5)) 2400 1 ∗ ((sf3.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
                        ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ⊢
                        vecU8Buf A.repAlloc 2400#64 (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList ∗
                        memRegion (sp + 4704#64) 2400 := by
                      have h4704 := pointsToBytes_entails_memRegion (sp + 4704#64) (K.fromSeed seed).2.2.toList
                      rw [hdk_len] at h4704; rw [← sepConj_assoc]
                      exact sepConj_mono
                        (live_pointsTo_entails_vecU8Buf (A := A.repAlloc) (sf3.readReg64 (Reg.gpr 0#5))
                          (K.fromSeed seed).2.2.toList 2400 hdk_len (by decide) (by decide) hne0_3)
                        h4704
                    refine SepWP.fold hfold_dk (by sep_focus) ?_
                    refine seq_vm_lscro (mid := (blkPl_427).base + 684#64)
                      (P_mid :=
                        (A.live (sf1.readReg64 (Reg.gpr 0#5)) 64 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ (K.fromSeed seed).1.toList) ∗
                         vecU8Buf A.repAlloc 1152#64 (sf2.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.1.toList ∗
                         vecU8Buf A.repAlloc 2400#64 (sf3.readReg64 (Reg.gpr 0#5)) (K.fromSeed seed).2.2.toList ∗
                         memRegion (sp + 4704#64) 2400 ∗ A.pool lim st3 sd1 ∗
                         stackAt sp spqrSendCalleeStack) ∗ Frame)
                      (Q := fun sf =>
                        sf.sp = sp ∧ sf.readReg64 .x0 = sp + 7136#64 ∧ sf.readReg64 .x1 = epoch ∧
                        sf.readReg64 .x2 = sf1.readReg64 (Reg.gpr 0#5) ∧ sf.readReg64 .x3 = 64#64 ∧
                        sf.readReg64 .x8 = sp + 4832#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
                        sf.readReg64 .x20 = sf1.readReg64 (Reg.gpr 0#5) ∧ sf.readReg64 .x21 = sf2.readReg64 (Reg.gpr 0#5) ∧
                        sf.readReg64 .x22 = epoch ∧ sf.readReg64 .x23 = sf3.readReg64 (Reg.gpr 0#5) ∧
                        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = 2400#64 ∧
                        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = 64#64 ∧
                        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.trace = s0.trace ∧
                        calleeSavedVRegs sf = calleeSavedVRegs s) hcrl_d1 ?_ ?_
                    · by_vm_steps (
                        wp_steps
                        refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
                          ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
                            ⟨by simp only [State.sp, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x0, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x1, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x2, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x3, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x8, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x19, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x20, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x21, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x22, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x23, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x24, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x25, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x26, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x27, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [Reg.x28, BitVec.add_assoc, wp_norm, arm64_norm, *],
                             by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩⟩)
                    · rintro sf hpc_sf hrun_sf hcrl_sf hvm_sf
                        ⟨hsp_sf, hx0_sf, hx1_sf, hx2_sf, hx3_sf, hx8_sf,
                         hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf, hx24_sf,
                         hx25_sf, hx26_sf, hx27_sf, hx28_sf, htr_sf, hvregs_sf⟩
                      have hpool_eq :
                          A.pool lim st3 sd1 = A.pool lim (M.stepEvents keysUnsampledAllocEvents st) sf := by
                        rw [hstep_all]; exact (A.pool_of_vmPreserved hvm_sf).symm
                      rw [hpool_eq]
                      exact hnext sf (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) (sf3.readReg64 (Reg.gpr 0#5))
                        hcrl_sf hne0_1 h0b_1 hpc_sf hrun_sf hsp_sf
                        hx0_sf hx1_sf hx2_sf hx3_sf hx8_sf
                        hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf hx24_sf
                        hx25_sf hx26_sf hx27_sf hx28_sf htr_sf hvregs_sf

theorem step_keysUnsampled_512_to_684_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym (withVmPreserved mlkemPk2Spec))
    (sp epoch : BitVec 64) (seed : List.Vector (BitVec 8) 64)
    (hpk1_slice : ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList)
    (hpk2_slice : ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList)
    (st : M.σ) (hfit : FitsEnv M lim st KeysUnsampledAllocEnv)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp}
    {post Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 512#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 7008#64) (hx22 : s.readReg64 .x22 = epoch)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      ((sp + 4704#64) ↦ₛ (K.fromSeed seed).2.2.toList) ∗
      A.pool lim st s ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr ek_ptr dk_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      hdr_ptr ≠ 0 → (hdr_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 684#64 → sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x0 = sp + 7136#64 → sf.readReg64 .x1 = epoch →
      sf.readReg64 .x2 = hdr_ptr → sf.readReg64 .x3 = 64#64 →
      sf.readReg64 .x8 = sp + 4832#64 → sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = hdr_ptr → sf.readReg64 .x21 = ek_ptr →
      sf.readReg64 .x22 = epoch → sf.readReg64 .x23 = dk_ptr →
      sf.readReg64 .x24 = s.readReg64 .x24 → sf.readReg64 .x25 = 2400#64 →
      sf.readReg64 .x26 = s.readReg64 .x26 → sf.readReg64 .x27 = 64#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 → sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((A.live hdr_ptr 64 1 ∗ (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          memRegion (sp + 4704#64) 2400 ∗
          A.pool lim (M.stepEvents keysUnsampledAllocEvents st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 684#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_keysUnsampled_512_to_684_sepWP_placed hA hpk2 sp epoch seed hpk1_slice hpk2_slice
    st hfit hcrl hsp_align hpc hrun hsp hx21 hx22 htrace hP
    fun sf hdr_ptr ek_ptr dk_ptr hcrl_sf hne0 h0b hpc_sf hrun_sf hsp_sf
      hx0 hx1 hx2 hx3 hx8 hx19 hx20 hx21' hx22' hx23 hx24 hx25 hx26 hx27 hx28 htr hvregs =>
      SepWP.done hpc_sf hrun_sf fun _ =>
        hnext sf hdr_ptr ek_ptr dk_ptr hcrl_sf hne0 h0b hpc_sf hrun_sf hsp_sf
          hx0 hx1 hx2 hx3 hx8 hx19 hx20 hx21' hx22' hx23 hx24 hx25 hx26 hx27 hx28 htr hvregs

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
