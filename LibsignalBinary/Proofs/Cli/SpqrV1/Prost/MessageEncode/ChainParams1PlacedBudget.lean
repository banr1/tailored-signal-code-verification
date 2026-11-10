/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Alloc.FetchPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParamsBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint4BasePlaced
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams1Budget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated1Budget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `encode<ChainParams> [local#3]` Verification (Block `453`)

Proves deterministic-capacity `encode_varint [local#4]` contracts (Block `451`) and budget-threaded
`EncodeChainParams1PlacedOk*` and exact-capacity `EncodeToVec` contracts on CLI Block `453` under
`[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAlloc RustCliAllocBudget
   RustLayoutOk VmPreserved rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB ChainParamsPB.encodeRaw)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeUint32Field)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall doReserveStack doReserveStackX reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (EncVarintCalleeSavedPlaced EncodeVarintGhost StepInv encodeVarintAux_of_not_ult
   encodeVarintAux_of_ult encodeVarint_exit_bs encodeVarint_step_bs shr63_ult_128
   stackAt_encodeVarint_gen_eq varintContByte vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm (ushr_ushr_7)
open scoped CryptoVerification.LibsignalTripleRatchet.Prost
open scoped CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.SpqrV1.Alloc
  (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.Varint
  (encodeVarint_exit_bs_s9 stage_len_lt_of_exit stage_len_lt_of_step)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (EncodeChainParamsGhost MsgEnc48CalleeSavedPlaced
   bs0_append_chainParamsHeaderBytes bs0_append_encodeChainParamsMsg
   bs_append_maxJump_of_ne_zero bs_append_maxJump_of_zero
   bs_append_maxOooKeys_of_ne_zero bs_append_maxOooKeys_of_zero
   calleeSavedPreserved_setPC_placed cap_toNat_eq_of_beq chainParamsHeaderBytes
   chainParamsHeaderBytes_len_bounds chainParamsHeaderBytes_len_eq encodeChainParamsMsg
   encodeChainParamsMsg_len_split lt_cap_toNat_of_beq_false maxJump_field_len_of_ne_zero
   maxOooKeys_field_len_of_ne_zero msgEnc48CalleeSavedPlaced_setPC msgEnc48SavedFrame
   msgEnc48VarintStackOf reserveCap_one_bounds subroutine_ok_withMsgEnc48CSPlaced_placed
   withMsgEnc48CSPlaced)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPl_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed (blkPC_451 blkPl_451 lsProg_451)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_453 blkPl_453_ρ lsProg_453)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEnv_events encodeVarintEvents pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBaseBudget (VecPushBudgetInv)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget
  (doReserve2SpecOf doReserve2SpecWithPlaced doReserve2_with_placed_of_ok)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeVarintDetSpec encodeVarintDetSpecOf encodeVarintDetSpecX)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated1Budget (VecCapStepInv2)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
  (do_reserve2_placed_ok do_reserve2_placed_ok_x
   step_encVarint2_final_placed step_encVarint2_prologue_placed
   step_encVarint2_s1_placed step_encVarint2_s2_placed step_encVarint2_s3_placed
   step_encVarint2_s9_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
  (step_encVarint2_s4_placed step_encVarint2_s5_placed step_encVarint2_s6_placed
   step_encVarint2_s7_placed step_encVarint2_s8_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (pushBytesStep pushBytesStep_snd_eq reserveStep reserveStep_of_need_doReserveEvents
   reserveStep_of_spare sepWP_done_tpidr_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
  (step_msg48_do_reserve2_call_placed step_msg48_encode_varint_det_call_placed
   step_msg48_encode_varint_det_tailcall_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (EncodeChainParamsEnv VecU8EncodeEnv encodeChainParamsExactVmSpecOf
   encodeChainParamsSpecOf fitsEnv_vecU8EncodeEnv_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams1Budget
  (ChainParamsBudgetInv CpReserve1Stepper extract_vecU8At_bounds hookSat_withPanics_spqr
   noAllocCostModel rawVmRecordBudget rawVmRecordBudget_pool_zeroEnforced
   vacuous_doReserve2_placed_ok vecU8At_rawVmRecordBudget vmRecordBudget
   vmRecordBudget_pool_zeroEnforced vmRecordBudget_repAlloc zeroEnforcedLimits)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParamsBasePlacedBudget
  (EncodeChainParams1ExactPlacedOk EncodeChainParams1PlacedOk EncodeChainParams1PlacedOkExt
   EncodeChainParams1PlacedOkExtX EncodeChainParams1PlacedOkX
   step_chainParams_after_hdr_branch_placed step_chainParams_after_maxJump_branch_placed
   step_chainParams_epilogue_placed step_chainParams_len_placed
   step_chainParams_prologue_placed step_chainParams_push_maxJump_tag_placed
   step_chainParams_push_maxOooKeys_epilogue_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeChainParamsExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.FinalPlacedBudget
  (etv_encodeChainParams_exact_of_lscl)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64
  blkPl_453_ρ

@[local arm64_norm] private theorem blkPl_451_base_eq [LibsignalPlacement] :
    (blkPl_451).base = lsmpl.base 451 := rfl

@[local arm64_norm] private theorem blkPl_460_base_eq [LibsignalPlacement] :
    (blkPl_460).base = lsmpl.base 460 := rfl

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) :
    a + (b - a) = b := by bv_omega

@[local arm64_norm] private theorem bv_bl_target_norm (base off target : BitVec 64) :
    (base + off) + (target - base - off) = target := by bv_omega

@[local arm64_norm] private theorem bv_bl_entry_norm (base target : BitVec 64) :
    base + (target - base - 0#64) = target := by bv_omega

local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(CryptoVerification.SpqrV1.Prost.MessageEncode.MsgEnc48CalleeSavedPlaced.step $hcs
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) $hinv)

/-! ## 1. Deterministic-Capacity `encode_varint::<Vec<u8>> [local#4]` (Block `451` → Block `460`) -/

private theorem vecCapStepInv2_init (x : EncodeVarintGhost) :
    VecCapStepInv2 x x.cap x.bs (encodeVarint x.val).length := rfl

private theorem vecCapStepInv2_of_rem_eq {x : EncodeVarintGhost} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {n1 n2 : Nat}
    (h : VecCapStepInv2 x curCap curBs n1) (hn : n1 = n2) :
    VecCapStepInv2 x curCap curBs n2 := hn ▸ h

private theorem vecCapStepInv2_step_one {x : EncodeVarintGhost} {curCap nextCap : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8} {rem : Nat}
    (h : VecCapStepInv2 x curCap curBs (rem + 1))
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecCapStepInv2 x nextCap (curBs ++ [byte]) rem := by
  have hlen : (curBs ++ [byte]).length = curBs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  unfold VecCapStepInv2 at h ⊢
  rw [h, pushBytesStep, hcap_step, hlen]

private theorem vecPushBudgetInv2_exit {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt) (h : v.ult 128#64 = true) :
    VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt :=
  hinv.of_rem_eq (by rw [encodeVarintAux_of_ult h]; rfl)

private theorem vecCapStepInv2_exit {x : EncodeVarintGhost} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64}
    (hcap : VecCapStepInv2 x curCap curBs (encodeVarintAux (fuel + 1) v).length)
    (h : v.ult 128#64 = true) : VecCapStepInv2 x curCap curBs 1 :=
  vecCapStepInv2_of_rem_eq hcap (by rw [encodeVarintAux_of_ult h]; rfl)

private theorem vecPushBudgetInv2_fits_reserve {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ} {curCap curPtr : BitVec 64}
    {curBs : List (BitVec 8)} {fuel : Nat} {v : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = false) (hcap_eq : curCap.toNat = curBs.length) :
    FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk x.v curCap curPtr curBs 1)) :=
  (hinv.of_rem_eq (by rw [encodeVarintAux_of_not_ult h]; rfl)).fits_reserve x.v hcap_eq

private theorem vecPushBudgetInv2_step {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeVarintGhost} {st0 curSt : M.σ} {curCap curPtr nextCap nextPtr : BitVec 64}
    {curBs : List (BitVec 8)} {byte : BitVec 8} {fuel : Nat} {v nextV : BitVec 64}
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs
      (encodeVarintAux (fuel + 1) v).length curSt)
    (h : v.ult 128#64 = false) (hshift : v >>> 7 = nextV)
    (hge : curCap.toNat ≤ nextCap.toNat)
    (hpres : curBs.length < curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr)
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecPushBudgetInv M lim x st0 nextCap nextPtr (curBs ++ [byte])
      (encodeVarintAux fuel nextV).length
      (M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt) :=
  (hinv.of_rem_eq (by rw [encodeVarintAux_of_not_ult h, hshift]; rfl)).step hge hpres hcap_step

private theorem vecCapStepInv2_step {x : EncodeVarintGhost}
    {curCap nextCap : BitVec 64} {curBs : List (BitVec 8)} {byte : BitVec 8}
    {fuel : Nat} {v nextV : BitVec 64}
    (hcap : VecCapStepInv2 x curCap curBs (encodeVarintAux (fuel + 1) v).length)
    (h : v.ult 128#64 = false) (hshift : v >>> 7 = nextV)
    (hcap_step : nextCap.toNat = (pushByteStep curCap.toNat curBs.length).1) :
    VecCapStepInv2 x nextCap (curBs ++ [byte]) (encodeVarintAux fuel nextV).length :=
  vecCapStepInv2_step_one (vecCapStepInv2_of_rem_eq hcap (by rw [encodeVarintAux_of_not_ult h, hshift]; rfl)) hcap_step

/-- Deterministic-capacity exit lemma proving `(encodeVarintDetSpecOf resStack A lim).post`
for `encode_varint [local#4]` (Block `451` → Block `460`). -/
theorem step_encVarint2_det_exit_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (x : EncodeVarintGhost) (st0 curSt : M.σ)
    (lastVal curCap curPtr v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hinv : VecPushBudgetInv M lim x st0 curCap curPtr curBs 1 curSt)
    (hcap_inv : VecCapStepInv2 x curCap curBs 1)
    (hbs : curBs ++ [lastVal.setWidth 8] = x.bs ++ encodeVarint x.val)
    (hlen_lt : curBs.length < curCap.toNat ∨ curBs.length < 2 ^ 62)
    {R P : SepProp} {Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_451).base + 868#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 48#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = lastVal) (hx1 : s.readReg64 .x1 = x.v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length) (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSavedPlaced s0 s)
    (hP : P = ((x.v ↦₆₄ curCap) ∗ ((x.v + 8#64) ↦₆₄ curPtr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗ vecU8Buf A.repAlloc curCap curPtr curBs ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      A.pool lim curSt s ∗ stackAt (s0.sp - 48#64) resStack) ∗
      (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (lsProg_451 H) (s0.readReg64 .lr) s P
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeVarintDetSpecOf resStack A lim).post (x, st0) s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) Qp := by
  refine step_encVarint2_final_placed (F := emp) A lim H hdoReserve lastVal x.v curCap curPtr s0.sp v48 v40
    curBs curSt hlen_lt (fun hcap_eq => hinv.fits_reserve x.v hcap_eq)
    hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs (by rw [hP]; sep_ac_rfl) ?_
  intro sf cap' ptr' hpcf hrunf hspf htrf hcsf hge hpres hcap_step
  have hinv' := hinv.step (byte := lastVal.setWidth 8) hge hpres hcap_step
  have hcap_inv' := vecCapStepInv2_step_one (byte := lastVal.setWidth 8) hcap_inv hcap_step
  have hcap_det : cap'.toNat = (pushBytesStep (encodeVarint x.val).length x.cap.toNat x.bs.length).1 := by
    simpa [VecCapStepInv2, pushBytesStep] using hcap_inv'.symm
  have hres' := hinv'.res; rw [hbs] at hres'; have ⟨hcap_le, hcap_pres⟩ := hres'.finish
  have hev_eq : M.stepEvents (encodeVarintEvents x) st0 =
      M.stepEvents (pushByteStep curCap.toNat curBs.length).2 curSt := by
    simpa [pushBytesEvents] using hinv'.events_eq
  refine ⟨?_, hspf, hcsf⟩; intro hm_f
  rw [sepConj_emp, hbs, ← hev_eq] at hm_f
  simp only [encodeVarintDetSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v48, v40, s0.readReg64 .fp, s0.readReg64 .lr,
    s0.readReg64 .x20, s0.readReg64 .x19, encodeVarintEvents x, cap', ptr',
    htrf, ⟨hcap_le, hcap_pres, hcap_det⟩, ?_⟩
  rw [eq_true (encodeVarintEnv_events x), pure_true]; convert hm_f using 1; sep_ac_rfl

/-- Generalized placed correctness theorem for `encode_varint [local#4]` (Block `451` → Block `460`),
proving the deterministic post-capacity specification `encodeVarintDetSpecOf resStack A lim`. -/
theorem encodeVarint2_det_gen_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    {resStack : Nat} (hres : resStack + 8 * 6 < 2 ^ 64)
    (x : EncodeVarintGhost) (st0 : M.σ) (R : SepProp) (s0 : State)
    {Qp : State → SepProp → Prop}
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460) (doReserve2SpecWithPlaced resStack s0 A lim))
    (hpc0 : s0.pc = (blkPl_451).base) (hrun0 : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeVarintDetSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp0 : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_451 H) (s0.readReg64 .lr) s0 P
        (fun s' Q =>
          ((s'.mem ⊨ Q ∗ R) → (s'.mem ⊨ (encodeVarintDetSpecOf resStack A lim).post (x, st0) s0 s' ∗ R)) ∧
          s'.sp = s0.sp ∧ CalleeSavedPreserved s0 s') Qp := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp0
  simp only [encodeVarintDetSpecOf, encodeVarintFitSpecOf, vecU8At_eq_header_sep_buf, vecHeader,
    stackAt_encodeVarint_gen_eq hres s0.sp, sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v48, v40, v32, v24, v16, v8, ⟨hx0, hx1, hlen_bound, hfits0⟩, hpre⟩
  refine ⟨((x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      ((x.v + 16#64) ↦₆₄ BitVec.ofNat 64 x.bs.length) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
      ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
      A.pool lim st0 s0) ∗ (vecU8Buf A.repAlloc x.cap x.ptr x.bs ∗ stackAt (s0.sp - 48#64) resStack),
    by convert hpre using 1; sep_ac_rfl, ?_⟩
  refine step_encVarint2_prologue_placed A lim H x.val x.v x.cap x.ptr s0.sp
    v48 v40 v32 v24 v16 v8 x.bs st0 hpc0 hrun0 rfl halign hx0 hx1 rfl ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)
  have hlen_def : (encodeVarint x.val).length = (encodeVarintAux 10 x.val).length := by
    with_unfolding_all rfl
  have hinv0 := (VecPushBudgetInv.init x st0 hfits0).of_rem_eq hlen_def
  have hcap0 := vecCapStepInv2_of_rem_eq (vecCapStepInv2_init x) hlen_def
  have hbs0 : x.bs ++ encodeVarintAux 10 x.val = x.bs ++ encodeVarint x.val := by
    with_unfolding_all rfl
  cases hult0 : x.val.ult 128#64
  · simp only [hult0, ↓reduceIte, Bool.false_eq_true] at hpc1
    have hbs1 := encodeVarint_step_bs hbs0 hult0 rfl
    refine step_encVarint2_s1_placed (F := FSave) A lim H hdoReserve x.val x.v x.cap x.ptr s0.sp v48 v40 x.bs st0
      (stage_len_lt_of_step hlen_bound hinv0.res hbs0) (vecPushBudgetInv2_fits_reserve hinv0 hult0)
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by dsimp [FSave]; sep_ac_rfl) ?_
    intro s2 cap1 ptr1 v48_1 v40_1 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 hge1 hpres1 hstep1
    have hinv1 := vecPushBudgetInv2_step (byte := varintContByte x.val) hinv0 hult0 rfl hge1 hpres1 hstep1
    have hcap1 := vecCapStepInv2_step (byte := varintContByte x.val) hcap0 hult0 rfl hstep1
    cases hult1 : (x.val >>> 7).ult 128#64
    · simp only [hult1, ↓reduceIte, Bool.false_eq_true] at hpc2 hx0_2
      have hbs2 := encodeVarint_step_bs (nextV := x.val >>> 14) hbs1 hult1 (ushr_ushr_7 x.val 7 14)
      refine step_encVarint2_s2_placed (F := FSave) A lim H hdoReserve x.val x.v cap1 ptr1 s0.sp v48_1 v40_1 _ _
        (stage_len_lt_of_step hlen_bound hinv1.res hbs1) (vecPushBudgetInv2_fits_reserve hinv1 hult1)
        hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hx10_2 hcs2 rfl ?_
      intro s3 cap2 ptr2 v48_2 v40_2 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 hge2 hpres2 hstep2
      have hinv2 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 7)) hinv1 hult1 (ushr_ushr_7 x.val 7 14) hge2 hpres2 hstep2
      have hcap2 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 7)) hcap1 hult1 (ushr_ushr_7 x.val 7 14) hstep2
      cases hult2 : (x.val >>> 14).ult 128#64
      · simp only [hult2, ↓reduceIte, Bool.false_eq_true] at hpc3 hx0_3
        have hbs3 := encodeVarint_step_bs (nextV := x.val >>> 21) hbs2 hult2 (ushr_ushr_7 x.val 14 21)
        refine step_encVarint2_s3_placed (F := FSave) A lim H hdoReserve x.val x.v cap2 ptr2 s0.sp v48_2 v40_2 _ _
          (stage_len_lt_of_step hlen_bound hinv2.res hbs2) (vecPushBudgetInv2_fits_reserve hinv2 hult2)
          hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hx10_3 hcs3 rfl ?_
        intro s4 cap3 ptr3 v48_3 v40_3 hpc4 hrun4 hsp4 htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 hge3 hpres3 hstep3
        have hinv3 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 14)) hinv2 hult2 (ushr_ushr_7 x.val 14 21) hge3 hpres3 hstep3
        have hcap3 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 14)) hcap2 hult2 (ushr_ushr_7 x.val 14 21) hstep3
        cases hult3 : (x.val >>> 21).ult 128#64
        · simp only [hult3, ↓reduceIte, Bool.false_eq_true] at hpc4 hx0_4
          have hbs4 := encodeVarint_step_bs (nextV := x.val >>> 28) hbs3 hult3 (ushr_ushr_7 x.val 21 28)
          refine step_encVarint2_s4_placed (F := FSave) A lim H hdoReserve x.val x.v cap3 ptr3 s0.sp v48_3 v40_3 _ _
            (stage_len_lt_of_step hlen_bound hinv3.res hbs3) (vecPushBudgetInv2_fits_reserve hinv3 hult3)
            hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hx12_4 hcs4 rfl ?_
          intro s5 cap4 ptr4 v48_4 v40_4 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 hge4 hpres4 hstep4
          have hinv4 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 21)) hinv3 hult3 (ushr_ushr_7 x.val 21 28) hge4 hpres4 hstep4
          have hcap4 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 21)) hcap3 hult3 (ushr_ushr_7 x.val 21 28) hstep4
          cases hult4 : (x.val >>> 28).ult 128#64
          · simp only [hult4, ↓reduceIte, Bool.false_eq_true] at hpc5 hx0_5
            have hbs5 := encodeVarint_step_bs (nextV := x.val >>> 35) hbs4 hult4 (ushr_ushr_7 x.val 28 35)
            refine step_encVarint2_s5_placed (F := FSave) A lim H hdoReserve x.val x.v cap4 ptr4 s0.sp v48_4 v40_4 _ _
              (stage_len_lt_of_step hlen_bound hinv4.res hbs4) (vecPushBudgetInv2_fits_reserve hinv4 hult4)
              hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hx10_5 hx11_5 hx12_5 hcs5 rfl ?_
            intro s6 cap5 ptr5 v48_5 v40_5 hpc6 hrun6 hsp6 htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 hge5 hpres5 hstep5
            have hinv5 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 28)) hinv4 hult4 (ushr_ushr_7 x.val 28 35) hge5 hpres5 hstep5
            have hcap5 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 28)) hcap4 hult4 (ushr_ushr_7 x.val 28 35) hstep5
            cases hult5 : (x.val >>> 35).ult 128#64
            · simp only [hult5, ↓reduceIte, Bool.false_eq_true] at hpc6 hx0_6
              have hbs6 := encodeVarint_step_bs (nextV := x.val >>> 42) hbs5 hult5 (ushr_ushr_7 x.val 35 42)
              refine step_encVarint2_s6_placed (F := FSave) A lim H hdoReserve x.val x.v cap5 ptr5 s0.sp v48_5 v40_5 _ _
                (stage_len_lt_of_step hlen_bound hinv5.res hbs5) (vecPushBudgetInv2_fits_reserve hinv5 hult5)
                hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hx10_6 hx11_6 hx13_6 hcs6 rfl ?_
              intro s7 cap6 ptr6 v48_6 v40_6 hpc7 hrun7 hsp7 htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 hge6 hpres6 hstep6
              have hinv6 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 35)) hinv5 hult5 (ushr_ushr_7 x.val 35 42) hge6 hpres6 hstep6
              have hcap6 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 35)) hcap5 hult5 (ushr_ushr_7 x.val 35 42) hstep6
              cases hult6 : (x.val >>> 42).ult 128#64
              · simp only [hult6, ↓reduceIte, Bool.false_eq_true] at hpc7 hx0_7
                have hbs7 := encodeVarint_step_bs (nextV := x.val >>> 49) hbs6 hult6 (ushr_ushr_7 x.val 42 49)
                refine step_encVarint2_s7_placed (F := FSave) A lim H hdoReserve x.val x.v cap6 ptr6 s0.sp v48_6 v40_6 _ _
                  (stage_len_lt_of_step hlen_bound hinv6.res hbs6) (vecPushBudgetInv2_fits_reserve hinv6 hult6)
                  hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hx12_7 hx13_7 hcs7 rfl ?_
                intro s8 cap7 ptr7 v48_7 v40_7 hpc8 hrun8 hsp8 htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 hge7 hpres7 hstep7
                have hinv7 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 42)) hinv6 hult6 (ushr_ushr_7 x.val 42 49) hge7 hpres7 hstep7
                have hcap7 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 42)) hcap6 hult6 (ushr_ushr_7 x.val 42 49) hstep7
                cases hult7 : (x.val >>> 49).ult 128#64
                · simp only [hult7, ↓reduceIte, Bool.false_eq_true] at hpc8 hx0_8
                  have hbs8 := encodeVarint_step_bs (nextV := x.val >>> 56) hbs7 hult7 (ushr_ushr_7 x.val 49 56)
                  refine step_encVarint2_s8_placed (F := FSave) A lim H hdoReserve x.val x.v cap7 ptr7 s0.sp v48_7 v40_7 _ _
                    (stage_len_lt_of_step hlen_bound hinv7.res hbs7) (vecPushBudgetInv2_fits_reserve hinv7 hult7)
                    hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hx10_8 hx11_8 hx12_8 hcs8 rfl ?_
                  intro s9 cap8 ptr8 v48_8 v40_8 hpc9 hrun9 hsp9 htr9 hx0_9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 hge8 hpres8 hstep8
                  have hinv8 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 49)) hinv7 hult7 (ushr_ushr_7 x.val 49 56) hge8 hpres8 hstep8
                  have hcap8 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 49)) hcap7 hult7 (ushr_ushr_7 x.val 49 56) hstep8
                  cases hult8 : (x.val >>> 56).ult 128#64
                  · simp only [hult8, ↓reduceIte, Bool.false_eq_true] at hpc9 hx0_9
                    have hbs9 := encodeVarint_step_bs (nextV := x.val >>> 63) hbs8 hult8 (ushr_ushr_7 x.val 56 63)
                    refine step_encVarint2_s9_placed
                      (F := ((s0.sp - 48#64) ↦₆₄ v48_8) ∗ ((s0.sp - 40#64) ↦₆₄ v40_8) ∗ FSave)
                      A lim H hdoReserve x.val x.v cap8 ptr8 s0.sp _ _ hult8
                      (stage_len_lt_of_step hlen_bound hinv8.res hbs8) (vecPushBudgetInv2_fits_reserve hinv8 hult8)
                      hpc9 hrun9 hsp9 halign htr9 hx1_9 hx8_9 hx9_9 hx10_9 hx11_9 hcs9 (by sep_ac_rfl) ?_
                    intro s10 cap9 ptr9 hpc10 hrun10 hsp10 htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 hge9 hpres9 hstep9
                    have hinv9 := vecPushBudgetInv2_step (byte := varintContByte (x.val >>> 56)) hinv8 hult8 (ushr_ushr_7 x.val 56 63) hge9 hpres9 hstep9
                    have hcap9 := vecCapStepInv2_step (byte := varintContByte (x.val >>> 56)) hcap8 hult8 (ushr_ushr_7 x.val 56 63) hstep9
                    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ 1#64 cap9 ptr9 v48_8 v40_8 _
                      (vecPushBudgetInv2_exit hinv9 (shr63_ult_128 x.val)) (vecCapStepInv2_exit hcap9 (shr63_ult_128 x.val))
                      (encodeVarint_exit_bs_s9 hbs9 hult8) (stage_len_lt_of_exit hlen_bound hinv9.res (encodeVarint_exit_bs_s9 hbs9 hult8))
                      hpc10 hrun10 hsp10 halign htr10 hx0_10 hx1_10 hx8_10 hx9_10 hcs10 (by dsimp [FSave]; sep_ac_rfl)
                  · simp only [hult8, ↓reduceIte] at hpc9 hx0_9
                    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 56) cap8 ptr8 v48_8 v40_8 _
                      (vecPushBudgetInv2_exit hinv8 hult8) (vecCapStepInv2_exit hcap8 hult8) (encodeVarint_exit_bs hbs8 hult8)
                      (stage_len_lt_of_exit hlen_bound hinv8.res (encodeVarint_exit_bs hbs8 hult8)) hpc9 hrun9 hsp9 halign htr9 hx0_9 hx1_9 hx8_9 hx9_9 hcs9 rfl
                · simp only [hult7, ↓reduceIte] at hpc8 hx0_8
                  exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 49) cap7 ptr7 v48_7 v40_7 _
                    (vecPushBudgetInv2_exit hinv7 hult7) (vecCapStepInv2_exit hcap7 hult7) (encodeVarint_exit_bs hbs7 hult7)
                    (stage_len_lt_of_exit hlen_bound hinv7.res (encodeVarint_exit_bs hbs7 hult7)) hpc8 hrun8 hsp8 halign htr8 hx0_8 hx1_8 hx8_8 hx9_8 hcs8 rfl
              · simp only [hult6, ↓reduceIte] at hpc7 hx0_7
                exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 42) cap6 ptr6 v48_6 v40_6 _
                  (vecPushBudgetInv2_exit hinv6 hult6) (vecCapStepInv2_exit hcap6 hult6) (encodeVarint_exit_bs hbs6 hult6)
                  (stage_len_lt_of_exit hlen_bound hinv6.res (encodeVarint_exit_bs hbs6 hult6)) hpc7 hrun7 hsp7 halign htr7 hx0_7 hx1_7 hx8_7 hx9_7 hcs7 rfl
            · simp only [hult5, ↓reduceIte] at hpc6 hx0_6
              exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 35) cap5 ptr5 v48_5 v40_5 _
                (vecPushBudgetInv2_exit hinv5 hult5) (vecCapStepInv2_exit hcap5 hult5) (encodeVarint_exit_bs hbs5 hult5)
                (stage_len_lt_of_exit hlen_bound hinv5.res (encodeVarint_exit_bs hbs5 hult5)) hpc6 hrun6 hsp6 halign htr6 hx0_6 hx1_6 hx8_6 hx9_6 hcs6 rfl
          · simp only [hult4, ↓reduceIte] at hpc5 hx0_5
            exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 28) cap4 ptr4 v48_4 v40_4 _
              (vecPushBudgetInv2_exit hinv4 hult4) (vecCapStepInv2_exit hcap4 hult4) (encodeVarint_exit_bs hbs4 hult4)
              (stage_len_lt_of_exit hlen_bound hinv4.res (encodeVarint_exit_bs hbs4 hult4)) hpc5 hrun5 hsp5 halign htr5 hx0_5 hx1_5 hx8_5 hx9_5 hcs5 rfl
        · simp only [hult3, ↓reduceIte] at hpc4 hx0_4
          exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 21) cap3 ptr3 v48_3 v40_3 _
            (vecPushBudgetInv2_exit hinv3 hult3) (vecCapStepInv2_exit hcap3 hult3) (encodeVarint_exit_bs hbs3 hult3)
            (stage_len_lt_of_exit hlen_bound hinv3.res (encodeVarint_exit_bs hbs3 hult3)) hpc4 hrun4 hsp4 halign htr4 hx0_4 hx1_4 hx8_4 hx9_4 hcs4 rfl
      · simp only [hult2, ↓reduceIte] at hpc3 hx0_3
        exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 14) cap2 ptr2 v48_2 v40_2 _
          (vecPushBudgetInv2_exit hinv2 hult2) (vecCapStepInv2_exit hcap2 hult2) (encodeVarint_exit_bs hbs2 hult2)
          (stage_len_lt_of_exit hlen_bound hinv2.res (encodeVarint_exit_bs hbs2 hult2)) hpc3 hrun3 hsp3 halign htr3 hx0_3 hx1_3 hx8_3 hx9_3 hcs3 rfl
    · simp only [hult1, ↓reduceIte] at hpc2 hx0_2
      exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 _ (x.val >>> 7) cap1 ptr1 v48_1 v40_1 _
        (vecPushBudgetInv2_exit hinv1 hult1) (vecCapStepInv2_exit hcap1 hult1) (encodeVarint_exit_bs hbs1 hult1)
        (stage_len_lt_of_exit hlen_bound hinv1.res (encodeVarint_exit_bs hbs1 hult1)) hpc2 hrun2 hsp2 halign htr2 hx0_2 hx1_2 hx8_2 hx9_2 hcs2 rfl
  · simp only [hult0, ↓reduceIte] at hpc1
    exact step_encVarint2_det_exit_placed hres A lim H hdoReserve x st0 st0 x.val x.cap x.ptr v48 v40 x.bs
      (vecPushBudgetInv2_exit hinv0 hult0) (vecCapStepInv2_exit hcap0 hult0) (encodeVarint_exit_bs hbs0 hult0)
      (stage_len_lt_of_exit hlen_bound hinv0.res (encodeVarint_exit_bs hbs0 hult0))
      hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx8_1 hx9_1 hcs1 (by sep_ac_rfl)

theorem encodeVarint2_det_placed_ok_of_doReserve [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 8 * 6 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : String → Option (State → State))
    (hdoReserve : subroutine_ok (lsProg_451 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim))) :
    subroutine_ok (lsProg_451 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp
  rintro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre hsp0
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcode0, hpre⟩
  obtain ⟨P, hP, hwp⟩ := encodeVarint2_det_gen_placed_ok A lim H hres x st0 R s0
    (doReserve2_with_placed_of_ok A lim s0 hcode0 hdoReserve) hpc0 hrun0 hpre hsp0
  exact ⟨P, R, hP, hwp⟩

theorem encode_varint2_det_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_451).rebase (blkPl_451).base H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpec A lim)) :=
  encodeVarint2_det_placed_ok_of_doReserve (resStack := doReserveStack) (by decide) A lim H
    (ls_subroutine_ok_of_block (callerProg := lsProg_451 H)
      (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_varint2_det_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_451).rebase (blkPl_451).base H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecX A lim)) :=
  encodeVarint2_det_placed_ok_of_doReserve (resStack := doReserveStackX) (by decide) A lim H
    (ls_subroutine_ok_of_block (callerProg := lsProg_451 H)
      (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))

/-! ## 2. Block `453` (`[local#3]`) Reserve Steppers, Stage Steppers & Core Proof -/

private theorem sepWPp_mono_post {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q1 Q2 Qp1 Qp2 : State → SepProp → Prop} (h : SepWPp prog ret s P Q1 Qp1)
    (hq : ∀ sf Pf, Q1 sf Pf → Q2 sf Pf) (hqp : ∀ sf Pf, Qp1 sf Pf → Qp2 sf Pf) :
    SepWPp prog ret s P Q2 Qp2 := fun R hm hL => by
  obtain ⟨sf, hst, ⟨h1, h2, Pf, hmf, hQ⟩ | ⟨hp, Pf, hmf, hQp⟩ | hoom⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨h1, h2, Pf, hmf, hq sf Pf hQ⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl ⟨hp, Pf, hmf, hqp sf Pf hQp⟩)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hoom)⟩

private theorem satisfies_encodeChainParams_post {resStack : Nat} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (x : EncodeChainParamsGhost) (st0 : M.σ)
    (s0 sf : State) (R : SepProp) (cap' ptr' : BitVec 64) (evs : List AllocEvent)
    (htrf : sf.trace = s0.trace) (hge : x.cap.toNat ≤ cap'.toNat)
    (hpres : x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat → cap' = x.cap ∧ ptr' = x.ptr)
    (hEnv : EncodeChainParamsEnv x evs)
    (hsp_ev : x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat → evs = [] ∧ VmPreserved s0 sf)
    (hm : sf.mem ⊨ vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeChainParamsMsg x.tag x.p) ∗
      A.pool lim (M.stepEvents evs st0) sf ∗ stackAt s0.sp (msgEnc48VarintStackOf resStack) ∗ R) :
    sf.mem ⊨ (encodeChainParamsSpecOf resStack A lim).post (x, st0) s0 sf ∗ R := by
  dsimp only [encodeChainParamsSpecOf]
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨htrf, ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨cap', ?_⟩
  rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨ptr', ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hge, hpres⟩, ?_⟩
  rw [sepConj_left_comm (vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeChainParamsMsg x.tag x.p))]
  rw [sepExists_sepConj_left, satisfies_sepExists]; refine ⟨evs, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨⟨hEnv, hsp_ev⟩, ?_⟩
  exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm

private theorem step_reserve_1_common_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_453 H) (lsmpl.base 460)
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim))) :
    CpReserve1Stepper resStack A lim (lsProg_453 H) blkPl_453 212#64 228#64 s0 ∧
      CpReserve1Stepper resStack A lim (lsProg_453 H) blkPl_453 128#64 144#64 s0 := by
  constructor
  · intro v curCap curPtr sp curBs p curSt hfit1 hfits s ret P F Q Qp
      hpc hrun hsp halign htr hx19 hx20 hx21 hcs hP hnext
    have hx21' := hx21 rfl; subst hP
    refine extract_vecU8At_bounds A.repAlloc v curCap curPtr curBs
      (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by sep_ac_rfl) fun hcap_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
    by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
    · have hcap_eq := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
      have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
      have hres_eq := reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
      have hfits_do : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by rwa [hres_eq] at hfits
      apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0; rw [← A.pool_of_vmPreserved hvmp0]
        refine step_msg48_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
          ((blkPl_453).base + 312#64) curBs 1 curSt hbound1 hfits_do (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm]) (cs_step hcs hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
        intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
        let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx20_1 : s1.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs01.2.1]; simp only [arm64_norm, *]
        have hx21_1 : s1.readReg64 .x21 = p.maxJump.zeroExtend 64 := by rw [hcs01.2.2.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_453).base + 228#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hvmp1 hinv1
          have hst_eq : M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) curSt =
              M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by rw [hres_eq]
          rw [← A.pool_of_vmPreserved hvmp1, hst_eq]
          refine SepWPp.weaken_pre (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (fun _ => by simp only [arm64_norm, *])
              (cs_step hcs1 hinv1) (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega)
              (fun h => absurd h (by omega)) (htoNat1.trans (congrArg Prod.fst hres_eq.symm)))))
    · have hlt0 := lt_cap_toNat_of_beq_false hcap_le (Bool.eq_false_iff.mpr hcap)
      have hres_eq := reserveStep_of_spare (cap := curCap.toNat) (len := curBs.length) (additional := 1) (by omega)
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_453).base + 228#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0
        have hst_eq : curSt = M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by rw [hres_eq]; rfl
        rw [← A.pool_of_vmPreserved hvmp0, hst_eq]
        refine SepWPp.weaken_pre (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (fun _ => by simp only [arm64_norm, *])
            (cs_step hcs hinv0) hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (congrArg Prod.fst hres_eq.symm)))
  · intro v curCap curPtr sp curBs p curSt hfit1 hfits s ret P F Q Qp
      hpc hrun hsp halign htr hx19 hx20 _ hcs hP hnext
    subst hP
    refine extract_vecU8At_bounds A.repAlloc v curCap curPtr curBs
      (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by sep_ac_rfl) fun hcap_le _ _ => ?_
    rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
    by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
    · have hcap_eq := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
      have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
      obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
      have hres_eq := reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
      have hfits_do : FitsEvents M lim curSt (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by rwa [hres_eq] at hfits
      apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 460)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0; rw [← A.pool_of_vmPreserved hvmp0]
        refine step_msg48_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
          ((blkPl_453).base + 292#64) curBs 1 curSt hbound1 hfits_do (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm]) (cs_step hcs hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
        intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
        let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx20_1 : s1.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs01.2.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_453).base + 144#64)
        by_vm_steps (
          wp_steps
          apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
          intro hvmp1 hinv1
          have hst_eq : M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) curSt =
              M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by rw [hres_eq]
          rw [← A.pool_of_vmPreserved hvmp1, hst_eq]
          refine SepWPp.weaken_pre (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
            (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (fun h => absurd h (by decide))
              (cs_step hcs1 hinv1) (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega)
              (fun h => absurd h (by omega)) (htoNat1.trans (congrArg Prod.fst hres_eq.symm)))))
    · have hlt0 := lt_cap_toNat_of_beq_false hcap_le (Bool.eq_false_iff.mpr hcap)
      have hres_eq := reserveStep_of_spare (cap := curCap.toNat) (len := curBs.length) (additional := 1) (by omega)
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_453).base + 144#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0
        have hst_eq : curSt = M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by rw [hres_eq]; rfl
        rw [← A.pool_of_vmPreserved hvmp0, hst_eq]
        refine SepWPp.weaken_pre (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (fun h => absurd h (by decide))
            (cs_step hcs hinv0) hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (congrArg Prod.fst hres_eq.symm)))

theorem step_reserve_212_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_453 H) (lsmpl.base 460) (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim))) :
    CpReserve1Stepper resStack A lim (lsProg_453 H) blkPl_453 212#64 228#64 s0 :=
  (step_reserve_1_common_placed hres A lim hdoReserve).1

theorem step_reserve_128_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_453 H) (lsmpl.base 460) (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim))) :
    CpReserve1Stepper resStack A lim (lsProg_453 H) blkPl_453 128#64 144#64 s0 :=
  (step_reserve_1_common_placed hres A lim hdoReserve).2

private theorem step_hdr_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_453 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (x : EncodeChainParamsGhost) (st0 : M.σ) (sp : BitVec 64)
    (inv0 : ChainParamsBudgetInv M lim x st0 x.cap.toNat [])
    (hfit_hdr : x.bs.length + (chainParamsHeaderBytes x.tag x.p).length ≤ x.cap.toNat ∨
      x.bs.length + (chainParamsHeaderBytes x.tag x.p).length + 10 < 2 ^ 62)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = x.tag) (hw1 : s.readReg32 .x1 = x.p.maxJump)
    (hw2 : s.readReg32 .x2 = x.p.maxOooKeys) (hx3 : s.readReg64 .x3 = x.v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s ∗
      stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64) (evs1 : List AllocEvent),
      sm.pc = (blkPl_453).base + (if x.p.maxJump == 0#32 then 124#64 else 212#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = x.v → sm.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = x.p.maxJump.zeroExtend 64 → MsgEnc48CalleeSavedPlaced s0 sm →
      x.cap.toNat ≤ cap1.toNat →
      (x.bs.length + (chainParamsHeaderBytes x.tag x.p).length ≤ x.cap.toNat →
        cap1 = x.cap ∧ ptr1 = x.ptr) →
      ChainParamsBudgetInv M lim x st0 cap1.toNat evs1 →
      SepWPp (lsProg_453 H) ret sm
        ((vecU8At A.repAlloc x.v cap1 ptr1 (x.bs ++ chainParamsHeaderBytes x.tag x.p) ∗
          A.pool lim (M.stepEvents evs1 st0) sm ∗
          stackAt (sp - 48#64) (0x30 + resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp (lsProg_453 H) ret s P Q Qp := by
  have hlen_split := encodeChainParamsMsg_len_split x.tag x.p
  have hlen_eq := chainParamsHeaderBytes_len_eq x.tag x.p
  obtain ⟨hb1, hb2, _⟩ := chainParamsHeaderBytes_len_bounds x.tag x.p
  refine step_chainParams_prologue_placed hres H x.v sp x.tag x.p hpc hrun hsp halign htr
    hw0 hw1 hw2 hx3 hcs hhs0 (F := vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1 hvmp0
  rw [sepConj_assoc, sepConj_left_comm (vecU8At A.repAlloc x.v x.cap x.ptr x.bs),
    ← A.pool_of_vmPreserved hvmp0]
  have hle_k : x.bs.length + (encodeVarint ((2#32 ||| (x.tag <<< 3)).zeroExtend 64)).length ≤
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length := by omega
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1 hinv1; rw [← A.pool_of_vmPreserved hvmp1]
    refine step_msg48_encode_varint_det_call_placed A lim hencVarint
      ((2#32 ||| (x.tag <<< 3)).zeroExtend 64) x.v x.cap x.ptr sp ((blkPl_453).base + 44#64) x.bs
      (M.stepEvents [] st0) (by omega) (inv0.fits_varint hle_k)
      (F := msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (cs_step hcs1 hinv1) (by dsimp only [AllocCostModel.stepEvents]; sep_ac_rfl) ?_
    intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge01 hpres01 hcap01_eq
    have inv01 := inv0.step_varint hle_k hcap01_eq
    set evs01 := ([] : List AllocEvent) ++ (pushBytesStep (encodeVarint ((2#32 ||| (x.tag <<< 3)).zeroExtend 64)).length x.cap.toNat x.bs.length).2
    have hev01 : M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk ((2#32 ||| (x.tag <<< 3)).zeroExtend 64) x.v x.cap x.ptr x.bs))
        (M.stepEvents [] st0) = M.stepEvents evs01 st0 := by
      simp only [evs01, encodeVarintEvents, pushBytesStep_snd_eq, List.nil_append, AllocCostModel.stepEvents, List.foldl_nil]
    rw [hev01]
    have hx19_2 : s2.readReg64 .x19 = x.v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64 := by rw [hcs12.2.1]; simp only [arm64_norm, *]
    have hx21_2 : s2.readReg64 .x21 = x.p.maxJump.zeroExtend 64 := by rw [hcs12.2.2.1]; simp only [arm64_norm, *]
    refine step_chainParams_len_placed H x.p x.v sp hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hcs2 ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hx21_3 hcs3 hvmp2
    rw [← A.pool_of_vmPreserved hvmp2]
    set bsK := x.bs ++ encodeVarint ((2#32 ||| (x.tag <<< 3)).zeroExtend 64)
    have hfit_len : bsK.length + (encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length)).length ≤ cap01.toNat ∨
        bsK.length + 10 < 2 ^ 62 := by
      rw [List.length_append]
      rcases hfit_hdr with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    have hle_len : bsK.length + (encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length)).length ≤
        x.bs.length + (encodeChainParamsMsg x.tag x.p).length := by rw [List.length_append]; omega
    cases hmo : (x.p.maxOooKeys == 0#32)
    · simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc3
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp3 hinv3; rw [← A.pool_of_vmPreserved hvmp3]
        refine step_msg48_encode_varint_det_call_placed A lim hencVarint
          (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length) x.v cap01 ptr01 sp ((blkPl_453).base + 120#64)
          bsK (M.stepEvents evs01 st0) hfit_len (inv01.fits_varint hle_len)
          (F := msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
        intro s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1 hcap1_eq
        have inv1 := inv01.step_varint hle_len hcap1_eq
        set evs1 := evs01 ++ (pushBytesStep (encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length)).length cap01.toNat bsK.length).2
        have hev1 : M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length) x.v cap01 ptr01 bsK))
            (M.stepEvents evs01 st0) = M.stepEvents evs1 st0 := by
          simp only [evs1, encodeVarintEvents, pushBytesStep_snd_eq, ← M.stepEvents_append]
        rw [hev1, bs0_append_chainParamsHeaderBytes x.bs x.tag x.p]
        have hx19_4 : s4.readReg64 .x19 = x.v := by rw [hcs34.1]; simp only [arm64_norm, *]
        have hx20_4 : s4.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64 := by rw [hcs34.2.1]; simp only [arm64_norm, *]
        have hx21_4 : s4.readReg64 .x21 = x.p.maxJump.zeroExtend 64 := by rw [hcs34.2.2.1]; simp only [arm64_norm, *]
        have hpc4' : s4.pc = (blkPl_453).base + (if x.p.maxOooKeys == 0#32 then 208#64 else 120#64) := by
          simp only [hmo, Bool.false_eq_true, ↓reduceIte, hpc4]
        refine step_chainParams_after_hdr_branch_placed H x.p x.v sp hpc4' hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4 ?_
        intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 hvmp4
        rw [← A.pool_of_vmPreserved hvmp4]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext s5 sv3 cap1 ptr1 evs1 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 (Nat.le_trans hge01 hge1) ?_ inv1)
        intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega); exact hpres1 (by rw [List.length_append]; omega))
    · simp only [hmo, ↓reduceIte] at hpc3
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp3 hinv3; rw [← A.pool_of_vmPreserved hvmp3]
        refine step_msg48_encode_varint_det_call_placed A lim hencVarint
          (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length) x.v cap01 ptr01 sp ((blkPl_453).base + 208#64)
          bsK (M.stepEvents evs01 st0) hfit_len (inv01.fits_varint hle_len)
          (F := msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
        intro s4 cap1 ptr1 hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge1 hpres1 hcap1_eq
        have inv1 := inv01.step_varint hle_len hcap1_eq
        set evs1 := evs01 ++ (pushBytesStep (encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length)).length cap01.toNat bsK.length).2
        have hev1 : M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length) x.v cap01 ptr01 bsK))
            (M.stepEvents evs01 st0) = M.stepEvents evs1 st0 := by
          simp only [evs1, encodeVarintEvents, pushBytesStep_snd_eq, ← M.stepEvents_append]
        rw [hev1, bs0_append_chainParamsHeaderBytes x.bs x.tag x.p]
        have hx19_4 : s4.readReg64 .x19 = x.v := by rw [hcs34.1]; simp only [arm64_norm, *]
        have hx20_4 : s4.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64 := by rw [hcs34.2.1]; simp only [arm64_norm, *]
        have hx21_4 : s4.readReg64 .x21 = x.p.maxJump.zeroExtend 64 := by rw [hcs34.2.2.1]; simp only [arm64_norm, *]
        have hpc4' : s4.pc = (blkPl_453).base + (if x.p.maxOooKeys == 0#32 then 208#64 else 120#64) := by
          simp only [hmo, ↓reduceIte, hpc4]
        refine step_chainParams_after_hdr_branch_placed H x.p x.v sp hpc4' hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4 ?_
        intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 hvmp4
        rw [← A.pool_of_vmPreserved hvmp4]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext s5 sv3 cap1 ptr1 evs1 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 (Nat.le_trans hge01 hge1) ?_ inv1)
        intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega); exact hpres1 (by rw [List.length_append]; omega)))

private theorem step_maxJump_1_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_453 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hres212 : CpReserve1Stepper resStack A lim (lsProg_453 H) blkPl_453 212#64 228#64 s0)
    (x : EncodeChainParamsGhost) (st0 : M.σ) (curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (accEvs : List AllocEvent)
    (inv : ChainParamsBudgetInv M lim x st0 curCap.toNat accEvs)
    (hrem : curBs.length + (encodeUint32Field 1#32 x.p.maxJump).length ≤
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length)
    (hfit_mj : curBs.length + (encodeUint32Field 1#32 x.p.maxJump).length ≤ curCap.toNat ∨
      curBs.length + (encodeUint32Field 1#32 x.p.maxJump).length + 10 < 2 ^ 62)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + (if x.p.maxJump == 0#32 then 124#64 else 212#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx20 : s.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.p.maxJump.zeroExtend 64) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc x.v curCap curPtr curBs ∗
      A.pool lim (M.stepEvents accEvs st0) s ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64) (nextEvs : List AllocEvent),
      sm.pc = (blkPl_453).base + (if x.p.maxOooKeys == 0#32 then 264#64 else 128#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = x.v → sm.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeUint32Field 1#32 x.p.maxJump).length ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      ChainParamsBudgetInv M lim x st0 nextCap.toNat nextEvs →
      SepWPp (lsProg_453 H) ret sm
        ((vecU8At A.repAlloc x.v nextCap nextPtr (curBs ++ encodeUint32Field 1#32 x.p.maxJump) ∗
          A.pool lim (M.stepEvents nextEvs st0) sm ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp (lsProg_453 H) ret s P Q Qp := by
  cases hmj : (x.p.maxJump == 0#32)
  · simp only [hmj, Bool.false_eq_true, ↓reduceIte] at hpc
    obtain ⟨hlen_mj, hge2_mj⟩ := maxJump_field_len_of_ne_zero x.p hmj
    have hle1 : curBs.length + 1 ≤ x.bs.length + (encodeChainParamsMsg x.tag x.p).length := by omega
    refine hres212 x.v curCap curPtr sp curBs x.p (M.stepEvents accEvs st0) (by omega)
      (inv.fits_reserve1 hle1) hpc hrun hsp halign htr hx19 hx20 (fun _ => hx21) hcs hP ?_
    intro s1 cap01 ptr01 hpc1 hrun1 hsp1 htr1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1 hlt01 hge01 hpres01 hcap01_eq
    have hx21_1' := hx21_1 rfl; have inv01 := inv.step_reserve1 hle1 hcap01_eq
    set evs01 := accEvs ++ (reserveStep curCap.toNat curBs.length 1).2
    have hev01 : M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 (M.stepEvents accEvs st0) =
        M.stepEvents evs01 st0 := (M.stepEvents_append _ _ _).symm
    rw [hev01]
    refine step_chainParams_push_maxJump_tag_placed A.repAlloc H x.v cap01 ptr01 sp curBs x.p hlt01
      hpc1 hrun1 hsp1 htr1 hx1_1 hx19_1 hx20_1 hx21_1' hcs1
      (F := A.pool lim (M.stepEvents evs01 st0) s1 ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by sep_ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hx21_2 hcs2 hvmp1
    rw [← A.pool_of_vmPreserved hvmp1]
    have hfit_v : (curBs ++ [0x08#8]).length + (encodeVarint (x.p.maxJump.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x08#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_mj with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    have hle_v : (curBs ++ [0x08#8]).length + (encodeVarint (x.p.maxJump.zeroExtend 64)).length ≤
        x.bs.length + (encodeChainParamsMsg x.tag x.p).length := by rw [List.length_append, List.length_singleton]; omega
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp2 hinv2; rw [← A.pool_of_vmPreserved hvmp2]
      refine step_msg48_encode_varint_det_call_placed A lim hencVarint (x.p.maxJump.zeroExtend 64)
        x.v cap01 ptr01 sp ((blkPl_453).base + 260#64) (curBs ++ [0x08#8]) (M.stepEvents evs01 st0)
        hfit_v (inv01.fits_varint hle_v) (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (cs_step hcs2 hinv2) (by sep_ac_rfl) ?_
      intro s3 nextCap nextPtr hpc3 hrun3 hsp3 htr3 hcs23 hcs3 hge1 hpres1 hcap1_eq
      have inv1 := inv01.step_varint hle_v hcap1_eq
      set nextEvs := evs01 ++ (pushBytesStep (encodeVarint (x.p.maxJump.zeroExtend 64)).length cap01.toNat (curBs ++ [0x08#8]).length).2
      have hev1 : M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (x.p.maxJump.zeroExtend 64) x.v cap01 ptr01 (curBs ++ [0x08#8])))
          (M.stepEvents evs01 st0) = M.stepEvents nextEvs st0 := by
        simp only [nextEvs, encodeVarintEvents, pushBytesStep_snd_eq, ← M.stepEvents_append]
      rw [hev1, bs_append_maxJump_of_ne_zero curBs x.p hmj]
      have hx19_3 : s3.readReg64 .x19 = x.v := by rw [hcs23.1]; simp only [arm64_norm, *]
      have hx20_3 : s3.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64 := by rw [hcs23.2.1]; simp only [arm64_norm, *]
      have hpc3' : s3.pc = (blkPl_453).base + (if x.p.maxJump == 0#32 then 124#64 else 260#64) := by
        simp only [hmj, Bool.false_eq_true, ↓reduceIte, hpc3]
      refine step_chainParams_after_maxJump_branch_placed H x.p x.v sp hpc3' hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 ?_
      intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 hvmp3
      rw [← A.pool_of_vmPreserved hvmp3]
      refine hnext s4 nextCap nextPtr nextEvs hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 (Nat.le_trans hge01 hge1) ?_ inv1
      intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
      exact hpres1 (by rw [List.length_append, List.length_singleton]; omega))
  · subst hP
    refine step_chainParams_after_maxJump_branch_placed H x.p x.v sp
      (by simp only [hmj, ↓reduceIte] at hpc ⊢; exact hpc) hrun hsp htr hx19 hx20 hcs ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hvmp0
    rw [← A.pool_of_vmPreserved hvmp0, ← bs_append_maxJump_of_zero curBs x.p hmj]
    exact hnext s1 curCap curPtr accEvs hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) inv

private theorem step_tailcall_184_1_placed [LibsignalPlacement] {resStack : Nat} (hres96 : resStack + 96 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_453 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (val v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit_v : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits_v : FitsEvents M lim curSt (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + 184#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = s0.readReg64 .lr) (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v) (hcc : CalleeSavedPreserved s0 s) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeVarint val).length ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1 →
      Q sf ((vecU8At A.repAlloc v nextCap nextPtr (curBs ++ encodeVarint val) ∗
        A.pool lim (M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)) curSt) sf ∗
        stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_453 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hvmp hinv; rw [← A.pool_of_vmPreserved hvmp]
    exact step_msg48_encode_varint_det_tailcall_placed hres96 A lim hencVarint
      val v curCap curPtr sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
      (s0.readReg64 .x20) (s0.readReg64 .x19) curBs curSt hfit_v hfits_v (F := F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (calleeSavedPreserved_setPC_placed _ hcc) (msgEnc48CalleeSavedPlaced_setPC _ hcs hinv) rfl hnext)

private theorem step_maxOooKeys_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State)) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_453 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hres128 : CpReserve1Stepper resStack A lim (lsProg_453 H) blkPl_453 128#64 144#64 s0)
    (x : EncodeChainParamsGhost) (st0 : M.σ) (curCap curPtr sp sv3 : BitVec 64)
    (curBs : List (BitVec 8)) (accEvs : List AllocEvent)
    (inv : ChainParamsBudgetInv M lim x st0 curCap.toNat accEvs)
    (hrem : curBs.length + (encodeUint32Field 2#32 x.p.maxOooKeys).length ≤
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length)
    (hfit_mo : curBs.length + (encodeUint32Field 2#32 x.p.maxOooKeys).length ≤ curCap.toNat ∨
      curBs.length + (encodeUint32Field 2#32 x.p.maxOooKeys).length + 10 < 2 ^ 62)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_453).base + (if x.p.maxOooKeys == 0#32 then 264#64 else 128#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx20 : s.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (nextCap nextPtr : BitVec 64) (nextEvs : List AllocEvent),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → StepInv s0 sf → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeUint32Field 2#32 x.p.maxOooKeys).length ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      ChainParamsBudgetInv M lim x st0 nextCap.toNat nextEvs →
      Q sf ((vecU8At A.repAlloc x.v nextCap nextPtr (curBs ++ encodeUint32Field 2#32 x.p.maxOooKeys) ∗
        A.pool lim (M.stepEvents nextEvs st0) sf ∗ stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_453 H) (s0.readReg64 .lr) s P Q Qp := by
  have hres96 : resStack + 96 < 2 ^ 64 := by omega
  cases hmo : (x.p.maxOooKeys == 0#32)
  · simp only [hmo, Bool.false_eq_true, ↓reduceIte] at hpc
    obtain ⟨hlen_mo, hge2_mo⟩ := maxOooKeys_field_len_of_ne_zero x.p hmo
    have hle1 : curBs.length + 1 ≤ x.bs.length + (encodeChainParamsMsg x.tag x.p).length := by omega
    refine hres128 x.v curCap curPtr sp curBs x.p (M.stepEvents accEvs st0) (by omega)
      (inv.fits_reserve1 hle1) hpc hrun hsp halign htr hx19 hx20 (fun h => absurd h (by decide)) hcs
      (F := msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by rw [hP]; sep_ac_rfl) ?_
    intro s1 cap01 ptr01 hpc1 hrun1 hsp1 htr1 hx1_1 hx19_1 hx20_1 _ hcs1 hlt01 hge01 hpres01 hcap01_eq
    have inv01 := inv.step_reserve1 hle1 hcap01_eq
    set evs01 := accEvs ++ (reserveStep curCap.toNat curBs.length 1).2
    have hev01 : M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 (M.stepEvents accEvs st0) =
        M.stepEvents evs01 st0 := (M.stepEvents_append _ _ _).symm
    rw [hev01]
    refine step_chainParams_push_maxOooKeys_epilogue_placed A.repAlloc H x.v cap01 ptr01 sp sv3
      curBs x.p hlt01 hpc1 hrun1 hsp1 halign htr1 hx1_1 hx19_1 hx20_1 hcs1
      (F := A.pool lim (M.stepEvents evs01 st0) s1 ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by sep_ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hlr2 hx0_2 hx1_2 hcc2 hcs2 hvmp1
    rw [← A.pool_of_vmPreserved hvmp1]
    have hfit_v : (curBs ++ [0x10#8]).length + (encodeVarint (x.p.maxOooKeys.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x10#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_mo with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    have hle_v : (curBs ++ [0x10#8]).length + (encodeVarint (x.p.maxOooKeys.zeroExtend 64)).length ≤
        x.bs.length + (encodeChainParamsMsg x.tag x.p).length := by rw [List.length_append, List.length_singleton]; omega
    refine step_tailcall_184_1_placed hres96 A lim H hencVarint (x.p.maxOooKeys.zeroExtend 64)
      x.v cap01 ptr01 sp sv3 (curBs ++ [0x10#8]) (M.stepEvents evs01 st0) hfit_v (inv01.fits_varint hle_v)
      hpc2 hrun2 hsp2 halign htr2 hlr2 hx0_2 hx1_2 hcc2 hcs2 (F := F) (by sep_ac_rfl) ?_
    intro sf nextCap nextPtr hpcf hrunf hspf htrf hccf hcsf hge1 hpres1 hcap1_eq
    have inv1 := inv01.step_varint hle_v hcap1_eq
    set nextEvs := evs01 ++ (pushBytesStep (encodeVarint (x.p.maxOooKeys.zeroExtend 64)).length cap01.toNat (curBs ++ [0x10#8]).length).2
    have hev1 : M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk (x.p.maxOooKeys.zeroExtend 64) x.v cap01 ptr01 (curBs ++ [0x10#8])))
        (M.stepEvents evs01 st0) = M.stepEvents nextEvs st0 := by
      simp only [nextEvs, encodeVarintEvents, pushBytesStep_snd_eq, ← M.stepEvents_append]
    have hq := hnext sf nextCap nextPtr nextEvs hpcf hrunf hspf htrf hccf
      hcsf.2.2.2.2.2.2.2.2.1 (Nat.le_trans hge01 hge1) (by
        intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
        exact hpres1 (by rw [List.length_append, List.length_singleton]; omega)) inv1
    rwa [← bs_append_maxOooKeys_of_ne_zero curBs x.p hmo, ← hev1] at hq
  · simp only [hmo, ↓reduceIte] at hpc
    refine step_chainParams_epilogue_placed hres96 H sp sv3 hpc hrun hsp halign htr hcs
      (F := vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗ F)
      (by rw [hP]; sep_ac_rfl) ?_
    intro sf hpcf hrunf hspf htrf hccf hinvf hvmp0
    have hq := hnext sf curCap curPtr accEvs hpcf hrunf hspf htrf hccf hinvf (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) inv
    rw [bs_append_maxOooKeys_of_zero curBs x.p hmo, A.pool_of_vmPreserved hvmp0] at hq
    have hEq : stackAt sp (msgEnc48VarintStackOf resStack) ∗
        (vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗ F) =
        (vecU8At A.repAlloc x.v curCap curPtr curBs ∗ A.pool lim (M.stepEvents accEvs st0) s ∗
          stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F := by sep_ac_rfl
    rwa [hEq]

/-- Core placed execution theorem for Block `453` establishing `EncodeChainParamsEnv`. -/
theorem chainParams1_core_placed_ok [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    {x : EncodeChainParamsGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    {Qp : State → SepProp → Prop}
    (hencV : subroutine_ok (lsProg_453 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hres212 : CpReserve1Stepper resStack A lim (lsProg_453 H) blkPl_453 212#64 228#64 s0)
    (hres128 : CpReserve1Stepper resStack A lim (lsProg_453 H) blkPl_453 128#64 144#64 s0)
    (hpc : s0.pc = (blkPl_453).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeChainParamsSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp (lsProg_453 H) (s0.readReg64 .lr) s0 P
        (fun sf Q =>
          (sf.trace = s0.trace ∧
            ∃ evs cap' ptr',
              x.cap.toNat ≤ cap'.toNat ∧
              (x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat →
                cap' = x.cap ∧ ptr' = x.ptr) ∧
              EncodeChainParamsEnv x evs ∧
              Q = vecU8At A.repAlloc x.v cap' ptr' (x.bs ++ encodeChainParamsMsg x.tag x.p) ∗
                A.pool lim (M.stepEvents evs st0) sf ∗
                stackAt s0.sp (msgEnc48VarintStackOf resStack)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) Qp := by
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp_align
  have hres96 : resStack + 96 < 2 ^ 64 := by omega
  have hpre_pure := hpre; dsimp only [encodeChainParamsSpecOf] at hpre_pure
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
  obtain ⟨⟨hw0, hw1, hw2, hx3, _, _, hfit, hEnv⟩, hpre_mem⟩ := hpre_pure
  have hpre_rewritten : s0.mem ⊨ ((vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s0 ∗
      stackAt s0.sp (msgEnc48VarintStackOf resStack)) ∗ emp) ∗ R := by
    convert hpre_mem using 1; sep_ac_rfl
  refine ⟨_, hpre_rewritten, ?_⟩
  have hlen_split := encodeChainParamsMsg_len_split x.tag x.p
  have hfit_hdr : x.bs.length + (chainParamsHeaderBytes x.tag x.p).length ≤ x.cap.toNat ∨
      x.bs.length + (chainParamsHeaderBytes x.tag x.p).length + 10 < 2 ^ 62 := by
    rcases hfit with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
  refine step_hdr_1_placed hres96 A lim H hencV x st0 s0.sp (ChainParamsBudgetInv.init hEnv)
    hfit_hdr (F := emp) hpc hrun rfl halign rfl hw0 hw1 hw2 hx3
    (MsgEnc48CalleeSavedPlaced.refl s0) rfl rfl ?_
  intro s1 sv3 cap1 ptr1 evs1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hcs1 hge1 hpres1 inv1
  have hfit_mj : (x.bs ++ chainParamsHeaderBytes x.tag x.p).length +
      (encodeUint32Field 1#32 x.p.maxJump).length ≤ cap1.toNat ∨
      (x.bs ++ chainParamsHeaderBytes x.tag x.p).length +
        (encodeUint32Field 1#32 x.p.maxJump).length + 10 < 2 ^ 62 := by
    rw [List.length_append]
    rcases hfit with h | h
    · left; obtain ⟨rfl, _⟩ := hpres1 (by omega); omega
    · right; omega
  refine step_maxJump_1_placed A lim H hencV hres212 x st0 cap1 ptr1 s0.sp
    (x.bs ++ chainParamsHeaderBytes x.tag x.p) evs1 inv1
    (by rw [List.length_append]; omega) hfit_mj hpc1 hrun1 hsp1 halign htr1
    hx19_1 hx20_1 hx21_1 hcs1
    (F := msgEnc48SavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ emp)
    (by sep_ac_rfl) ?_
  intro s2 cap2 ptr2 evs2 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge2 hpres2 inv2
  have hfit_mo : ((x.bs ++ chainParamsHeaderBytes x.tag x.p) ++ encodeUint32Field 1#32 x.p.maxJump).length +
      (encodeUint32Field 2#32 x.p.maxOooKeys).length ≤ cap2.toNat ∨
      ((x.bs ++ chainParamsHeaderBytes x.tag x.p) ++ encodeUint32Field 1#32 x.p.maxJump).length +
        (encodeUint32Field 2#32 x.p.maxOooKeys).length + 10 < 2 ^ 62 := by
    rw [List.length_append, List.length_append]
    rcases hfit with h | h
    · left
      obtain ⟨rfl, _⟩ := hpres1 (by omega)
      obtain ⟨rfl, _⟩ := hpres2 (by rw [List.length_append]; omega)
      omega
    · right; omega
  refine step_maxOooKeys_1_placed hres A lim H hencV hres128 x st0 cap2 ptr2 s0.sp sv3
    ((x.bs ++ chainParamsHeaderBytes x.tag x.p) ++ encodeUint32Field 1#32 x.p.maxJump)
    evs2 inv2 (by rw [List.length_append, List.length_append]; omega) hfit_mo
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2 (F := emp) (by sep_ac_rfl) ?_
  intro sf cap3 ptr3 evs3 hpcf hrunf hspf htrf hccf _ hge3 hpres3 inv3
  refine ⟨⟨htrf, evs3, cap3, ptr3, Nat.le_trans hge1 (Nat.le_trans hge2 hge3), ?_,
    ⟨cap3.toNat, inv3.chain⟩, ?_⟩, hspf, hccf⟩
  · intro hle
    obtain ⟨rfl, rfl⟩ := hpres1 (by omega)
    obtain ⟨rfl, rfl⟩ := hpres2 (by rw [List.length_append]; omega)
    exact hpres3 (by rw [List.length_append, List.length_append]; omega)
  · rw [bs0_append_encodeChainParamsMsg x.bs x.tag x.p, sepConj_emp]

/-! ## 3. Public Relocatable Contracts on Block `453` -/

theorem encode_chainParams_1_placed_ok_of_callees [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)}
    (henc0 : subroutine_ok (lsProg_453 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_453 H) (lsmpl.base 460)
      (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim))) :
    subroutine_ok (lsProg_453 H) (blkPl_453).base
      (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf resStack A lim)) := by
  apply subroutine_ok_of_sepWPp; rintro ⟨x, st0⟩ R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hcl0, hpre⟩
  by_cases hspare : x.bs.length + (encodeChainParamsMsg x.tag x.p).length ≤ x.cap.toNat
  · have hpre_pure := hpre; dsimp only [encodeChainParamsSpecOf] at hpre_pure
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre_pure
    rcases hpre_pure with ⟨⟨hw0, hw1, hw2, hx3, ht1, ht2, _, _⟩, hmem⟩
    have hpreVac : s0.mem ⊨
        (encodeChainParamsSpecOf resStack (vmRecordBudget A s0) zeroEnforcedLimits).pre (x, ()) s0 ∗
          (A.pool lim st0 s0 ∗ R) := by
      dsimp only [encodeChainParamsSpecOf]
      rw [vmRecordBudget_pool_zeroEnforced, vmRecordBudget_repAlloc]
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hw0, hw1, hw2, hx3, ht1, ht2, Or.inl hspare,
        fitsEnv_vecU8EncodeEnv_of_spare noAllocCostModel zeroEnforcedLimits () hspare⟩, ?_⟩
      have hmem' : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗ (vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
          stackAt s0.sp (msgEnc48VarintStackOf resStack) ∗ A.pool lim st0 s0 ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨VmPreserved.refl s0, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'
    have hencVac : subroutine_ok (lsProg_453 H) (blkPl_451).base
        (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack (vmRecordBudget A s0) zeroEnforcedLimits)) :=
      ls_subroutine_ok_of_block (callerProg := lsProg_453 H)
        (encodeVarint2_det_placed_ok_of_doReserve (by omega) (vmRecordBudget A s0) zeroEnforcedLimits H
          (vacuous_doReserve2_placed_ok (vmRecordBudget A s0)))
    obtain ⟨P, hP, hwp⟩ := chainParams1_core_placed_ok (Qp := fun _ _ => False) hres
      (vmRecordBudget A s0) zeroEnforcedLimits H
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencVac)
      (step_reserve_212_1_placed hres (vmRecordBudget A s0) zeroEnforcedLimits
        (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (vacuous_doReserve2_placed_ok (vmRecordBudget A s0))))
      (step_reserve_128_1_placed hres (vmRecordBudget A s0) zeroEnforcedLimits
        (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (vacuous_doReserve2_placed_ok (vmRecordBudget A s0))))
      hpc hrun hpreVac hsp
    refine ⟨P, A.pool lim st0 s0 ∗ R, hP, sepWPp_mono_post hwp ?_ (fun _ _ h => h.elim)⟩
    rintro sf Qf ⟨⟨htrf, _, cap', ptr', _, hpres, _, rfl⟩, hspf, hccf⟩
    rcases hpres hspare with ⟨rfl, rfl⟩
    refine ⟨fun hmQ => ?_, hspf, hccf⟩
    have hmQ' : sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗
        (vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ encodeChainParamsMsg x.tag x.p) ∗
          A.pool lim st0 s0 ∗ stackAt s0.sp (msgEnc48VarintStackOf resStack) ∗ R) := by
      rw [vmRecordBudget_pool_zeroEnforced, vmRecordBudget_repAlloc] at hmQ
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmQ
    rw [satisfies_pure_sepConj] at hmQ'; rcases hmQ' with ⟨hvm, hmRest⟩
    rw [← A.pool_of_vmPreserved hvm] at hmRest
    exact satisfies_encodeChainParams_post A lim x st0 s0 sf R x.cap x.ptr [] htrf
      (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (VecU8EncodeEnv.nil _ _) (fun _ => ⟨rfl, hvm⟩) hmRest
  · obtain ⟨P, hP, hwp⟩ := chainParams1_core_placed_ok (Qp := fun _ _ => False) hres A lim H
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 henc0)
      (step_reserve_212_1_placed hres A lim (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0))
      (step_reserve_128_1_placed hres A lim (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0))
      hpc hrun hpre hsp
    refine ⟨P, R, hP, sepWPp_mono_post hwp ?_ (fun _ _ h => h.elim)⟩
    rintro sf Qf ⟨⟨htrf, evs, cap', ptr', hge, hpres, hEnv, rfl⟩, hspf, hccf⟩
    refine ⟨fun hmQ => ?_, hspf, hccf⟩
    exact satisfies_encodeChainParams_post A lim x st0 s0 sf R cap' ptr' evs htrf hge hpres hEnv
      (fun h => absurd h hspare) (by simpa only [sepConj_assoc] using hmQ)

theorem encode_chainParams_1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams1PlacedOk A lim H :=
  encode_chainParams_1_placed_ok_of_callees (resStack := doReserveStack) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_453 H) (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_453 H) (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_chainParams_1_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams1PlacedOkX A lim H :=
  encode_chainParams_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_453 H) (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_453 H) (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))

theorem encode_chainParams_1_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams1PlacedOkExt A lim ext :=
  encode_chainParams_1_placed_ok h_panic
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustNoAllocShimSym]) hshim)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustAllocSym]) halloc)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustReallocSym]) hrealloc)

theorem encode_chainParams_1_placed_ok_ext_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams1PlacedOkExtX A lim ext :=
  encode_chainParams_1_placed_ok_x h_panic
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustNoAllocShimSym]) hshim)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustAllocSym]) halloc)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustReallocSym]) hrealloc)

theorem encode_chainParams_1_placed_ok_withPanics [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams1PlacedOkExt A lim ext :=
  encode_chainParams_1_placed_ok h_panic hshim halloc hrealloc

theorem encode_chainParams_1_placed_ok_withPanics_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat (Rust.withPanics ext) spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat (Rust.withPanics ext) spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat (Rust.withPanics ext) spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams1PlacedOkExtX A lim ext :=
  encode_chainParams_1_placed_ok_x h_panic hshim halloc hrealloc

theorem encode_chainParams_1_exact_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (H : String → Option (State → State)) :
    EncodeChainParams1ExactPlacedOk resStack A H := by
  apply subroutine_ok_of_sepWPp; intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨hcl0, hpre⟩
  dsimp only [encodeChainParamsExactVmSpecOf] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hw0, hw1, hw2, hx3, ht1, ht2, hspare⟩, hmem⟩
  have hpreVac : s0.mem ⊨
      (encodeChainParamsSpecOf resStack (rawVmRecordBudget A hblk s0) zeroEnforcedLimits).pre (x, ()) s0 ∗ R := by
    dsimp only [encodeChainParamsSpecOf]
    rw [rawVmRecordBudget_pool_zeroEnforced, vecU8At_rawVmRecordBudget]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hw0, hw1, hw2, hx3, ht1, ht2, Or.inl hspare,
      fitsEnv_vecU8EncodeEnv_of_spare noAllocCostModel zeroEnforcedLimits () hspare⟩, ?_⟩
    have hmem' : s0.mem ⊨ ⌜VmPreserved s0 s0⌝ ∗
        (vecU8At A x.v x.cap x.ptr x.bs ∗ stackAt s0.sp (msgEnc48VarintStackOf resStack) ∗ R) := by
      rw [satisfies_pure_sepConj]
      exact ⟨VmPreserved.refl s0, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem'
  have hencVac : subroutine_ok (lsProg_453 H) (blkPl_451).base
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack (rawVmRecordBudget A hblk s0) zeroEnforcedLimits)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_453 H)
      (encodeVarint2_det_placed_ok_of_doReserve (by omega) (rawVmRecordBudget A hblk s0) zeroEnforcedLimits H
        (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0)))
  obtain ⟨P, hP, hwp⟩ := chainParams1_core_placed_ok (Qp := fun _ _ => False) hres
    (rawVmRecordBudget A hblk s0) zeroEnforcedLimits H
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hencVac)
    (step_reserve_212_1_placed hres (rawVmRecordBudget A hblk s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0))))
    (step_reserve_128_1_placed hres (rawVmRecordBudget A hblk s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0))))
    hpc hrun hpreVac hsp
  refine ⟨P, R, hP, sepWPp_mono_post hwp ?_ (fun _ _ h => h.elim)⟩
  rintro sf Qf ⟨⟨htrf, _, cap', ptr', _, hpres, _, rfl⟩, hspf, hccf⟩
  rcases hpres hspare with ⟨rfl, rfl⟩
  refine ⟨fun hmQ => ?_, hspf, hccf⟩
  have hmQ' : sf.mem ⊨ ⌜VmPreserved s0 sf⌝ ∗
      (vecU8At A x.v x.cap x.ptr (x.bs ++ encodeChainParamsMsg x.tag x.p) ∗
        stackAt s0.sp (msgEnc48VarintStackOf resStack) ∗ R) := by
    rw [rawVmRecordBudget_pool_zeroEnforced, vecU8At_rawVmRecordBudget] at hmQ
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmQ
  rw [satisfies_pure_sepConj] at hmQ'; rcases hmQ' with ⟨hvm, hmRest⟩
  dsimp only [withLsCodeLoaded, encodeChainParamsExactVmSpecOf]
  simp only [sepConj_assoc]; rw [satisfies_pure_sepConj]
  exact ⟨⟨hvm, htrf⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmRest⟩

theorem encode_chainParams_1_exact_cli_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) (A : RustCliAlloc)
    (H : String → Option (State → State)) :
    EncodeChainParams1ExactPlacedOk resStack A.repAlloc H :=
  encode_chainParams_1_exact_placed_ok hres A.repAlloc A.block_valid H

/-- Exact-capacity `encodeChainParamsExactSpecOf` contract on Block `453` (`doReserveStack`). -/
theorem etv_encodeChainParams_1_exact_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_453 H) (blkPl_453).base
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStack A lim)) :=
  etv_encodeChainParams_exact_of_lscl (by decide)
    (encode_chainParams_1_placed_ok h_panic hshim halloc hrealloc)

/-- Exact-capacity `encodeChainParamsExactSpecOf` contract on Block `453` (`doReserveStackX`). -/
theorem etv_encodeChainParams_1_exact_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_453 H) (blkPl_453).base
      (withLsCodeLoaded lsmpl (encodeChainParamsExactSpecOf doReserveStackX A lim)) :=
  etv_encodeChainParams_exact_of_lscl (by decide)
    (encode_chainParams_1_placed_ok_x h_panic hshim halloc hrealloc)

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.ChainParams1PlacedBudget
