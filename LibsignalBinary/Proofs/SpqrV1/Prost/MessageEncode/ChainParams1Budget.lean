/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams1
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated1Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Verification of `ChainParams::encode [local#1]` (`Block 150`)

Defines the running event-chain invariant `ChainParamsBudgetInv`, proves the shared relocatable
core theorem `chainParams_core_placed_ok` for Blocks `150` and `313`, and instantiates the
budget-threaded `[LibsignalPlacement]` contracts for `ChainParams::encode [local#1]` (`Block 150`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams1Budget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents
  RustCliAlloc RustCliAllocBudget RustLayoutOk VmPreserved fitsEvents_append rustAllocEvents
  rustReallocEvents zeroBudgetLimits rustCliAllocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement blkPC_148 blkPC_150 blkPC_292 blkPC_313
  blkPl_148 blkPl_150 blkPl_150_ρ blkPl_157 blkPl_292 blkPl_313 blkPl_313_ρ lsProg_148 lsProg_150
  lsProg_157 lsProg_313 ls_resolve_blk_148 ls_resolve_blk_157 ls_resolve_blk_292
  ls_subroutine_ok_of_block lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalSpqrV1 (ChainParamsPB ChainParamsPB.encodeRaw)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeUint32Field)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall doReserveStack doReserveStackX reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost StepInv)
open CryptoVerification.SpqrV1.Alloc (spqrHandleErrorSym spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen (noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64 ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
  vecU8At_eq_header_sep_buf zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode (EncodeChainParamsGhost MsgEnc48CalleeSavedPlaced
  bs0_append_chainParamsHeaderBytes bs0_append_encodeChainParamsMsg bs_append_maxJump_of_ne_zero
  bs_append_maxJump_of_zero bs_append_maxOooKeys_of_ne_zero bs_append_maxOooKeys_of_zero
  calleeSavedPreserved_setPC_placed cap_toNat_eq_of_beq chainParamsHeaderBytes
  chainParamsHeaderBytes_len_bounds chainParamsHeaderBytes_len_eq encodeChainParamsMsg
  encodeChainParamsMsg_len_split lt_cap_toNat_of_beq_false maxJump_field_len_of_ne_zero
  maxOooKeys_field_len_of_ne_zero msgEnc48CalleeSavedPlaced_setPC msgEnc48SavedFrame
  msgEnc48VarintStackOf reserveCap_one_bounds subroutine_ok_withMsgEnc48CSPlaced_placed
  subroutine_ok_withMsgEnc48CSPlaced_placed_blk withMsgEnc48CSPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents fitsEnv_doReserve_iff noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (encodeVarintEvents)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf doReserveSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2BaseBudget (do_reserve2_placed_ok do_reserve2_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget (encodeVarintDetSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated1Budget
  (encodeVarint2_det_placed_ok_of_doReserve encode_varint2_det_placed_ok encode_varint2_det_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget (pushBytesStep pushBytesStep_snd_eq
  reserveStep reserveStep_of_need reserveStep_of_need_doReserveEvents reserveStep_of_spare
  reserveStep_one_eq_pushByteStep sepWP_done_tpidr_placed sepWP_done_vm_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
  (step_msg48_do_reserve2_call_placed step_msg48_encode_varint_det_call_placed
   step_msg48_encode_varint_det_tailcall_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBaseBudget
  (EncodeChainParamsEnv VecU8EncodeEnv VecU8ReserveChain encodeChainParamsExactVmSpecOf
   encodeChainParamsSpec encodeChainParamsSpecOf encodeChainParamsSpecX fitsEnv_vecU8EncodeEnv_of_spare)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBasePlacedBudget
  (EncodeChainParams150ExactPlacedOk EncodeChainParams150PlacedOk EncodeChainParams150PlacedOkExt
   EncodeChainParams150PlacedOkExtX EncodeChainParams150PlacedOkX IsChainParamsEncodePlacedBase
   IsChainParamsEncodePlacedProg step_chainParams_after_hdr_branch_placed
   step_chainParams_after_maxJump_branch_placed step_chainParams_epilogue_placed
   step_chainParams_len_placed step_chainParams_prologue_placed
   step_chainParams_push_maxJump_tag_placed step_chainParams_push_maxOooKeys_epilogue_placed)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32 ProofLib.truncate32_ofNat64 zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm] private theorem bv_pc_add_sub_cancel (a b : BitVec 64) : a + (b - a) = b := by bv_omega
@[local arm64_norm] private theorem bv_pc_rel_target (b k t : BitVec 64) : b + k + (t - b - k) = t := by bv_omega

local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(CryptoVerification.SpqrV1.Prost.MessageEncode.MsgEnc48CalleeSavedPlaced.step $hcs
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) $hinv)

/-! ## 1. Zero-Allocation `VmPreserved` Budget Adapters & `ChainParamsBudgetInv` -/

abbrev noAllocCostModel : AllocCostModel where
  σ := Unit; init := (); step := fun _ _ => (); footprint := fun _ => 0; maxDynIvs := fun _ => 0
  stepReserve := fun ev _ => ev.reqBytes + 1; liveBytes := fun _ => 0
  footprint_mono := fun _ _ => Nat.le_refl 0; maxDynIvs_mono := fun _ _ => Nat.le_refl 0
  stepReserve_mono := fun _ _ _ => Nat.le_refl _; req_le_stepReserve := fun _ _ => Nat.le_succ _
  liveBytes_free_le := fun _ _ _ => Nat.le_refl 0

def zeroEnforcedLimits : BudgetLimits :=
  { staticCount := 0, staticBytes := 0, physCap := 0, enforced := true }

def rawVmRecordBudget (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (s0 : State) : RustCliAllocBudget noAllocCostModel where
  pool := fun lim _ s => if lim.enforced then ⌜VmPreserved s0 s⌝ else emp
  live := A.live; block_valid := hblk
  pool_transport := by
    intro lim _ s s' hvm; split_ifs
    · exact congrArg SepProp.pure (propext ⟨fun h => h.trans hvm.symm, fun h => h.trans hvm⟩)
    · rfl
  pool_zero_transport := by intro _ _ _ _; dsimp only [zeroBudgetLimits]; simp only [Bool.false_eq_true, ↓reduceIte]
abbrev vmRecordBudget {M : AllocCostModel} (A : RustCliAllocBudget M) (s0 : State) :
    RustCliAllocBudget noAllocCostModel := rawVmRecordBudget A.repAlloc A.block_valid s0
@[simp] theorem vmRecordBudget_repAlloc {M : AllocCostModel} (A : RustCliAllocBudget M) (s0 : State) :
    (vmRecordBudget A s0).repAlloc = A.repAlloc := rfl
@[simp] theorem vecU8At_rawVmRecordBudget (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢ ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (s0 : State) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At (rawVmRecordBudget A hblk s0).repAlloc v cap ptr bs = vecU8At A v cap ptr bs := rfl
@[simp] theorem rawVmRecordBudget_pool_zeroEnforced (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢ ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (s0 s : State) (st : noAllocCostModel.σ) :
    (rawVmRecordBudget A hblk s0).pool zeroEnforcedLimits st s = ⌜VmPreserved s0 s⌝ := rfl
@[simp] theorem vmRecordBudget_pool_zeroEnforced {M : AllocCostModel} (A : RustCliAllocBudget M)
    (s0 s : State) (st : noAllocCostModel.σ) :
    (vmRecordBudget A s0).pool zeroEnforcedLimits st s = ⌜VmPreserved s0 s⌝ := rfl
theorem not_fitsEvent_zeroEnforcedLimits (ev : AllocEvent) :
    ¬ FitsEvent noAllocCostModel zeroEnforcedLimits () ev := by
  rintro ⟨_, _, hram, _⟩; dsimp only [noAllocCostModel, zeroEnforcedLimits] at hram; omega
theorem not_fitsEvents_zeroEnforcedLimits_doReserve (d : DoReserveCall) :
    ¬ FitsEvents noAllocCostModel zeroEnforcedLimits () (doReserveEvents d) := by
  dsimp only [doReserveEvents, rustAllocEvents, rustReallocEvents]
  split_ifs <;> intro h <;> exact not_fitsEvent_zeroEnforcedLimits _ h.1

theorem vacuous_doReserve2_placed_ok [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {resStack : Nat} (B : RustCliAllocBudget noAllocCostModel) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack B zeroEnforcedLimits)) := by
  refine subroutine_ok_outcome_intro fun ⟨d, st⟩ R s _ _ hpre _ => ?_
  dsimp only [withLsCodeLoaded, doReserve2SpecOf] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨_, hpre⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, _, _, _, hEnv⟩, _⟩; cases st
  exact False.elim (not_fitsEvents_zeroEnforcedLimits_doReserve d ((fitsEnv_doReserve_iff d).mp hEnv))

theorem vacuous_doReserve7_placed_ok [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {resStack : Nat} (B : RustCliAllocBudget noAllocCostModel) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (doReserveSpecOf resStack B zeroEnforcedLimits)) := by
  refine subroutine_ok_outcome_intro fun ⟨d, st⟩ R s _ _ hpre _ => ?_
  dsimp only [withLsCodeLoaded, doReserveSpecOf] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨_, hpre⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_, _, _, _, _, _, hEnv⟩, _⟩; cases st
  exact False.elim (not_fitsEvents_zeroEnforcedLimits_doReserve d ((fitsEnv_doReserve_iff d).mp hEnv))

theorem vecU8ReserveChain_reserveStep {cap len additional finalLen : Nat}
    (hle : len + additional ≤ finalLen) :
    VecU8ReserveChain cap (reserveStep cap len additional).1 finalLen
      (reserveStep cap len additional).2 := by
  by_cases h : len + additional ≤ cap
  · rw [reserveStep_of_spare h]; exact .nil cap finalLen
  · rw [reserveStep_of_need h]; exact VecU8ReserveChain.single_reserve (by omega) hle

theorem vecU8ReserveChain_pushBytesStep :
    ∀ (n cap len finalLen : Nat), len + n ≤ finalLen →
      VecU8ReserveChain cap (pushBytesStep n cap len).1 finalLen (pushBytesStep n cap len).2
  | 0, cap, _, finalLen, _ => .nil cap finalLen
  | n + 1, cap, len, finalLen, hle => by
    dsimp only [pushBytesStep]
    rw [← reserveStep_one_eq_pushByteStep]
    exact (vecU8ReserveChain_reserveStep (finalLen := finalLen) (by omega)).trans (Nat.le_refl _)
      (vecU8ReserveChain_pushBytesStep n _ (len + 1) finalLen (by omega))

/-- Running allocator event-chain invariant across `encode<ChainParams>`. -/
structure ChainParamsBudgetInv (M : AllocCostModel) (lim : BudgetLimits)
    (x : EncodeChainParamsGhost) (st0 : M.σ) (curCap : Nat) (accEvs : List AllocEvent) : Prop where
  fitsEnv : FitsEnv M lim st0 (EncodeChainParamsEnv x)
  chain : VecU8ReserveChain x.cap.toNat curCap
    (x.bs.length + (encodeChainParamsMsg x.tag x.p).length) accEvs

theorem ChainParamsBudgetInv.init {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeChainParamsGhost} {st0 : M.σ}
    (hEnv : FitsEnv M lim st0 (EncodeChainParamsEnv x)) :
    ChainParamsBudgetInv M lim x st0 x.cap.toNat [] :=
  ⟨hEnv, .nil _ _⟩

theorem ChainParamsBudgetInv.fits_varint {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeChainParamsGhost} {st0 : M.σ} {curCap curPtr val : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent}
    (inv : ChainParamsBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + (encodeVarint val).length ≤
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length) :
    FitsEvents M lim (M.stepEvents accEvs st0)
      (encodeVarintEvents (EncodeVarintGhost.mk val x.v curCap curPtr curBs)) := by
  have hstep := vecU8ReserveChain_pushBytesStep (encodeVarint val).length curCap.toNat curBs.length _ hle
  have hall := inv.fitsEnv _ ⟨_, inv.chain.trans (Nat.le_refl _) hstep⟩
  have h2 := ((fitsEvents_append M lim accEvs _ st0).mp hall).2
  simpa only [encodeVarintEvents, pushBytesStep_snd_eq] using h2

theorem ChainParamsBudgetInv.step_varint {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeChainParamsGhost} {st0 : M.σ} {curCap nextCap val : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent}
    (inv : ChainParamsBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + (encodeVarint val).length ≤
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length)
    (hcap_eq : nextCap.toNat = (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).1) :
    ChainParamsBudgetInv M lim x st0 nextCap.toNat
      (accEvs ++ (pushBytesStep (encodeVarint val).length curCap.toNat curBs.length).2) := by
  have hstep := vecU8ReserveChain_pushBytesStep (encodeVarint val).length curCap.toNat curBs.length _ hle
  rw [← hcap_eq] at hstep
  exact ⟨inv.fitsEnv, inv.chain.trans (Nat.le_refl _) hstep⟩

theorem ChainParamsBudgetInv.fits_reserve1 {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeChainParamsGhost} {st0 : M.σ} {curCap : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent}
    (inv : ChainParamsBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + 1 ≤ x.bs.length + (encodeChainParamsMsg x.tag x.p).length) :
    FitsEvents M lim (M.stepEvents accEvs st0) (reserveStep curCap.toNat curBs.length 1).2 := by
  have hstep := vecU8ReserveChain_reserveStep (cap := curCap.toNat) hle
  have hall := inv.fitsEnv _ ⟨_, inv.chain.trans (Nat.le_refl _) hstep⟩
  exact ((fitsEvents_append M lim accEvs _ st0).mp hall).2

theorem ChainParamsBudgetInv.step_reserve1 {M : AllocCostModel} {lim : BudgetLimits}
    {x : EncodeChainParamsGhost} {st0 : M.σ} {curCap nextCap : BitVec 64}
    {curBs : List (BitVec 8)} {accEvs : List AllocEvent}
    (inv : ChainParamsBudgetInv M lim x st0 curCap.toNat accEvs)
    (hle : curBs.length + 1 ≤ x.bs.length + (encodeChainParamsMsg x.tag x.p).length)
    (hcap_eq : nextCap.toNat = (reserveStep curCap.toNat curBs.length 1).1) :
    ChainParamsBudgetInv M lim x st0 nextCap.toNat
      (accEvs ++ (reserveStep curCap.toNat curBs.length 1).2) := by
  have hstep := vecU8ReserveChain_reserveStep (cap := curCap.toNat) hle
  rw [← hcap_eq] at hstep
  exact ⟨inv.fitsEnv, inv.chain.trans (Nat.le_refl _) hstep⟩

theorem extract_vecU8At_bounds {prog : Program} {ret : BitVec 64} {s : State}
    (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) {F P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm' : s.mem ⊨ ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ F ∗ R) := by
    rw [hP, vecU8At] at hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  rw [satisfies_pure_sepConj] at hm'
  exact h hm'.1.1 hm'.1.2.1 hm'.1.2.2 R hm hL

/-! ## 2. Shared Relocatable Steppers for Blocks `150` & `313` -/

/-- Relocatable base program with `varint` callee entry for Blocks `150` and `313`. -/
def IsCpPlacedBase (P_blk : Program) (pl : Placement) (varint_pc : BitVec 64) : Prop :=
  (∃ (inst : LibsignalPlacement), P_blk = @blkPC_150 inst ∧ pl = @blkPl_150 inst ∧
    varint_pc = (@blkPl_148 inst).base) ∨
  (∃ (inst : LibsignalPlacement), P_blk = @blkPC_313 inst ∧ pl = @blkPl_313 inst ∧
    varint_pc = (@blkPl_292 inst).base)

/-- Relocatable rebased program with `varint` callee entry for Blocks `150` and `313`. -/
def IsCpPlacedProg (prog : Program) (pl : Placement) (varint_pc : BitVec 64) : Prop :=
  ∃ P_blk H, prog = P_blk.rebase pl.base H ∧ IsCpPlacedBase P_blk pl varint_pc

theorem IsCpPlacedBase.toEncodePlacedBase {P_blk : Program} {pl : Placement} {varint_pc : BitVec 64}
    (h : IsCpPlacedBase P_blk pl varint_pc) : IsChainParamsEncodePlacedBase P_blk pl := by
  rcases h with ⟨inst, rfl, rfl, _⟩ | ⟨inst, rfl, rfl, _⟩
  · exact Or.inl ⟨inst, rfl, rfl⟩
  · exact Or.inr ⟨inst, rfl, rfl⟩

theorem IsCpPlacedProg.toEncodePlacedProg {prog : Program} {pl : Placement} {varint_pc : BitVec 64}
    (h : IsCpPlacedProg prog pl varint_pc) : IsChainParamsEncodePlacedProg prog pl := by
  rcases h with ⟨P_blk, H, rfl, hbase⟩
  exact ⟨P_blk, H, rfl, hbase.toEncodePlacedBase⟩

theorem isCpPlacedProg_150 [LibsignalPlacement] (H : String → Option (State → State)) :
    IsCpPlacedProg (lsProg_150 H) blkPl_150 (blkPl_148).base :=
  ⟨blkPC_150, H, rfl, Or.inl ⟨‹_›, rfl, rfl, rfl⟩⟩

theorem isCpPlacedProg_313 [LibsignalPlacement] (H : String → Option (State → State)) :
    IsCpPlacedProg (lsProg_313 H) blkPl_313 (blkPl_292).base :=
  ⟨blkPC_313, H, rfl, Or.inr ⟨‹_›, rfl, rfl, rfl⟩⟩

theorem cpPlaced_fetch_bl_varint {P_blk : Program} {pl : Placement} {varint_pc : BitVec 64}
    (hbase : IsCpPlacedBase P_blk pl varint_pc) (H : String → Option (State → State)) {k : Nat}
    (h150 : ∀ [LibsignalPlacement],
      ((blkPC_150).rebase (blkPl_150).base H).fetch ((blkPl_150).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_150).ρ "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" -
          (blkPl_150).base - BitVec.ofNat 64 k)))
    (h313 : ∀ [LibsignalPlacement],
      ((blkPC_313).rebase (blkPl_313).base H).fetch ((blkPl_313).base + BitVec.ofNat 64 k) =
        some (Instr.bl ((blkPl_313).ρ "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" -
          (blkPl_313).base - BitVec.ofNat 64 k))) :
    (P_blk.rebase pl.base H).fetch (pl.base + BitVec.ofNat 64 k) =
      some (Instr.bl (varint_pc - (pl.base + BitVec.ofNat 64 k))) := by
  rcases hbase with ⟨inst, rfl, rfl, rfl⟩ | ⟨inst, rfl, rfl, rfl⟩
  · letI := inst; have h := @h150 inst
    simp only [blkPl_150_ρ, ls_resolve_blk_148] at h
    have heq : lsmpl.base 148 - (blkPl_150).base - BitVec.ofNat 64 k =
        (blkPl_148).base - ((blkPl_150).base + BitVec.ofNat 64 k) := by
      change (blkPl_148).base - (blkPl_150).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h
  · letI := inst; have h := @h313 inst
    simp only [blkPl_313_ρ, ls_resolve_blk_292] at h
    have heq : lsmpl.base 292 - (blkPl_313).base - BitVec.ofNat 64 k =
        (blkPl_292).base - ((blkPl_313).base + BitVec.ofNat 64 k) := by
      change (blkPl_292).base - (blkPl_313).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

theorem cpPlaced_fetch_b_varint {P_blk : Program} {pl : Placement} {varint_pc : BitVec 64}
    (hbase : IsCpPlacedBase P_blk pl varint_pc) (H : String → Option (State → State)) {k : Nat}
    (h150 : ∀ [LibsignalPlacement],
      ((blkPC_150).rebase (blkPl_150).base H).fetch ((blkPl_150).base + BitVec.ofNat 64 k) =
        some (Instr.b ((blkPl_150).ρ "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#2]" -
          (blkPl_150).base - BitVec.ofNat 64 k)))
    (h313 : ∀ [LibsignalPlacement],
      ((blkPC_313).rebase (blkPl_313).base H).fetch ((blkPl_313).base + BitVec.ofNat 64 k) =
        some (Instr.b ((blkPl_313).ρ "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" -
          (blkPl_313).base - BitVec.ofNat 64 k))) :
    (P_blk.rebase pl.base H).fetch (pl.base + BitVec.ofNat 64 k) =
      some (Instr.b (varint_pc - (pl.base + BitVec.ofNat 64 k))) := by
  rcases hbase with ⟨inst, rfl, rfl, rfl⟩ | ⟨inst, rfl, rfl, rfl⟩
  · letI := inst; have h := @h150 inst
    simp only [blkPl_150_ρ, ls_resolve_blk_148] at h
    have heq : lsmpl.base 148 - (blkPl_150).base - BitVec.ofNat 64 k =
        (blkPl_148).base - ((blkPl_150).base + BitVec.ofNat 64 k) := by
      change (blkPl_148).base - (blkPl_150).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h
  · letI := inst; have h := @h313 inst
    simp only [blkPl_313_ρ, ls_resolve_blk_292] at h
    have heq : lsmpl.base 292 - (blkPl_313).base - BitVec.ofNat 64 k =
        (blkPl_292).base - ((blkPl_313).base + BitVec.ofNat 64 k) := by
      change (blkPl_292).base - (blkPl_313).base - BitVec.ofNat 64 k = _; bv_omega
    rwa [heq] at h

/-- Type of the 1-byte capacity reservation stepper at offset `off` (`212 → 228` or `128 → 144`). -/
def CpReserve1Stepper {M : AllocCostModel} (resStack : Nat) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (prog : Program) (pl : Placement) (off retOff : BitVec 64)
    (s0 : State) : Prop :=
  ∀ (v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (p : ChainParamsPB) (curSt : M.σ),
    (curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62) →
    FitsEvents M lim curSt (reserveStep curCap.toNat curBs.length 1).2 →
    ∀ {s : State} {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop},
      s.pc = pl.base + off → s.status = .Running → s.sp = sp - 48#64 → sp &&& 15#64 = 0#64 →
      s.trace = s0.trace → s.readReg64 .x19 = v →
      s.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
      (off = 212#64 → s.readReg64 .x21 = p.maxJump.zeroExtend 64) →
      MsgEnc48CalleeSavedPlaced s0 s →
      P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
        stackAt (sp - 48#64) (0x30 + resStack)) ∗ F →
      (∀ (sm : State) (nextCap nextPtr : BitVec 64),
        sm.pc = pl.base + retOff → sm.status = .Running → sm.sp = sp - 48#64 →
        sm.trace = s0.trace → sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
        sm.readReg64 .x19 = v → sm.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 →
        (off = 212#64 → sm.readReg64 .x21 = p.maxJump.zeroExtend 64) →
        MsgEnc48CalleeSavedPlaced s0 sm → curBs.length < nextCap.toNat →
        curCap.toNat ≤ nextCap.toNat →
        (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
        nextCap.toNat = (reserveStep curCap.toNat curBs.length 1).1 →
        SepWPp prog ret sm
          ((vecU8At A.repAlloc v nextCap nextPtr curBs ∗
            A.pool lim (M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt) sm ∗
            stackAt (sp - 48#64) (0x30 + resStack)) ∗ F) Q Qp) →
      SepWPp prog ret s P Q Qp

theorem step_hdr_placed {resStack : Nat} (hres : resStack + 96 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {pl : Placement} {varint_pc : BitVec 64} (hfn : IsCpPlacedProg prog pl varint_pc)
    {s0 s : State}
    (hencVarint : subroutine_ok prog varint_pc
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (x : EncodeChainParamsGhost) (st0 : M.σ) (sp : BitVec 64)
    (inv0 : ChainParamsBudgetInv M lim x st0 x.cap.toNat [])
    (hfit_hdr : x.bs.length + (chainParamsHeaderBytes x.tag x.p).length ≤ x.cap.toNat ∨
      x.bs.length + (chainParamsHeaderBytes x.tag x.p).length + 10 < 2 ^ 62)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = pl.base) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hw0 : s.readReg32 .x0 = x.tag) (hw1 : s.readReg32 .x1 = x.p.maxJump)
    (hw2 : s.readReg32 .x2 = x.p.maxOooKeys) (hx3 : s.readReg64 .x3 = x.v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s) (hhs0 : s = s0)
    (hP : P = (vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s ∗
      stackAt sp (msgEnc48VarintStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64) (evs1 : List AllocEvent),
      sm.pc = pl.base + (if x.p.maxJump == 0#32 then 124#64 else 212#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = x.v → sm.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64 →
      sm.readReg64 .x21 = x.p.maxJump.zeroExtend 64 → MsgEnc48CalleeSavedPlaced s0 sm →
      x.cap.toNat ≤ cap1.toNat →
      (x.bs.length + (chainParamsHeaderBytes x.tag x.p).length ≤ x.cap.toNat →
        cap1 = x.cap ∧ ptr1 = x.ptr) →
      ChainParamsBudgetInv M lim x st0 cap1.toNat evs1 →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc x.v cap1 ptr1 (x.bs ++ chainParamsHeaderBytes x.tag x.p) ∗
          A.pool lim (M.stepEvents evs1 st0) sm ∗
          stackAt (sp - 48#64) (0x30 + resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hfnE := hfn.toEncodePlacedProg
  have hlen_split := encodeChainParamsMsg_len_split x.tag x.p
  have hlen_eq := chainParamsHeaderBytes_len_eq x.tag x.p
  obtain ⟨hb1, hb2, _⟩ := chainParamsHeaderBytes_len_bounds x.tag x.p
  refine step_chainParams_prologue_placed hres hfnE x.v sp x.tag x.p hpc hrun hsp halign htr
    hw0 hw1 hw2 hx3 hcs hhs0 (F := vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗ A.pool lim st0 s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hx20_1 hx21_1 hcs1 hvmp0
  rw [sepConj_assoc, sepConj_left_comm (vecU8At A.repAlloc x.v x.cap x.ptr x.bs),
    ← A.pool_of_vmPreserved hvmp0]
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩
  have hbl40 := cpPlaced_fetch_bl_varint hbase trapHooks (k := 40)
    (fun [LibsignalPlacement] => CryptoVerification.blkPC_150_rebase_fetch_0x28 _ trapHooks)
    (fun [LibsignalPlacement] => CryptoVerification.blkPC_313_rebase_fetch_0x28 _ trapHooks)
  have hle_k : x.bs.length + (encodeVarint ((2#32 ||| (x.tag <<< 3)).zeroExtend 64)).length ≤
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length := by omega
  apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1 hinv1; rw [← A.pool_of_vmPreserved hvmp1]
    refine step_msg48_encode_varint_det_call_placed A lim hencVarint
      ((2#32 ||| (x.tag <<< 3)).zeroExtend 64) x.v x.cap x.ptr sp (pl.base + 44#64) x.bs
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
    refine step_chainParams_len_placed hfnE x.p x.v sp hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hcs2 ?_
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
      have hbl116 := cpPlaced_fetch_bl_varint hbase trapHooks (k := 116)
        (fun [LibsignalPlacement] => CryptoVerification.blkPC_150_rebase_fetch_0x74 _ trapHooks)
        (fun [LibsignalPlacement] => CryptoVerification.blkPC_313_rebase_fetch_0x74 _ trapHooks)
      apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp3 hinv3; rw [← A.pool_of_vmPreserved hvmp3]
        refine step_msg48_encode_varint_det_call_placed A lim hencVarint
          (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length) x.v cap01 ptr01 sp (pl.base + 120#64)
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
        have hpc4' : s4.pc = pl.base + (if x.p.maxOooKeys == 0#32 then 208#64 else 120#64) := by
          simp only [hmo, Bool.false_eq_true, ↓reduceIte, hpc4]
        refine step_chainParams_after_hdr_branch_placed hfnE x.p x.v sp hpc4' hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4 ?_
        intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 hvmp4
        rw [← A.pool_of_vmPreserved hvmp4]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext s5 sv3 cap1 ptr1 evs1 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 (Nat.le_trans hge01 hge1) ?_ inv1)
        intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega); exact hpres1 (by rw [List.length_append]; omega))
    · simp only [hmo, ↓reduceIte] at hpc3
      have hbl204 := cpPlaced_fetch_bl_varint hbase trapHooks (k := 204)
        (fun [LibsignalPlacement] => CryptoVerification.blkPC_150_rebase_fetch_0xcc _ trapHooks)
        (fun [LibsignalPlacement] => CryptoVerification.blkPC_313_rebase_fetch_0xcc _ trapHooks)
      apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp3 hinv3; rw [← A.pool_of_vmPreserved hvmp3]
        refine step_msg48_encode_varint_det_call_placed A lim hencVarint
          (BitVec.ofNat 64 (ChainParamsPB.encodeRaw x.p).length) x.v cap01 ptr01 sp (pl.base + 208#64)
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
        have hpc4' : s4.pc = pl.base + (if x.p.maxOooKeys == 0#32 then 208#64 else 120#64) := by
          simp only [hmo, ↓reduceIte, hpc4]
        refine step_chainParams_after_hdr_branch_placed hfnE x.p x.v sp hpc4' hrun4 hsp4 htr4 hx19_4 hx20_4 hx21_4 hcs4 ?_
        intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 hvmp4
        rw [← A.pool_of_vmPreserved hvmp4]
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (hnext s5 sv3 cap1 ptr1 evs1 hpc5 hrun5 hsp5 htr5 hx19_5 hx20_5 hx21_5 hcs5 (Nat.le_trans hge01 hge1) ?_ inv1)
        intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega); exact hpres1 (by rw [List.length_append]; omega)))

theorem step_maxJump_placed {resStack : Nat}
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {pl : Placement} {varint_pc : BitVec 64} (hfn : IsCpPlacedProg prog pl varint_pc)
    {s0 s : State}
    (hencVarint : subroutine_ok prog varint_pc (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hres212 : CpReserve1Stepper resStack A lim prog pl 212#64 228#64 s0)
    (x : EncodeChainParamsGhost) (st0 : M.σ) (curCap curPtr sp : BitVec 64)
    (curBs : List (BitVec 8)) (accEvs : List AllocEvent)
    (inv : ChainParamsBudgetInv M lim x st0 curCap.toNat accEvs)
    (hrem : curBs.length + (encodeUint32Field 1#32 x.p.maxJump).length ≤
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length)
    (hfit_mj : curBs.length + (encodeUint32Field 1#32 x.p.maxJump).length ≤ curCap.toNat ∨
      curBs.length + (encodeUint32Field 1#32 x.p.maxJump).length + 10 < 2 ^ 62)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = pl.base + (if x.p.maxJump == 0#32 then 124#64 else 212#64))
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.v)
    (hx20 : s.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.p.maxJump.zeroExtend 64) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc x.v curCap curPtr curBs ∗
      A.pool lim (M.stepEvents accEvs st0) s ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64) (nextEvs : List AllocEvent),
      sm.pc = pl.base + (if x.p.maxOooKeys == 0#32 then 264#64 else 128#64) →
      sm.status = .Running → sm.sp = sp - 48#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = x.v → sm.readReg64 .x20 = x.p.maxOooKeys.zeroExtend 64 →
      MsgEnc48CalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (encodeUint32Field 1#32 x.p.maxJump).length ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      ChainParamsBudgetInv M lim x st0 nextCap.toNat nextEvs →
      SepWPp prog ret sm
        ((vecU8At A.repAlloc x.v nextCap nextPtr (curBs ++ encodeUint32Field 1#32 x.p.maxJump) ∗
          A.pool lim (M.stepEvents nextEvs st0) sm ∗ stackAt (sp - 48#64) (0x30 + resStack)) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  have hfnE := hfn.toEncodePlacedProg
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
    refine step_chainParams_push_maxJump_tag_placed A.repAlloc hfnE x.v cap01 ptr01 sp curBs x.p hlt01
      hpc1 hrun1 hsp1 htr1 hx1_1 hx19_1 hx20_1 hx21_1' hcs1
      (F := A.pool lim (M.stepEvents evs01 st0) s1 ∗ stackAt (sp - 48#64) (0x30 + resStack) ∗ F) (by sep_ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hx21_2 hcs2 hvmp1
    rw [← A.pool_of_vmPreserved hvmp1]
    rcases hfn with ⟨P_blk, H, rfl, hbase⟩
    have hbl256 := cpPlaced_fetch_bl_varint hbase trapHooks (k := 256)
      (fun [LibsignalPlacement] => CryptoVerification.blkPC_150_rebase_fetch_0x100 _ trapHooks)
      (fun [LibsignalPlacement] => CryptoVerification.blkPC_313_rebase_fetch_0x100 _ trapHooks)
    have hfit_v : (curBs ++ [0x08#8]).length + (encodeVarint (x.p.maxJump.zeroExtend 64)).length ≤ cap01.toNat ∨
        (curBs ++ [0x08#8]).length + 10 < 2 ^ 62 := by
      rw [List.length_append, List.length_singleton]
      rcases hfit_mj with h | h
      · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
      · right; omega
    have hle_v : (curBs ++ [0x08#8]).length + (encodeVarint (x.p.maxJump.zeroExtend 64)).length ≤
        x.bs.length + (encodeChainParamsMsg x.tag x.p).length := by rw [List.length_append, List.length_singleton]; omega
    apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp2 hinv2; rw [← A.pool_of_vmPreserved hvmp2]
      refine step_msg48_encode_varint_det_call_placed A lim hencVarint (x.p.maxJump.zeroExtend 64)
        x.v cap01 ptr01 sp (pl.base + 260#64) (curBs ++ [0x08#8]) (M.stepEvents evs01 st0)
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
      have hpc3' : s3.pc = pl.base + (if x.p.maxJump == 0#32 then 124#64 else 260#64) := by
        simp only [hmj, Bool.false_eq_true, ↓reduceIte, hpc3]
      refine step_chainParams_after_maxJump_branch_placed hfnE x.p x.v sp hpc3' hrun3 hsp3 htr3 hx19_3 hx20_3 hcs3 ?_
      intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 hvmp3
      rw [← A.pool_of_vmPreserved hvmp3]
      refine hnext s4 nextCap nextPtr nextEvs hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4 (Nat.le_trans hge01 hge1) ?_ inv1
      intro hle; obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
      exact hpres1 (by rw [List.length_append, List.length_singleton]; omega))
  · subst hP
    refine step_chainParams_after_maxJump_branch_placed hfnE x.p x.v sp
      (by simp only [hmj, ↓reduceIte] at hpc ⊢; exact hpc) hrun hsp htr hx19 hx20 hcs ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 hvmp0
    rw [← A.pool_of_vmPreserved hvmp0, ← bs_append_maxJump_of_zero curBs x.p hmj]
    exact hnext s1 curCap curPtr accEvs hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) inv

theorem step_tailcall_184_placed {resStack : Nat} (hres96 : resStack + 96 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {pl : Placement} {varint_pc : BitVec 64} (hfn : IsCpPlacedProg prog pl varint_pc) {s0 s : State}
    (hencVarint : subroutine_ok prog varint_pc (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (val v curCap curPtr sp sv3 : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit_v : curBs.length + (encodeVarint val).length ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits_v : FitsEvents M lim curSt (encodeVarintEvents (EncodeVarintGhost.mk val v curCap curPtr curBs)))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = pl.base + 184#64) (hrun : s.status = .Running) (hsp : s.sp = sp)
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
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  rcases hfn with ⟨P_blk, H, rfl, hbase⟩; subst hP
  have hb184 := cpPlaced_fetch_b_varint hbase trapHooks (k := 184)
    (fun [LibsignalPlacement] => CryptoVerification.blkPC_150_rebase_fetch_0xb8 _ trapHooks)
    (fun [LibsignalPlacement] => CryptoVerification.blkPC_313_rebase_fetch_0xb8 _ trapHooks)
  apply sepWPp_of_sepWP_cs_vm_placed (mid := varint_pc)
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

theorem step_maxOooKeys_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {pl : Placement} {varint_pc : BitVec 64} (hfn : IsCpPlacedProg prog pl varint_pc) {s0 s : State}
    (hencVarint : subroutine_ok prog varint_pc (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hres128 : CpReserve1Stepper resStack A lim prog pl 128#64 144#64 s0)
    (x : EncodeChainParamsGhost) (st0 : M.σ) (curCap curPtr sp sv3 : BitVec 64)
    (curBs : List (BitVec 8)) (accEvs : List AllocEvent)
    (inv : ChainParamsBudgetInv M lim x st0 curCap.toNat accEvs)
    (hrem : curBs.length + (encodeUint32Field 2#32 x.p.maxOooKeys).length ≤
      x.bs.length + (encodeChainParamsMsg x.tag x.p).length)
    (hfit_mo : curBs.length + (encodeUint32Field 2#32 x.p.maxOooKeys).length ≤ curCap.toNat ∨
      curBs.length + (encodeUint32Field 2#32 x.p.maxOooKeys).length + 10 < 2 ^ 62)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = pl.base + (if x.p.maxOooKeys == 0#32 then 264#64 else 128#64))
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
    SepWPp prog (s0.readReg64 .lr) s P Q Qp := by
  have hfnE := hfn.toEncodePlacedProg; have hres96 : resStack + 96 < 2 ^ 64 := by omega
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
    refine step_chainParams_push_maxOooKeys_epilogue_placed A.repAlloc hfnE x.v cap01 ptr01 sp sv3
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
    refine step_tailcall_184_placed hres96 A lim hfn hencVarint (x.p.maxOooKeys.zeroExtend 64)
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
    refine step_chainParams_epilogue_placed hres96 hfnE sp sv3 hpc hrun hsp halign htr hcs
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

/-- Shared core placed execution theorem for Blocks `150` and `313` establishing `EncodeChainParamsEnv`. -/
theorem chainParams_core_placed_ok {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {pl : Placement} {varint_pc : BitVec 64} (hfn : IsCpPlacedProg prog pl varint_pc)
    {x : EncodeChainParamsGhost} {st0 : M.σ} {R : SepProp} {s0 : State}
    {Qp : State → SepProp → Prop}
    (hencV : subroutine_ok prog varint_pc
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hres212 : CpReserve1Stepper resStack A lim prog pl 212#64 228#64 s0)
    (hres128 : CpReserve1Stepper resStack A lim prog pl 128#64 144#64 s0)
    (hpc : s0.pc = pl.base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (encodeChainParamsSpecOf resStack A lim).pre (x, st0) s0 ∗ R)
    (hsp_align : s0.spAligned = true) :
    ∃ P, (s0.mem ⊨ P ∗ R) ∧
      SepWPp prog (s0.readReg64 .lr) s0 P
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
  refine step_hdr_placed hres96 A lim hfn hencV x st0 s0.sp (ChainParamsBudgetInv.init hEnv)
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
  refine step_maxJump_placed A lim hfn hencV hres212 x st0 cap1 ptr1 s0.sp
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
  refine step_maxOooKeys_placed hres A lim hfn hencV hres128 x st0 cap2 ptr2 s0.sp sv3
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

/-- Assemble `encodeChainParamsSpecOf` from `chainParams_core_placed_ok` on `(M, A, lim)` plus a
spare-capacity instantiation on `vmRecordBudget A s0`. -/
theorem chainParams_full_placed_ok_of_core [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {prog : Program} {pl : Placement} {varint_pc : BitVec 64}
    (hfn : IsCpPlacedProg prog pl varint_pc) {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (henc0 : subroutine_ok prog varint_pc (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hres212 : ∀ s0, LibsignalCodeLoaded lsmpl s0.mem → CpReserve1Stepper resStack A lim prog pl 212#64 228#64 s0)
    (hres128 : ∀ s0, LibsignalCodeLoaded lsmpl s0.mem → CpReserve1Stepper resStack A lim prog pl 128#64 144#64 s0)
    (hencVac : ∀ s0, subroutine_ok prog varint_pc
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack (vmRecordBudget A s0) zeroEnforcedLimits)))
    (hres212Vac : ∀ s0, LibsignalCodeLoaded lsmpl s0.mem →
      CpReserve1Stepper resStack (vmRecordBudget A s0) zeroEnforcedLimits prog pl 212#64 228#64 s0)
    (hres128Vac : ∀ s0, LibsignalCodeLoaded lsmpl s0.mem →
      CpReserve1Stepper resStack (vmRecordBudget A s0) zeroEnforcedLimits prog pl 128#64 144#64 s0) :
    subroutine_ok prog pl.base (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf resStack A lim)) := by
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
    obtain ⟨P, hP, hwp⟩ := chainParams_core_placed_ok (Qp := fun _ _ => False) hres
      (vmRecordBudget A s0) zeroEnforcedLimits hfn
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (hencVac s0))
      (hres212Vac s0 hcl0) (hres128Vac s0 hcl0) hpc hrun hpreVac hsp
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
  · obtain ⟨P, hP, hwp⟩ := chainParams_core_placed_ok (Qp := fun _ _ => False) hres A lim hfn
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 henc0)
      (hres212 s0 hcl0) (hres128 s0 hcl0) hpc hrun hpre hsp
    refine ⟨P, R, hP, sepWPp_mono_post hwp ?_ (fun _ _ h => h.elim)⟩
    rintro sf Qf ⟨⟨htrf, evs, cap', ptr', hge, hpres, hEnv, rfl⟩, hspf, hccf⟩
    refine ⟨fun hmQ => ?_, hspf, hccf⟩
    exact satisfies_encodeChainParams_post A lim x st0 s0 sf R cap' ptr' evs htrf hge hpres hEnv
      (fun h => absurd h hspare) (by simpa only [sepConj_assoc] using hmQ)

/-- Assemble exact-capacity 0-allocation `encodeChainParamsExactVmSpecOf` (`A.live`-only) from
`chainParams_core_placed_ok` on `rawVmRecordBudget A hblk s0`. -/
theorem chainParams_exact_placed_ok_of_core [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {prog : Program} {pl : Placement} {varint_pc : BitVec 64}
    (hfn : IsCpPlacedProg prog pl varint_pc) (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (hencVac : ∀ s0, subroutine_ok prog varint_pc
      (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack (rawVmRecordBudget A hblk s0) zeroEnforcedLimits)))
    (hres212Vac : ∀ s0, LibsignalCodeLoaded lsmpl s0.mem →
      CpReserve1Stepper resStack (rawVmRecordBudget A hblk s0) zeroEnforcedLimits prog pl 212#64 228#64 s0)
    (hres128Vac : ∀ s0, LibsignalCodeLoaded lsmpl s0.mem →
      CpReserve1Stepper resStack (rawVmRecordBudget A hblk s0) zeroEnforcedLimits prog pl 128#64 144#64 s0) :
    subroutine_ok prog pl.base (withLsCodeLoaded lsmpl (encodeChainParamsExactVmSpecOf resStack A)) := by
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
  obtain ⟨P, hP, hwp⟩ := chainParams_core_placed_ok (Qp := fun _ _ => False) hres
    (rawVmRecordBudget A hblk s0) zeroEnforcedLimits hfn
    (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (hencVac s0))
    (hres212Vac s0 hcl0) (hres128Vac s0 hcl0) hpc hrun hpreVac hsp
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

/-! ## 3. Block `150` (`[local#1]`) Reserve Steppers & Placed Contracts -/

private theorem step_reserve_1_common_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_150 H) (lsmpl.base 157)
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim))) :
    CpReserve1Stepper resStack A lim (lsProg_150 H) blkPl_150 212#64 228#64 s0 ∧
      CpReserve1Stepper resStack A lim (lsProg_150 H) blkPl_150 128#64 144#64 s0 := by
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
      apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 157)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0; rw [← A.pool_of_vmPreserved hvmp0]
        refine step_msg48_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
          ((blkPl_150).base + 312#64) curBs 1 curSt hbound1 hfits_do (F := F)
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
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_150).base + 228#64)
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
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_150).base + 228#64)
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
      apply sepWPp_of_sepWP_cs_vm_placed (mid := lsmpl.base 157)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp0 hinv0; rw [← A.pool_of_vmPreserved hvmp0]
        refine step_msg48_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
          ((blkPl_150).base + 292#64) curBs 1 curSt hbound1 hfits_do (F := F)
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega) (by simp only [arm64_norm]) (cs_step hcs hinv0)
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
        intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
        let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
        have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
        have hx20_1 : s1.readReg64 .x20 = p.maxOooKeys.zeroExtend 64 := by rw [hcs01.2.1]; simp only [arm64_norm, *]
        rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
        apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_150).base + 144#64)
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
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_150).base + 144#64)
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
    (hdoReserve : subroutine_ok (lsProg_150 H) (lsmpl.base 157) (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim))) :
    CpReserve1Stepper resStack A lim (lsProg_150 H) blkPl_150 212#64 228#64 s0 :=
  (step_reserve_1_common_placed hres A lim hdoReserve).1

theorem step_reserve_128_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)} {s0 : State}
    (hdoReserve : subroutine_ok (lsProg_150 H) (lsmpl.base 157) (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim))) :
    CpReserve1Stepper resStack A lim (lsProg_150 H) blkPl_150 128#64 144#64 s0 :=
  (step_reserve_1_common_placed hres A lim hdoReserve).2

theorem encode_chainParams_1_placed_ok_of_callees [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)}
    (henc0 : subroutine_ok (lsProg_150 H) (blkPl_148).base (withLsCodeLoaded lsmpl (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve0 : subroutine_ok (lsProg_150 H) (lsmpl.base 157) (withLsCodeLoaded lsmpl (doReserve2SpecOf resStack A lim))) :
    subroutine_ok (lsProg_150 H) (blkPl_150).base (withLsCodeLoaded lsmpl (encodeChainParamsSpecOf resStack A lim)) :=
  chainParams_full_placed_ok_of_core hres (isCpPlacedProg_150 H) A lim henc0
    (fun s0 hcl0 => step_reserve_212_1_placed hres A lim (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0))
    (fun s0 hcl0 => step_reserve_128_1_placed hres A lim (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 hdoReserve0))
    (fun s0 => ls_subroutine_ok_of_block (callerProg := lsProg_150 H)
      (encodeVarint2_det_placed_ok_of_doReserve (by omega) (vmRecordBudget A s0) zeroEnforcedLimits H
        (vacuous_doReserve2_placed_ok (vmRecordBudget A s0))))
    (fun s0 hcl0 => step_reserve_212_1_placed hres (vmRecordBudget A s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (vacuous_doReserve2_placed_ok (vmRecordBudget A s0))))
    (fun s0 hcl0 => step_reserve_128_1_placed hres (vmRecordBudget A s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (vacuous_doReserve2_placed_ok (vmRecordBudget A s0))))

theorem encode_chainParams_1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams150PlacedOk A lim H :=
  encode_chainParams_1_placed_ok_of_callees (resStack := doReserveStack) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_150 H) (encode_varint2_det_placed_ok h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_150 H) (do_reserve2_placed_ok h_panic hshim halloc hrealloc))

theorem encode_chainParams_1_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams150PlacedOkX A lim H :=
  encode_chainParams_1_placed_ok_of_callees (resStack := doReserveStackX) (by decide) A lim
    (ls_subroutine_ok_of_block (callerProg := lsProg_150 H) (encode_varint2_det_placed_ok_x h_panic hshim halloc hrealloc))
    (ls_subroutine_ok_of_block (callerProg := lsProg_150 H) (do_reserve2_placed_ok_x h_panic hshim halloc hrealloc))

theorem hookSat_withPanics_spqr {α : Type} {ext : String → Option (State → State)}
    {hname : String} {spec : Spec α} (hnp : Rust.isPanicSymbol hname = false)
    (hsat : HookSat ext hname spec) : HookSat (Rust.withPanics ext) hname spec := by
  obtain ⟨f, hf, hok⟩ := hsat; exact ⟨f, by simp [Rust.withPanics, hnp, hf], hok⟩

theorem encode_chainParams_1_placed_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (h_panic : (Rust.withPanics ext) spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat ext spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat ext spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    EncodeChainParams150PlacedOkExt A lim ext :=
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
    EncodeChainParams150PlacedOkExtX A lim ext :=
  encode_chainParams_1_placed_ok_x h_panic
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustNoAllocShimSym]) hshim)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustAllocSym]) halloc)
    (hookSat_withPanics_spqr (by simp [Rust.isPanicSymbol, spqrRustReallocSym]) hrealloc)

theorem encode_chainParams_1_exact_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) (A : RustAlloc)
    (hblk : ∀ p n al, A.live p n al ⊢
      ⌜p ≠ 0#64 ∧ p.toNat % al = 0 ∧ p.toNat + n < 2 ^ 64 ∧ RustLayoutOk n al⌝ ∗ A.live p n al)
    (H : String → Option (State → State)) : EncodeChainParams150ExactPlacedOk resStack A H :=
  chainParams_exact_placed_ok_of_core hres (isCpPlacedProg_150 H) A hblk
    (fun s0 => ls_subroutine_ok_of_block (callerProg := lsProg_150 H)
      (encodeVarint2_det_placed_ok_of_doReserve (by omega) (rawVmRecordBudget A hblk s0) zeroEnforcedLimits H
        (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0))))
    (fun s0 hcl0 => step_reserve_212_1_placed hres (rawVmRecordBudget A hblk s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0))))
    (fun s0 hcl0 => step_reserve_128_1_placed hres (rawVmRecordBudget A hblk s0) zeroEnforcedLimits
      (subroutine_ok_withMsgEnc48CSPlaced_placed s0 hcl0 (vacuous_doReserve2_placed_ok (rawVmRecordBudget A hblk s0))))

theorem encode_chainParams_1_exact_cli_placed_ok [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 48 + 64 < 2 ^ 64) (A : RustCliAlloc) (H : String → Option (State → State)) :
    EncodeChainParams150ExactPlacedOk resStack A.repAlloc H :=
  encode_chainParams_1_exact_placed_ok hres A.repAlloc A.block_valid H

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParams1Budget
