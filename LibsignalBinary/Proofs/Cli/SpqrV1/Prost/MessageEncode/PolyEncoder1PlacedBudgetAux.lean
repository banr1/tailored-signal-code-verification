/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyDecoder1PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncodedLenPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeRepeated1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2BasePlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Varint.EncodeVarint2PlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedBudget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Stepping Helpers for `encode<PolynomialEncoder> [local#3]` (Block `456`)

Proves `2^60`-cap reserve/stage steppers and exact `2^59`-cap zero-allocation stage steppers on CLI
Block `456` under `[LibsignalPlacement]` and `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget VmPreserved
   fitsEvents_append)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (ProtoPolynomialEncoder)
open CryptoVerification.LibsignalSpqrV1.Proto (encodeUint32Field)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (EncodeVarintGhost)
open CryptoVerification.SpqrV1.Poly
  (ProtoPolynomialEncoderGhost protoPolynomialEncoderPinnedAt)
open CryptoVerification.SpqrV1.Varint
  (EncodeRepeatedGhost encodeRepeatedBytes encodeRepeatedStackOf repeatedBytesSliceAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero ofNat_countLeadingZeros_32
   ofNat_countLeadingZeros_64 ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   vecU8At_eq_header_sep_buf zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.MessageEncode
  (MsgEnc48CalleeSavedPlaced bs0_append_polyEncoderHeaderBytes bs_append_idx_of_ne_zero
   bs_append_idx_of_zero calleeSavedPreserved_setPC_placed cap_toNat_eq_of_beq
   idx_field_len_of_ne_zero lt_cap_toNat_of_beq_false msgEnc48CalleeSavedPlaced_setPC
   msgEnc48RepeatedStackOf msgEnc48SavedFrame polyEncoderElemsAt polyEncoderHeaderBytes
   polyEncoderHeaderBytes_len_bounds polyEncoderRestAt polynomialEncoderPBEncodedLen
   reserveCap_one_bounds withMsgEnc48CSPlaced)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (cap_beq_len_false_of_lt_placed)
open CryptoVerification.Cli.SpqrV1.Alloc.Placed (blkPl_460)
open CryptoVerification.Cli.SpqrV1.Varint.Placed (blkPl_448 blkPl_451)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced (blkPl_480)
open CryptoVerification.Cli.SpqrV1.Prost.MessageEncode.Placed (blkPl_456 lsProg_456)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodeVarintEvents encodeVarintEvents_of_spare pushByteStep)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarintPlacedCommonBudget (doReserve2SpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4BaseBudget (encodeVarintFitSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeatedCommonBudget
  (encodeRepeatedEvents encodeRepeatedSpecOf encodeVarintDetSpecOf pushBytesStep_add)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
  (encodeRepeatedStep pushBytesStep pushBytesStep_snd_eq reserveStep
   reserveStep_of_need_doReserveEvents reserveStep_of_spare reserveStep_one_eq_pushByteStep
   sepWP_done_tpidr_placed sepWP_done_vm_placed sepWPp_of_sepWP_cs_vm_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MsgEncPlacedCSBudget
  (step_msg48_encode_repeated_call_placed step_msg48_encode_repeated_tailcall_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBaseBudget
  (polynomialEncoderEncodedLenElemsOutSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
  (step_msg48rep_do_reserve2_call_placed step_msg48rep_encode_varint_call_placed
   step_msg48rep_encode_varint_det_call_placed step_msg48rep_polyEncLen_call_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoderBasePlacedBudget
  (step_polyEncoder_check_idx_placed step_polyEncoder_mov_x1_x19_68_placed
   step_polyEncoder_prep_polys_epilogue_placed step_polyEncoder_prep_pts_placed
   step_polyEncoder_prologue_placed step_polyEncoder_push_hdr_tag_placed
   step_polyEncoder_push_idx_tag_placed)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactBudget
  (encodeRepeated59ExactSpecOf)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExactPlacedABudget
  (step_msg48_encode_repeated59_exact_call_placed
   step_msg48_encode_repeated59_exact_tailcall_placed)

attribute [local irreducible] Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32 ProofLib.truncate32_ofNat64
  hwVarintLen_eq_ofNat_varintLen_norm hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  zext64_truncate32 noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

@[local arm64_norm] private theorem blkPl_451_base_eq [LibsignalPlacement] :
    (blkPl_451).base = lsmpl.base 451 := rfl
@[local arm64_norm] private theorem blkPl_460_base_eq [LibsignalPlacement] :
    (blkPl_460).base = lsmpl.base 460 := rfl
@[local arm64_norm] private theorem blkPl_448_base_eq [LibsignalPlacement] :
    (blkPl_448).base = lsmpl.base 448 := rfl
@[local arm64_norm] private theorem blkPl_480_base_eq [LibsignalPlacement] :
    (blkPl_480).base = lsmpl.base 480 := rfl

local macro "cs_step " hcs:term:max hinv:term:max : term =>
  `(CryptoVerification.SpqrV1.Prost.MessageEncode.MsgEnc48CalleeSavedPlaced.step $hcs
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp only [arm64_norm]) $hinv)

/-! ## 1. Pure Event & Capacity Decomposition Helpers -/

theorem pushBytesStep_one_eq (cap len : Nat) :
    pushBytesStep 1 cap len = reserveStep cap len 1 := by
  dsimp only [pushBytesStep]
  rw [List.append_nil, ← reserveStep_one_eq_pushByteStep]

theorem pushBytesStep_one_add (m cap len : Nat) :
    pushBytesStep (1 + m) cap len =
      let r0 := reserveStep cap len 1
      let r1 := pushBytesStep m r0.1 (len + 1)
      (r1.1, r0.2 ++ r1.2) := by
  rw [pushBytesStep_add 1 m cap len, pushBytesStep_one_eq]

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

/-! ## 2. Part 1 (`2^60` Cap): 1-Byte Reserve Steppers (`+20 → +40` and `+84 → +100` in Block `456`) -/

theorem step_reserve_20_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 128 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)}
    {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_456 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (reserveStep curCap.toNat curBs.length 1).2)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 20#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v)
    (hx19 : s.readReg64 .x19 = v) (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_456).base + 40#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (reserveStep curCap.toNat curBs.length 1).1 →
      SepWPp (lsProg_456 H) ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr curBs ∗
          A.pool lim (M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  subst hP
  refine extract_vecU8At_bounds A.repAlloc v curCap curPtr curBs
    (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hcap_le _ _ => ?_
  rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    have hres_eq := reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
    have hfits_do : FitsEvents M lim curSt
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      rwa [hres_eq] at hfits
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_460).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0; rw [← A.pool_of_vmPreserved hvmp0]
      refine step_msg48rep_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
        ((blkPl_456).base + 184#64) curBs 1 curSt hbound1 hfits_do (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        (by simp only [arm64_norm]) (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      have hx20_1 : s1.readReg64 .x20 = encA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 40#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp1 hinv1
        have hst_eq :
            M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) curSt =
              M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by
          rw [hres_eq]
        rw [← A.pool_of_vmPreserved hvmp1, hst_eq]
        refine SepWPp.weaken_pre
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (cs_step hcs1 hinv1)
            (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega)
            (fun h => absurd h (by omega)) (htoNat1.trans (congrArg Prod.fst hres_eq.symm)))))
  · have hlt0 := lt_cap_toNat_of_beq_false hcap_le (Bool.eq_false_iff.mpr hcap)
    have hres_eq := reserveStep_of_spare (cap := curCap.toNat) (len := curBs.length)
      (additional := 1) (by omega)
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 40#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0
      have hst_eq : curSt = M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by
        rw [hres_eq]; rfl
      rw [← A.pool_of_vmPreserved hvmp0, hst_eq]
      refine SepWPp.weaken_pre
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (cs_step hcs hinv0)
          hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (congrArg Prod.fst hres_eq.symm)))

theorem step_reserve_84_1_placed [LibsignalPlacement] {resStack : Nat}
    (hres : resStack + 128 < 2 ^ 64) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {H : String → Option (State → State)}
    {s0 s : State}
    (hdoReserve : subroutine_ok (lsProg_456 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (encA v curCap curPtr sp : BitVec 64) (curBs : List (BitVec 8)) (pb : ProtoPolynomialEncoder)
    (curSt : M.σ)
    (hfit1 : curBs.length + 1 ≤ curCap.toNat ∨ curBs.length + 10 < 2 ^ 62)
    (hfits : FitsEvents M lim curSt (reserveStep curCap.toNat curBs.length 1).2)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = pb.idx.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A.repAlloc v curCap curPtr curBs ∗ A.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = (blkPl_456).base + 100#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x0 = pb.idx.zeroExtend 64 →
      sm.readReg64 .x1 = BitVec.ofNat 64 curBs.length → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = encA → MsgEnc48CalleeSavedPlaced s0 sm →
      curBs.length < nextCap.toNat → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + 1 ≤ curCap.toNat → nextCap = curCap ∧ nextPtr = curPtr) →
      nextCap.toNat = (reserveStep curCap.toNat curBs.length 1).1 →
      SepWPp (lsProg_456 H) ret sm
        ((vecU8At A.repAlloc v nextCap nextPtr curBs ∗
          A.pool lim (M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  subst hP
  refine extract_vecU8At_bounds A.repAlloc v curCap curPtr curBs
    (F := A.pool lim curSt s ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun hcap_le _ _ => ?_
  rw [vecU8At_eq_header_sep_buf A.repAlloc v curCap curPtr curBs, vecHeader]
  by_cases hcap : curCap == BitVec.ofNat 64 curBs.length
  · have hcap_eq := cap_toNat_eq_of_beq (Nat.lt_of_le_of_lt hcap_le (BitVec.isLt curCap)) hcap
    have hfit10 : curBs.length + 10 < 2 ^ 62 := by rcases hfit1 with h | h <;> omega
    obtain ⟨hle1, hbound1, hge1, htoNat1⟩ := reserveCap_one_bounds hcap_eq hfit10
    have hres_eq := reserveStep_of_need_doReserveEvents v curCap curPtr curBs 1 (by omega)
    have hfits_do : FitsEvents M lim curSt
        (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) := by
      rwa [hres_eq] at hfits
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_460).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0; rw [← A.pool_of_vmPreserved hvmp0]
      refine step_msg48rep_do_reserve2_call_placed hres A lim hdoReserve v curCap curPtr sp
        ((blkPl_456).base + 208#64) curBs 1 curSt hbound1 hfits_do (F := F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *, BitVec.toNat_ofNat]; omega)
        (by simp only [arm64_norm]) (cs_step hcs hinv0)
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]) ?_
      intro s1 newPtr1 hpc1 hrun1 hsp1 htr1 hcs01 hcs1
      let newCap1 := BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length 1)
      have hx19_1 : s1.readReg64 .x19 = v := by rw [hcs01.1]; simp only [arm64_norm, *]
      have hx20_1 : s1.readReg64 .x20 = encA := by rw [hcs01.2.1]; simp only [arm64_norm, *]
      have hx21_1 : s1.readReg64 .x21 = pb.idx.zeroExtend 64 := by
        rw [hcs01.2.2.1]; simp only [arm64_norm, *]
      rw [vecU8At_eq_header_sep_buf A.repAlloc v newCap1 newPtr1 curBs, vecHeader]
      apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 100#64)
      by_vm_steps (
        wp_steps
        apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
        intro hvmp1 hinv1
        have hst_eq :
            M.stepEvents (doReserveEvents (DoReserveCall.mk v curCap curPtr curBs 1)) curSt =
              M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by
          rw [hres_eq]
        rw [← A.pool_of_vmPreserved hvmp1, hst_eq]
        refine SepWPp.weaken_pre
          (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
          (hnext _ newCap1 newPtr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (cs_step hcs1 hinv1)
            (by dsimp [newCap1]; omega) (by dsimp [newCap1]; omega)
            (fun h => absurd h (by omega)) (htoNat1.trans (congrArg Prod.fst hres_eq.symm)))))
  · have hlt0 := lt_cap_toNat_of_beq_false hcap_le (Bool.eq_false_iff.mpr hcap)
    have hres_eq := reserveStep_of_spare (cap := curCap.toNat) (len := curBs.length)
      (additional := 1) (by omega)
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 100#64)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp0 hinv0
      have hst_eq : curSt = M.stepEvents (reserveStep curCap.toNat curBs.length 1).2 curSt := by
        rw [hres_eq]; rfl
      rw [← A.pool_of_vmPreserved hvmp0, hst_eq]
      refine SepWPp.weaken_pre
        (by simp only [vecU8At_eq_header_sep_buf, vecHeader]; exact Entails.of_eq (by sep_ac_rfl))
        (hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (cs_step hcs hinv0)
          hlt0 (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) (congrArg Prod.fst hres_eq.symm)))

/-! ## 3. Part 1 (`2^60` Cap): Stage Steppers (`+0 → +76 → +128 → +144 → lr` in Block `456`) -/

theorem step_hdr_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} {s0 s : State}
    (hencLen : subroutine_ok (lsProg_456 H) (blkPl_480).base
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec A.repAlloc)))
    (hencVarint : subroutine_ok (lsProg_456 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_456 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (encA v cap0 ptr0 sp : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (bs0 : List (BitVec 8)) (st0 : M.σ)
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyEncoderHeaderBytes pb).length ≤ cap0.toNat ∨
      bs0.length + (polyEncoderHeaderBytes pb).length + 10 < 2 ^ 62)
    (hfits_hdr : FitsEvents M lim st0
      (pushBytesStep (polyEncoderHeaderBytes pb).length cap0.toNat bs0.length).2)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_456).base) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialEncoderPinnedAt A.repAlloc g encA pb ∗
      vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ A.pool lim st0 s ∗
      stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 cap1 ptr1 : BitVec 64)
      (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_456).base + 76#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → cap0.toNat ≤ cap1.toNat →
      (bs0.length + (polyEncoderHeaderBytes pb).length ≤ cap0.toNat →
        cap1 = cap0 ∧ ptr1 = ptr0) →
      cap1.toNat = (pushBytesStep (polyEncoderHeaderBytes pb).length cap0.toNat bs0.length).1 →
      SepWPp (lsProg_456 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt A.repAlloc encA g ptsElems polysElems ∗
          vecU8At A.repAlloc v cap1 ptr1 (bs0 ++ polyEncoderHeaderBytes pb) ∗
          A.pool lim (M.stepEvents (pushBytesStep (polyEncoderHeaderBytes pb).length
            cap0.toNat bs0.length).2 st0) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge2⟩ := polyEncoderHeaderBytes_len_bounds pb
  set vVal := BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)
  have hstep_split : pushBytesStep (polyEncoderHeaderBytes pb).length cap0.toNat bs0.length =
      (let r0 := reserveStep cap0.toNat bs0.length 1
       let r1 := pushBytesStep (encodeVarint vVal).length r0.1 (bs0.length + 1)
       (r1.1, r0.2 ++ r1.2)) := by
    rw [hlen_eq, pushBytesStep_one_add]
  have hfits_pair : FitsEvents M lim st0
      ((reserveStep cap0.toNat bs0.length 1).2 ++
        (pushBytesStep (encodeVarint vVal).length
          (reserveStep cap0.toNat bs0.length 1).1 (bs0.length + 1)).2) := by
    have h := hfits_hdr; rwa [hstep_split] at h
  obtain ⟨hfits_r0, hfits_r1⟩ := (fitsEvents_append M lim _ _ st0).mp hfits_pair
  refine step_polyEncoder_prologue_placed hres H encA v sp hhs0 hpc hrun hsp halign htr hx0 hx1 hcs
    (F := protoPolynomialEncoderPinnedAt A.repAlloc g encA pb ∗
      vecU8At A.repAlloc v cap0 ptr0 bs0 ∗ A.pool lim st0 s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hcs1 hvmp1
  rw [← A.pool_of_vmPreserved hvmp1]
  refine step_reserve_20_1_placed hres128 A lim hdoReserve encA v cap0 ptr0 sp bs0 st0 (by omega)
    hfits_r0 hpc1 hrun1 hsp1 halign htr1 hx0_1 hx1_1 hx19_1 hcs1
    (F := protoPolynomialEncoderPinnedAt A.repAlloc g encA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by sep_ac_rfl) ?_
  intro s2 cap01 ptr01 hpc2 hrun2 hsp2 htr2 hx1_2 hx19_2 hx20_2 hcs2 hlt01 hge01 hpres01 hcap01_eq
  set st01 := M.stepEvents (reserveStep cap0.toNat bs0.length 1).2 st0
  refine step_polyEncoder_push_hdr_tag_placed A.repAlloc H encA v cap01 ptr01 sp bs0 hlt01
    hpc2 hrun2 hsp2 htr2 hx1_2 hx19_2 hx20_2 hcs2
    (F := A.pool lim st01 s2 ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      protoPolynomialEncoderPinnedAt A.repAlloc g encA pb ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by sep_ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3 hvmp3
  rw [← A.pool_of_vmPreserved hvmp3]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_480).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hvmp3' hinv3; rw [← A.pool_of_vmPreserved hvmp3']
    refine step_msg48rep_polyEncLen_call_placed hres128 A lim hencLen encA sp
      ((blkPl_456).base + 68#64) g pb st01 hlen_lt
      (F := vecU8At A.repAlloc v cap01 ptr01 (bs0 ++ [0x12#8]) ∗
        msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
          (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
    intro s4 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt hpc4 hrun4 hsp4 htr4 hx0_4
      hcs34 hcs4 _hvmp4
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    refine step_polyEncoder_mov_x1_x19_68_placed H vVal encA v sp
      hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
    intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5 hvmp5
    rw [← A.pool_of_vmPreserved hvmp5]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp5' hinv5; rw [← A.pool_of_vmPreserved hvmp5']
      have hfit_len : (bs0 ++ [0x12#8]).length + (encodeVarint vVal).length ≤ cap01.toNat ∨
          (bs0 ++ [0x12#8]).length + 10 < 2 ^ 62 := by
        rw [List.length_append, List.length_singleton]
        rcases hfit_hdr with h | h
        · left; obtain ⟨rfl, _⟩ := hpres01 (by omega); omega
        · right; omega
      have hlen_bsK : (bs0 ++ [0x12#8]).length = bs0.length + 1 := by
        rw [List.length_append, List.length_singleton]
      have hfits_var : FitsEvents M lim st01
          (encodeVarintEvents (EncodeVarintGhost.mk vVal v cap01 ptr01 (bs0 ++ [0x12#8]))) := by
        simpa only [encodeVarintEvents, pushBytesStep_snd_eq, hcap01_eq, hlen_bsK] using hfits_r1
      refine step_msg48rep_encode_varint_det_call_placed hres128 A lim hencVarint
        vVal v cap01 ptr01 sp ((blkPl_456).base + 76#64) (bs0 ++ [0x12#8]) st01
        hfit_len hfits_var
        (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt A.repAlloc encA g ptsElems polysElems ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (cs_step hcs5 hinv5) (by sep_ac_rfl) ?_
      intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 hge1 hpres1 hcap1_eq
      have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
      have hx20_6 : s6.readReg64 .x20 = encA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
      have hst_hdr :
          M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk vVal v cap01 ptr01 (bs0 ++ [0x12#8]))) st01 =
            M.stepEvents (pushBytesStep (polyEncoderHeaderBytes pb).length cap0.toNat bs0.length).2 st0 := by
        simp only [st01, encodeVarintEvents, pushBytesStep_snd_eq, hcap01_eq, hlen_bsK,
          ← M.stepEvents_append, hstep_split]
      have hcap1_full :
          cap1.toNat = (pushBytesStep (polyEncoderHeaderBytes pb).length cap0.toNat bs0.length).1 := by
        rw [hcap1_eq, hcap01_eq, hlen_bsK, hstep_split]
      rw [bs0_append_polyEncoderHeaderBytes bs0 pb, hst_hdr]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext s6 sv3 cap1 ptr1 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
          hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6 (Nat.le_trans hge01 hge1) ?_ hcap1_full)
      intro hspare
      obtain ⟨rfl, rfl⟩ := hpres01 (by omega)
      exact hpres1 (by rw [hlen_bsK]; omega)))

theorem step_idx_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_456 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintDetSpecOf resStack A lim)))
    (hdoReserve : subroutine_ok (lsProg_456 H) (blkPl_460).base
      (withMsgEnc48CSPlaced s0 (doReserve2SpecOf resStack A lim)))
    (encA v cap1 ptr1 sp : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    (bs1 : List (BitVec 8)) (st1 : M.σ)
    (hfit_idx : bs1.length + (encodeUint32Field 1#32 pb.idx).length ≤ cap1.toNat ∨
      bs1.length + (encodeUint32Field 1#32 pb.idx).length + 10 < 2 ^ 62)
    (hfits_idx : FitsEvents M lim st1
      (pushBytesStep (encodeUint32Field 1#32 pb.idx).length cap1.toNat bs1.length).2)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 76#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A.repAlloc v cap1 ptr1 bs1 ∗ A.pool lim st1 s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_456).base + 128#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → cap1.toNat ≤ cap2.toNat →
      (bs1.length + (encodeUint32Field 1#32 pb.idx).length ≤ cap1.toNat →
        cap2 = cap1 ∧ ptr2 = ptr1) →
      cap2.toNat = (pushBytesStep (encodeUint32Field 1#32 pb.idx).length cap1.toNat bs1.length).1 →
      SepWPp (lsProg_456 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          vecU8At A.repAlloc v cap2 ptr2 (bs1 ++ encodeUint32Field 1#32 pb.idx) ∗
          A.pool lim (M.stepEvents (pushBytesStep (encodeUint32Field 1#32 pb.idx).length
            cap1.toNat bs1.length).2 st1) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  refine step_polyEncoder_check_idx_placed H encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A.repAlloc v cap1 ptr1 bs1 ∗ A.pool lim st1 s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvmp1
  rw [← A.pool_of_vmPreserved hvmp1]
  cases hidx : (pb.idx == 0#32)
  · simp only [hidx, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_idx, hge2_idx⟩ := idx_field_len_of_ne_zero pb hidx
    set idxVal := pb.idx.zeroExtend 64
    have hstep_split : pushBytesStep (encodeUint32Field 1#32 pb.idx).length cap1.toNat bs1.length =
        (let r0 := reserveStep cap1.toNat bs1.length 1
         let r1 := pushBytesStep (encodeVarint idxVal).length r0.1 (bs1.length + 1)
         (r1.1, r0.2 ++ r1.2)) := by
      rw [hlen_idx, pushBytesStep_one_add]
    have hfits_pair : FitsEvents M lim st1
        ((reserveStep cap1.toNat bs1.length 1).2 ++
          (pushBytesStep (encodeVarint idxVal).length
            (reserveStep cap1.toNat bs1.length 1).1 (bs1.length + 1)).2) := by
      have h := hfits_idx; rwa [hstep_split] at h
    obtain ⟨hfits_r0, hfits_r1⟩ := (fitsEvents_append M lim _ _ st1).mp hfits_pair
    refine step_reserve_84_1_placed hres A lim hdoReserve encA v cap1 ptr1 sp bs1 pb st1
      (by omega) hfits_r0 hpc1 hrun1 hsp1 halign htr1 hx0_1 hx19_1 hx20_1 hcs1
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F) (by sep_ac_rfl) ?_
    intro s2 cap12 ptr12 hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      hlt12 hge12 hpres12 hcap12_eq
    set st12 := M.stepEvents (reserveStep cap1.toNat bs1.length 1).2 st1
    refine step_polyEncoder_push_idx_tag_placed A.repAlloc H encA v cap12 ptr12 sp bs1 pb hlt12
      hpc2 hrun2 hsp2 htr2 hx0_2 hx1_2 hx19_2 hx20_2 hcs2
      (F := A.pool lim st12 s2 ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
        polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvmp3
    rw [← A.pool_of_vmPreserved hvmp3]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base)
    by_vm_steps (
      wp_steps
      apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
      intro hvmp3' hinv3; rw [← A.pool_of_vmPreserved hvmp3']
      have hlen_bsK : (bs1 ++ [0x08#8]).length = bs1.length + 1 := by
        rw [List.length_append, List.length_singleton]
      have hfit_var : (bs1 ++ [0x08#8]).length + (encodeVarint idxVal).length ≤ cap12.toNat ∨
          (bs1 ++ [0x08#8]).length + 10 < 2 ^ 62 := by
        rw [hlen_bsK]
        rcases hfit_idx with h | h
        · left; obtain ⟨rfl, _⟩ := hpres12 (by omega); omega
        · right; omega
      have hfits_var : FitsEvents M lim st12
          (encodeVarintEvents (EncodeVarintGhost.mk idxVal v cap12 ptr12 (bs1 ++ [0x08#8]))) := by
        simpa only [encodeVarintEvents, pushBytesStep_snd_eq, hcap12_eq, hlen_bsK] using hfits_r1
      refine step_msg48rep_encode_varint_det_call_placed hres A lim hencVarint
        idxVal v cap12 ptr12 sp ((blkPl_456).base + 128#64) (bs1 ++ [0x08#8]) st12
        hfit_var hfits_var
        (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [idxVal, arm64_norm, *]) (by simp only [arm64_norm, *])
        (cs_step hcs3 hinv3) (by sep_ac_rfl) ?_
      intro s4 cap2 ptr2 hpc4 hrun4 hsp4 htr4 hcs34 hcs4 hge2 hpres2 hcap2_eq
      have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
      have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
      have hst_idx :
          M.stepEvents (encodeVarintEvents (EncodeVarintGhost.mk idxVal v cap12 ptr12 (bs1 ++ [0x08#8]))) st12 =
            M.stepEvents (pushBytesStep (encodeUint32Field 1#32 pb.idx).length cap1.toNat bs1.length).2 st1 := by
        simp only [st12, encodeVarintEvents, pushBytesStep_snd_eq, hcap12_eq, hlen_bsK,
          ← M.stepEvents_append, hstep_split]
      have hcap2_full :
          cap2.toNat = (pushBytesStep (encodeUint32Field 1#32 pb.idx).length cap1.toNat bs1.length).1 := by
        rw [hcap2_eq, hcap12_eq, hlen_bsK, hstep_split]
      rw [bs_append_idx_of_ne_zero bs1 pb hidx, hst_idx]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext s4 cap2 ptr2 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
          (Nat.le_trans hge12 hge2) ?_ hcap2_full)
      intro hspare
      obtain ⟨rfl, rfl⟩ := hpres12 (by omega)
      exact hpres2 (by rw [hlen_bsK]; omega))
  · simp only [hidx, ↓reduceIte] at hpc1
    have hfield_nil : encodeUint32Field 1#32 pb.idx = [] := by
      simpa using bs_append_idx_of_zero [] pb hidx
    have hlen_zero : (encodeUint32Field 1#32 pb.idx).length = 0 := by rw [hfield_nil]; rfl
    have hst_zero :
        st1 = M.stepEvents (pushBytesStep (encodeUint32Field 1#32 pb.idx).length cap1.toNat bs1.length).2 st1 := by
      rw [hlen_zero]; rfl
    have hcap_zero :
        cap1.toNat = (pushBytesStep (encodeUint32Field 1#32 pb.idx).length cap1.toNat bs1.length).1 := by
      rw [hlen_zero]; rfl
    rw [← bs_append_idx_of_zero bs1 pb hidx, hst_zero]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1
        (Nat.le_refl _) (fun _ => ⟨rfl, rfl⟩) hcap_zero)

theorem step_pts_1_placed [LibsignalPlacement] {resStack : Nat}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} {s0 s : State}
    (hencRep : subroutine_ok (lsProg_456 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A lim)))
    (encA v cap2 ptr2 sp : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    (bs2 : List (BitVec 8)) (st2 : M.σ)
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts_lt : pb.pts.length < 2 ^ 58)
    (hfit_pts : bs2.length + (encodeRepeatedBytes 2 pb.pts).length ≤ cap2.toNat ∨
      bs2.length + (encodeRepeatedBytes 2 pb.pts).length + 10 < 2 ^ 62)
    (hfits_pts : FitsEvents M lim st2 (encodeRepeatedStep 2 cap2.toNat bs2.length pb.pts).2)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 128#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A.repAlloc v cap2 ptr2 bs2 ∗ A.pool lim st2 s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_456).base + 144#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm → cap2.toNat ≤ cap3.toNat →
      (bs2.length + (encodeRepeatedBytes 2 pb.pts).length ≤ cap2.toNat →
        cap3 = cap2 ∧ ptr3 = ptr2) →
      cap3.toNat = (encodeRepeatedStep 2 cap2.toNat bs2.length pb.pts).1 →
      SepWPp (lsProg_456 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          vecU8At A.repAlloc v cap3 ptr3 (bs2 ++ encodeRepeatedBytes 2 pb.pts) ∗
          A.pool lim (M.stepEvents (encodeRepeatedStep 2 cap2.toNat bs2.length pb.pts).2 st2) sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp (lsProg_456 H) ret s P Q Qp oom := by
  have hpts_len : ptsElems.length = pb.pts.length := by
    rw [← hpts_eq, List.length_map]
  refine step_polyEncoder_prep_pts_placed H encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At A.repAlloc v cap2 ptr2 bs2 ∗ A.pool lim st2 s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1 hvmp1
  rw [← A.pool_of_vmPreserved hvmp1]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1' hinv1; rw [← A.pool_of_vmPreserved hvmp1']
    have hfits_rep : FitsEvents M lim st2
        (encodeRepeatedEvents (EncodeRepeatedGhost.mk 2 g.pts.ptr ptsElems v cap2 ptr2 bs2)) := by
      simpa only [encodeRepeatedEvents, hpts_eq] using hfits_pts
    refine step_msg48_encode_repeated_call_placed A lim hencRep 2 g.pts.ptr v cap2 ptr2 sp
      ((blkPl_456).base + 144#64) ptsElems bs2 st2 (by decide) (by decide)
      (by rw [hpts_len]; exact hpts_lt) (by simpa only [hpts_eq] using hfit_pts) hfits_rep
      (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗
        ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((encA + 48#64) ↦₃₂ pb.idx) ∗
        repeatedBytesSliceAt g.polys.ptr polysElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm] at hw0_1 ⊢; exact hw0_1) (by simp only [arm64_norm, *])
      (by rw [hpts_len]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (cs_step hcs1 hinv1)
      (by dsimp only [polyEncoderElemsAt]; sep_ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hcs12 hcs2 hge3 hpres3 hcap3_eq
    have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
    have hx20_2 : s2.readReg64 .x20 = encA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
    simp only [encodeRepeatedEvents, hpts_eq] at hpres3 hcap3_eq ⊢
    exact SepWPp.weaken_pre (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl))
      (hnext s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hcs2 hge3 hpres3 hcap3_eq))

theorem step_polys_1_placed [LibsignalPlacement] {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : String → Option (State → State)} {s0 s : State}
    (hencRep : subroutine_ok (lsProg_456 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeatedSpecOf resStack A lim)))
    (encA v cap3 ptr3 sp sv3 : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    (bs3 : List (BitVec 8)) (st3 : M.σ)
    (hpolys_eq : polysElems.map Prod.snd = pb.polys) (hpolys_lt : pb.polys.length < 2 ^ 58)
    (hfit_polys : bs3.length + (encodeRepeatedBytes 3 pb.polys).length ≤ cap3.toNat ∨
      bs3.length + (encodeRepeatedBytes 3 pb.polys).length + 10 < 2 ^ 62)
    (hfits_polys : FitsEvents M lim st3 (encodeRepeatedStep 3 cap3.toNat bs3.length pb.polys).2)
    {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_456).base + 144#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim st3 s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State) (cap4 ptr4 : BitVec 64),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf → cap3.toNat ≤ cap4.toNat →
      (bs3.length + (encodeRepeatedBytes 3 pb.polys).length ≤ cap3.toNat →
        cap4 = cap3 ∧ ptr4 = ptr3) →
      ∀ (P_f : SepProp),
        (P_f ⊢ (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          vecU8At A.repAlloc v cap4 ptr4 (bs3 ++ encodeRepeatedBytes 3 pb.polys) ∗
          A.pool lim (M.stepEvents (encodeRepeatedStep 3 cap3.toNat bs3.length pb.polys).2 st3) sf ∗
          stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) →
        Q sf P_f) :
    SepWPp (lsProg_456 H) (s0.readReg64 .lr) s P Q Qp oom := by
  have hpolys_len : polysElems.length = pb.polys.length := by
    rw [← hpolys_eq, List.length_map]
  refine step_polyEncoder_prep_polys_epilogue_placed H encA v sp sv3 g pb ptsElems polysElems
    hpc hrun hsp halign htr hx19 hx20 hcs
    (F := vecU8At A.repAlloc v cap3 ptr3 bs3 ∗ A.pool lim st3 s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hw0_1 hx1_1 hx2_1 hx3_1 hcc1 hcs1 hvmp1
  rw [← A.pool_of_vmPreserved hvmp1]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base)
  by_vm_steps (
    wp_steps
    apply sepWP_done_tpidr_placed (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, wp_norm, *])
    intro hvmp1' hinv1; rw [← A.pool_of_vmPreserved hvmp1']
    have hcc1' : CalleeSavedPreserved s0 (s1.setPC (lsmpl.base 448)) := by
      have ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp⟩ := hcc1
      exact ⟨by simpa only [arm64_norm] using h19, by simpa only [arm64_norm] using h20,
        by simpa only [arm64_norm] using h21, by simpa only [arm64_norm] using h22,
        by simpa only [arm64_norm] using h23, by simpa only [arm64_norm] using h24,
        by simpa only [arm64_norm] using h25, by simpa only [arm64_norm] using h26,
        by simpa only [arm64_norm] using h27, by simpa only [arm64_norm] using h28,
        by simpa only [arm64_norm] using hfp⟩
    have hfits_rep : FitsEvents M lim st3
        (encodeRepeatedEvents (EncodeRepeatedGhost.mk 3 g.polys.ptr polysElems v cap3 ptr3 bs3)) := by
      simpa only [encodeRepeatedEvents, hpolys_eq] using hfits_polys
    refine step_msg48_encode_repeated_tailcall_placed hres A lim hencRep 3 g.polys.ptr v cap3 ptr3
      sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
      (s0.readReg64 .x20) (s0.readReg64 .x19) polysElems bs3 st3 (by decide) (by decide)
      (by rw [hpolys_len]; exact hpolys_lt) (by simpa only [hpolys_eq] using hfit_polys) hfits_rep
      (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗
        ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
        ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗
        ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
        ((encA + 48#64) ↦₃₂ pb.idx) ∗
        repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm] at hw0_1 ⊢; exact hw0_1) (by simp only [arm64_norm, *])
      (by rw [hpolys_len]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hcc1' (cs_step hcs1 hinv1)
      (by dsimp only [polyEncoderElemsAt]; sep_ac_rfl) ?_
    intro sf cap4 ptr4 hpcf hrunf hspf htrf hccf hcsf hge4 hpres4 _hcap4_eq
    simp only [encodeRepeatedEvents, hpolys_eq] at hpres4 ⊢
    exact hnext sf cap4 ptr4 hpcf hrunf hspf htrf hccf hcsf hge4 hpres4 _
      (by dsimp only [polyEncoderElemsAt]; exact Entails.of_eq (by sep_ac_rfl)))

/-! ## 4. Part 2 (`2^59` Exact `0`-Allocation Cap): Stage Steppers on Block `456` -/

private theorem pool_step {M : AllocCostModel} (B : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s1 s2 : State} (h : VmPreserved s1 s2) :
    B.pool lim st s1 = B.pool lim st s2 :=
  (B.pool_of_vmPreserved h).symm

theorem step_pe1_hdr_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencLen : subroutine_ok (lsProg_456 H) (blkPl_480).base
      (withMsgEnc48CSPlaced s0 (polynomialEncoderEncodedLenElemsOutSpec B.repAlloc)))
    (hencVarint : subroutine_ok (lsProg_456 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (encA v cap0 ptr0 sp : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder) (bs0 : List (BitVec 8)) (curSt : M.σ)
    (hlen_lt : polynomialEncoderPBEncodedLen pb < 2 ^ 64)
    (hfit_hdr : bs0.length + (polyEncoderHeaderBytes pb).length ≤ cap0.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = (blkPl_456).base)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = encA) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (protoPolynomialEncoderPinnedAt B.repAlloc g encA pb ∗
      vecU8At B.repAlloc v cap0 ptr0 bs0 ∗ B.pool lim curSt s ∗
      stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State) (sv3 : BitVec 64)
      (ptsElems polysElems : List (BitVec 64 × List (BitVec 8))),
      ptsElems.map Prod.snd = pb.pts → pb.pts.length * 24 < 2 ^ 63 →
      polysElems.map Prod.snd = pb.polys → pb.polys.length * 24 < 2 ^ 63 →
      sm.pc = (blkPl_456).base + 76#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_456 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          polyEncoderRestAt B.repAlloc encA g ptsElems polysElems ∗
          vecU8At B.repAlloc v cap0 ptr0 (bs0 ++ polyEncoderHeaderBytes pb) ∗
          B.pool lim curSt sm ∗
          stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
          msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_456 H) ret s P Q Qp := by
  have hres128 : resStack + 128 < 2 ^ 64 := by omega
  obtain ⟨hlen_eq, hge2⟩ := polyEncoderHeaderBytes_len_bounds pb
  have hlt0 : bs0.length < cap0.toNat := by omega
  have hcap_f : (cap0 == BitVec.ofNat 64 bs0.length) = false :=
    cap_beq_len_false_of_lt_placed hlt0
  refine step_polyEncoder_prologue_placed hres H encA v sp hhs0 hpc hrun hsp halign htr hx0 hx1 hcs
    (F := protoPolynomialEncoderPinnedAt B.repAlloc g encA pb ∗
      vecU8At B.repAlloc v cap0 ptr0 bs0 ∗ B.pool lim curSt s ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 sv3 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx19_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01, vecU8At_eq_header_sep_buf B.repAlloc v cap0 ptr0 bs0, vecHeader]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 40#64); wp_steps
  apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm12 hinv1
  rw [← vecHeader, ← vecU8At_eq_header_sep_buf B.repAlloc v cap0 ptr0 bs0,
    pool_step B lim curSt hvm12]
  refine step_polyEncoder_push_hdr_tag_placed B.repAlloc H encA v cap0 ptr0 sp bs0 hlt0
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (cs_step hcs1 hinv1)
    (F := stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗
      protoPolynomialEncoderPinnedAt B.repAlloc g encA pb ∗ B.pool lim curSt _ ∗ F)
    (by sep_ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx19_3 hx20_3 hcs3 hvm23
  rw [pool_step B lim curSt hvm23]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_480).base); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm3b hinv3
  rw [pool_step B lim curSt hvm3b]
  refine step_msg48rep_polyEncLen_call_placed hres128 B lim hencLen encA sp
    ((blkPl_456).base + 68#64) g pb curSt hlen_lt
    (F := vecU8At B.repAlloc v cap0 ptr0 (bs0 ++ [0x12#8]) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (cs_step hcs3 hinv3)
    (by sep_ac_rfl) ?_
  intro s4 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt hpc4 hrun4 hsp4 htr4 hx0_4
    hcs34 hcs4 _
  have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
  have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
  refine step_polyEncoder_mov_x1_x19_68_placed H
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) encA v sp
    hpc4 hrun4 hsp4 htr4 hx0_4 hx19_4 hx20_4 hcs4 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5 hx19_5 hx20_5 hcs5 hvm45
  rw [pool_step B lim curSt hvm45]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm5b hinv5
  rw [pool_step B lim curSt hvm5b]
  have hfit_len : (bs0 ++ [0x12#8]).length +
      (encodeVarint (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))).length ≤ cap0.toNat := by
    rw [List.length_append, List.length_singleton]; omega
  have hevs_len :
      encodeVarintEvents
        (EncodeVarintGhost.mk (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb))
          v cap0 ptr0 (bs0 ++ [0x12#8])) = [] :=
    encodeVarintEvents_of_spare hfit_len
  refine step_msg48rep_encode_varint_call_placed hres128 B lim hencVarint
    (BitVec.ofNat 64 (polynomialEncoderPBEncodedLen pb)) v cap0 ptr0 sp ((blkPl_456).base + 76#64)
    (bs0 ++ [0x12#8]) curSt (Or.inl hfit_len) (by rw [hevs_len]; trivial)
    (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      polyEncoderRestAt B.repAlloc encA g ptsElems polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (cs_step hcs5 hinv5)
    (by sep_ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs56 hcs6 _ hpres1
  obtain ⟨rfl, rfl⟩ := hpres1 hfit_len
  have hx19_6 : s6.readReg64 .x19 = v := by rw [hcs56.1]; simp only [arm64_norm, *]
  have hx20_6 : s6.readReg64 .x20 = encA := by rw [hcs56.2.1]; simp only [arm64_norm, *]
  rw [hevs_len, bs0_append_polyEncoderHeaderBytes bs0 pb]
  dsimp only [AllocCostModel.stepEvents]
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext s6 sv3 ptsElems polysElems hpts_eq hpts_lt hpolys_eq hpolys_lt
      hpc6 hrun6 hsp6 htr6 hx19_6 hx20_6 hcs6)

theorem step_pe1_idx_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 128 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencVarint : subroutine_ok (lsProg_456 H) (blkPl_451).base
      (withMsgEnc48CSPlaced s0 (encodeVarintFitSpecOf resStack B lim)))
    (encA v curCap curPtr sp : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    (curBs : List (BitVec 8)) (curSt : M.σ)
    (hfit_idx : curBs.length + (encodeUint32Field 1#32 pb.idx).length ≤ curCap.toNat)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_456).base + 76#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_456).base + 128#64 → sm.status = .Running → sm.sp = sp - 48#64 →
      sm.trace = s0.trace → sm.readReg64 .x19 = v → sm.readReg64 .x20 = encA →
      MsgEnc48CalleeSavedPlaced s0 sm →
      SepWPp (lsProg_456 H) ret sm
        ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
          vecU8At B.repAlloc v curCap curPtr (curBs ++ encodeUint32Field 1#32 pb.idx) ∗
          B.pool lim curSt sm ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack)) ∗ F)
        Q Qp) :
    SepWPp (lsProg_456 H) ret s P Q Qp := by
  refine step_polyEncoder_check_idx_placed H encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  cases hidx : (pb.idx == 0#32)
  · simp only [hidx, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hlen_idx, hge2_idx⟩ := idx_field_len_of_ne_zero pb hidx
    have hlt0 : curBs.length < curCap.toNat := by omega
    have hcap_f : (curCap == BitVec.ofNat 64 curBs.length) = false :=
      cap_beq_len_false_of_lt_placed hlt0
    rw [vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs, vecHeader]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_456).base + 100#64); wp_steps
    apply sepWP_done_vm_placed (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm12 hinv1
    rw [← vecHeader, ← vecU8At_eq_header_sep_buf B.repAlloc v curCap curPtr curBs,
      pool_step B lim curSt hvm12]
    refine step_polyEncoder_push_idx_tag_placed B.repAlloc H encA v curCap curPtr sp curBs pb hlt0
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (cs_step hcs1 hinv1)
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ B.pool lim curSt _ ∗
        stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
      (by sep_ac_rfl) ?_
    intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3 hx19_3 hx20_3 hcs3 hvm23
    rw [pool_step B lim curSt hvm23]
    apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_451).base); wp_steps
    apply sepWP_done_vm_placed
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
    intro hvm3b hinv3
    rw [pool_step B lim curSt hvm3b]
    have hfit_v : (curBs ++ [0x08#8]).length +
        (encodeVarint (pb.idx.zeroExtend 64)).length ≤ curCap.toNat := by
      rw [List.length_append, List.length_singleton]; omega
    have hevs_v :
        encodeVarintEvents
          (EncodeVarintGhost.mk (pb.idx.zeroExtend 64) v curCap curPtr (curBs ++ [0x08#8])) = [] :=
      encodeVarintEvents_of_spare hfit_v
    refine step_msg48rep_encode_varint_call_placed hres B lim hencVarint
      (pb.idx.zeroExtend 64) v curCap curPtr sp ((blkPl_456).base + 128#64)
      (curBs ++ [0x08#8]) curSt (Or.inl hfit_v) (by rw [hevs_v]; trivial)
      (F := polyEncoderElemsAt encA g pb ptsElems polysElems ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (cs_step hcs3 hinv3)
      (by sep_ac_rfl) ?_
    intro s4 nextCap nextPtr hpc4 hrun4 hsp4 htr4 hcs34 hcs4 _ hpres1
    obtain ⟨rfl, rfl⟩ := hpres1 hfit_v
    have hx19_4 : s4.readReg64 .x19 = v := by rw [hcs34.1]; simp only [arm64_norm, *]
    have hx20_4 : s4.readReg64 .x20 = encA := by rw [hcs34.2.1]; simp only [arm64_norm, *]
    rw [hevs_v, bs_append_idx_of_ne_zero curBs pb hidx]
    dsimp only [AllocCostModel.stepEvents]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4)
  · simp only [hidx, ↓reduceIte] at hpc1
    rw [← bs_append_idx_of_zero curBs pb hidx]
    exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hcs1)

theorem step_pe1_pts_polys_exact_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    {M : AllocCostModel} (B : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) {s0 s : State}
    (hencRep : subroutine_ok (lsProg_456 H) (blkPl_448).base
      (withMsgEnc48CSPlaced s0 (encodeRepeated59ExactSpecOf resStack B lim)))
    (encA v curCap curPtr sp sv3 : BitVec 64) (g : ProtoPolynomialEncoderGhost)
    (pb : ProtoPolynomialEncoder)
    (ptsElems polysElems : List (BitVec 64 × List (BitVec 8)))
    (curBs : List (BitVec 8)) (curSt : M.σ)
    (hpts_eq : ptsElems.map Prod.snd = pb.pts) (hpts59 : pb.pts.length < 2 ^ 59)
    (hpolys_eq : polysElems.map Prod.snd = pb.polys) (hpolys59 : pb.polys.length < 2 ^ 59)
    (hfit_pts : curBs.length + (encodeRepeatedBytes 2 pb.pts).length ≤ curCap.toNat)
    (hfit_polys : (curBs ++ encodeRepeatedBytes 2 pb.pts).length +
      (encodeRepeatedBytes 3 pb.polys).length ≤ curCap.toNat)
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_456).base + 128#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 48#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = encA)
    (hcs : MsgEnc48CalleeSavedPlaced s0 s)
    (hP : P = (polyEncoderElemsAt encA g pb ptsElems polysElems ∗
      vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → MsgEnc48CalleeSavedPlaced s0 sf →
      Q sf ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
        vecU8At B.repAlloc v curCap curPtr
          ((curBs ++ encodeRepeatedBytes 2 pb.pts) ++ encodeRepeatedBytes 3 pb.polys) ∗
        B.pool lim curSt sf ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F)) :
    SepWPp (lsProg_456 H) (s0.readReg64 .lr) s P Q Qp := by
  have hpts_len : ptsElems.length = pb.pts.length := by rw [← hpts_eq, List.length_map]
  have hpolys_len : polysElems.length = pb.polys.length := by rw [← hpolys_eq, List.length_map]
  refine step_polyEncoder_prep_pts_placed H encA v sp g pb ptsElems polysElems
    hpc hrun hsp htr hx19 hx20 hcs
    (F := vecU8At B.repAlloc v curCap curPtr curBs ∗ B.pool lim curSt s ∗
      stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by rw [hP]; sep_ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hw0_1 hx1_1 hx2_1 hx3_1 hx19_1 hx20_1 hcs1 hvm01
  rw [pool_step B lim curSt hvm01]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro hvm1b hinv1
  rw [pool_step B lim curSt hvm1b]
  refine step_msg48_encode_repeated59_exact_call_placed B lim hencRep 2 g.pts.ptr v curCap curPtr sp
    ((blkPl_456).base + 144#64) ptsElems curBs curSt (by decide) (by decide) (by omega)
    (by rw [hpts_eq]; exact hfit_pts)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.polys.ptr polysElems ∗
      msgEnc48SavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) sv3 (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    halign (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by dsimp only [State.readReg32, Reg.x0] at hw0_1 ⊢; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rw [hpts_len]; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (cs_step hcs1 hinv1)
    (by dsimp only [polyEncoderElemsAt]; sep_ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hcs12 hcs2
  have hx19_2 : s2.readReg64 .x19 = v := by rw [hcs12.1]; simp only [arm64_norm, *]
  have hx20_2 : s2.readReg64 .x20 = encA := by rw [hcs12.2.1]; simp only [arm64_norm, *]
  rw [hpts_eq]
  refine step_polyEncoder_prep_polys_epilogue_placed H encA v sp sv3 g pb ptsElems polysElems
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2 hcs2
    (F := vecU8At B.repAlloc v curCap curPtr (curBs ++ encodeRepeatedBytes 2 pb.pts) ∗
      B.pool lim curSt s2 ∗ stackAt (sp - 48#64) (encodeRepeatedStackOf resStack) ∗ F)
    (by dsimp only [polyEncoderElemsAt]; sep_ac_rfl) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hw0_3 hx1_3 hx2_3 hx3_3 hcc3 hcs3 hvm23
  rw [pool_step B lim curSt hvm23]
  apply sepWPp_of_sepWP_cs_vm_placed (mid := (blkPl_448).base); wp_steps
  apply sepWP_done_vm_placed
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *])
  intro _ hinv3
  exact step_msg48_encode_repeated59_exact_tailcall_placed
    (s := s3.setPC (blkPl_448).base)
    hres B lim hencRep 3 g.polys.ptr v curCap curPtr sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x21) sv3
    (s0.readReg64 .x20) (s0.readReg64 .x19) polysElems
    (curBs ++ encodeRepeatedBytes 2 pb.pts) curSt (by decide) (by decide) (by omega)
    (by rw [hpolys_eq]; exact hfit_polys)
    (F := ((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
      ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
      ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)
    (State.pc_setPC _ _)
    ((State.status_setPC _ _).trans hrun3)
    ((State.sp_setPC _ _).trans hsp3)
    halign
    ((State.trace_setPC _ _).trans htr3)
    ((State.readReg64_setPC _ _ _).trans hlr3)
    (by dsimp only [State.readReg32] at hw0_3 ⊢; rw [State.readReg64_setPC]; exact hw0_3)
    ((State.readReg64_setPC _ _ _).trans hx1_3)
    (by rw [State.readReg64_setPC, hpolys_len]; exact hx2_3)
    ((State.readReg64_setPC _ _ _).trans hx3_3)
    (calleeSavedPreserved_setPC_placed _ hcc3)
    (msgEnc48CalleeSavedPlaced_setPC _ hcs3 hinv3)
    (by rw [B.pool_setPC]; dsimp only [polyEncoderElemsAt]; sep_ac_rfl)
    (fun sf hpcf hrunf hspf htrf hccf hcsf => by
      rw [hpolys_eq]
      have hq := hnext sf hpcf hrunf hspf htrf hccf hcsf
      have hEq :
          ((polyEncoderElemsAt encA g pb ptsElems polysElems ∗
            vecU8At B.repAlloc v curCap curPtr
              ((curBs ++ encodeRepeatedBytes 2 pb.pts) ++ encodeRepeatedBytes 3 pb.polys) ∗
            B.pool lim curSt sf ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗ F) =
          ((repeatedBytesSliceAt g.polys.ptr polysElems ∗
            vecU8At B.repAlloc v curCap curPtr
              ((curBs ++ encodeRepeatedBytes 2 pb.pts) ++ encodeRepeatedBytes 3 pb.polys) ∗
            B.pool lim curSt sf ∗ stackAt sp (msgEnc48RepeatedStackOf resStack)) ∗
            (((encA + 8#64) ↦₆₄ g.pts.ptr) ∗ ((encA + 16#64) ↦₆₄ BitVec.ofNat 64 pb.pts.length) ∗
              ((encA + 32#64) ↦₆₄ g.polys.ptr) ∗ ((encA + 40#64) ↦₆₄ BitVec.ofNat 64 pb.polys.length) ∗
              ((encA + 48#64) ↦₃₂ pb.idx) ∗ repeatedBytesSliceAt g.pts.ptr ptsElems ∗ F)) := by
        dsimp only [polyEncoderElemsAt]; sep_ac_rfl
      rw [hEq] at hq
      exact hq)

end LibsignalBinary.Proofs.Cli.SpqrV1.Prost.MessageEncode.PolyEncoder1PlacedBudgetAux
