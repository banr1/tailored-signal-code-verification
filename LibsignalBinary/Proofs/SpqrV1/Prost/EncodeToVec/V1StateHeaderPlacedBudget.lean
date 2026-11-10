/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeaderPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `[LibsignalPlacement]` Phase 2d Header & Jump-Table Dispatch (`Block 426`, `+1740 .. +1896`)

Proves `VmPreserved` and `A.pool lim st`-threaded `[LibsignalPlacement]` symbolic execution of
the `st.inner` and `v1.innerState` header branches (`+1740 .. +1880`) in `Block 426`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeaderPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8At)
open CryptoVerification.LibsignalProtoCodec (encodeVarint)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.SpqrV1.ProtoRepr
  (V1StatePBGhost noneCap2 v1StateJumpTableBytes v1StatePBEncodedLen v1StatePBPinnedAt)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (hwVarintLen_bvShift_eq_ofNat_varintLen_norm hwVarintLen_eq_ofNat_varintLen_norm
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   ofNat_countLeadingZeros_32 ofNat_countLeadingZeros_64
   ule_self_64 ule_zero_64 ult_self_64 ult_zero_64
   zeroExtend64_beq_zero32 zext64_truncate32)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (StepInv blkPC_426 blkPl_426 cap_add_two_beq_zero_false cap_add_two_bne_zero_true
   cap_beq_len_false_of_lt cap_xor_top_ult_11_false encodeToVecCalleeStackOf
   noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap3 noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   optPqRatchetInnerCap optPqRatchetInnerPBPinnedAt optPqRatchetInnerPBPinnedAt_cap_bounds
   vecU8At_expose_header vecU8At_expose_one vecU8At_pack_one withStepInv)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsPlacedBudget
  (sepWP_done_tpidr sepWP_done_vm sepWPp_of_sepWP_cs_vm)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhaseBudget
  (encodeVarintExactSpecOf step_etv_encode_varint_call_prog)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlacedBudget
  (step_etv_v1State_encLen_call_placed)

/-- Symbol name for the `.rodata` jump table of `PqRatchetState::encode_to_vec`. -/
abbrev etvJumpTableRoSym : String :=
  CryptoVerification.SpqrV1.Prost.EncodeToVec.etvJumpTableRoSym

private theorem etv_or_80_truncate8_and_7f (a : BitVec 64) :
    (a.truncate 8 ||| 0x80#8) = ((a &&& 0x7F#64) ||| 0x80#64).setWidth 8 := by
  bv_bits

private theorem etv_protoEncodeVarintAux_eq_codec_of_lt (fuel : Nat) (a : BitVec 64)
    (hbound : a >>> (7 * fuel) < 0x80#64) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux (fuel + 1) a =
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux (fuel + 1) a := by
  induction fuel generalizing a with
  | zero =>
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero] at hbound
    have h' : a.toNat < 0x80 := BitVec.lt_def.mp hbound
    simp only [CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux, hbound, h', ↓reduceIte]
  | succ fuel ih =>
    rw [CryptoVerification.LibsignalSpqrV1.Proto.encodeVarintAux,
      CryptoVerification.LibsignalProtoCodec.encodeVarintAux]
    have hlt_iff : (a < 0x80#64) ↔ (a.toNat < 0x80) := BitVec.lt_def
    by_cases h : a < 0x80#64
    · have h' : a.toNat < 0x80 := hlt_iff.mp h
      simp only [h, h', ↓reduceIte]
    · have h' : ¬ a.toNat < 0x80 := fun hc => h (hlt_iff.mpr hc)
      have hb' : (a >>> 7) >>> (7 * fuel) < 0x80#64 := by
        have hsh : (a >>> 7) >>> (7 * fuel) = a >>> (7 * (fuel + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
            ← Nat.pow_add]
          congr 2; omega
        rw [hsh]; exact hbound
      simp only [h, h', ↓reduceIte, etv_or_80_truncate8_and_7f a, ih (a >>> 7) hb']
      rfl

theorem etv_protoEncodeVarint_eq_codec (a : BitVec 64) :
    CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint a =
      CryptoVerification.LibsignalProtoCodec.encodeVarint a := by
  refine etv_protoEncodeVarintAux_eq_codec_of_lt 9 a ?_
  change a >>> 63 < 0x80#64
  bv_bits

private theorem sepWPp_extract_pure {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp} (φ : Prop)
    (hφ : ∀ R : SepProp, s.mem ⊨ P ∗ R → φ)
    (hnext : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hnext (hφ R hm) R hm hL

private theorem sepWPp_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs : List (BitVec 8)} {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hhm : s.mem ⊨
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ : SepProp) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ F ∗ R) := by
    rw [hP, vecU8At_expose_header] at hm
    convert hm using 1; sep_ac_rfl
  rw [satisfies_pure_sepConj] at hhm
  exact h hhm.1.1 hhm.1.2.1 hhm.1.2.2 R hm hL

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm zext64_truncate32
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  cap_add_two_beq_zero_false cap_add_two_bne_zero_true cap_xor_top_ult_11_false
  ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-- Step `+1740 .. +1808` (`Block 426`) when `st.inner = none` (`x28 = noneCap3`), exposing
`VmPreserved s sm` across the branch. -/
theorem step_encodeToVec_inner_none_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    {s0 s : State}
    (sp : BitVec 64)
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = noneCap3) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm → VmPreserved s sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm P Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1808#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv.1) hinv.2

theorem step_encodeToVec_inner_none_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (sp : BitVec 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = noneCap3) (hinv0 : StepInv s0 s)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm (A.pool lim st sm ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  refine step_encodeToVec_inner_none_placed H sp hpc hrun hsp htr hx28 hinv0 ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinvm hvm
  rw [← A.pool_of_vmPreserved hvm]
  exact hnext sm hpcm hrunm hspm htrm hx27m hfpm hinvm

/-- Step `+1740 .. +1800` (`Block 426`) when `st.inner = some (.v1 v1)`:
writes outer tag `0x1a#8`, calls `V1State::encoded_len [local#2]` (`lsmpl.base 405`), and calls
`encode_varint` (`lsmpl.base 292`), threading `A.pool lim st`. -/
theorem step_encodeToVec_inner_some_hdr_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {roV1 : BitVec 64}
    {s0 s : State}
    (hv1Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A.repAlloc roV1)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A lim)))
    (a sp cap ptr : BitVec 64) (g : V1StatePBGhost) (v1 : V1State) (bs : List (BitVec 8))
    (hv1_len : v1StatePBEncodedLen v1 < 2 ^ 64)
    (hfit : bs.length + 1 +
      (CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
        (BitVec.ofNat 64 (v1StatePBEncodedLen v1))).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g (some (.v1 v1)))
    (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A.repAlloc g (a + 128#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1800#64 → sm.status = .Running → sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = a + 128#64 →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = optPqRatchetInnerCap g (some (.v1 v1)) →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((v1StatePBPinnedAt A.repAlloc g (a + 128#64) v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          vecU8At A.repAlloc (sp - 120#64) cap ptr
            ((bs ++ [0x1a#8]) ++
              CryptoVerification.LibsignalSpqrV1.Proto.encodeVarint
                (BitVec.ofNat 64 (v1StatePBEncodedLen v1))) ∗
          A.pool lim st sm ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 == 0#64) = false ∧
      (optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 != 0#64) = true)
    (fun R' hm => by
      have hm' : s.mem ⊨ optPqRatchetInnerPBPinnedAt A.repAlloc g (a + 128#64) (some (.v1 v1)) ∗
          ((roV1 ↦ᵣ v1StateJumpTableBytes) ∗
           vecU8At A.repAlloc (sp - 120#64) cap ptr bs ∗ A.pool lim st s ∗
           stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        dsimp only [optPqRatchetInnerPBPinnedAt]; convert hm using 1; sep_ac_rfl
      exact optPqRatchetInnerPBPinnedAt_cap_bounds hm')
    fun ⟨hw_beq3, hw_bne3⟩ => ?_
  have hlt1 : bs.length < cap.toNat := by omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := v1StatePBPinnedAt A.repAlloc g (a + 128#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ A.pool lim st s ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by sep_ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A.repAlloc (sp - 120#64) cap ptr bs hlt1 hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  rw [h112, h104]
  apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 405)
  by_vm_steps
    wp_steps
    apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, wp_norm, *])
    intro hinv1
    have hpack := vecU8At_pack_one A.repAlloc (sp - 120#64) cap ptr bs 0x1a#8 hlt1 hcap hptr
    rw [h112, h104] at hpack
    refine step_etv_v1State_encLen_call_placed hres A.repAlloc hv1Len
      (a + 128#64) sp ((blkPl_426).base + 1792#64) g v1 hv1_len
      (F := vecU8At A.repAlloc (sp - 120#64) cap ptr (bs ++ [0x1a#8]) ∗ A.pool lim st s ∗ F)
      (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
      (by simp only [arm64_norm, *]) (hinv0.trans hinv1.1)
      (by rw [← hpack]; sep_ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1 hvm_m1
    rcases hcsm1 with ⟨_, hm20, hm21, _, _, _, _, _, hm27, hm28, hmfp, _⟩
    simp only [arm64_norm, hx20, hx21, hx28] at hm20 hm21 hm27 hm28 hmfp
    apply sepWPp_of_sepWP_cs_vm (mid := lsmpl.base 292)
    by_vm_steps
      wp_steps
      apply sepWP_done_tpidr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, wp_norm, *])
      intro hinv2
      have hpool2 : A.pool lim st s = A.pool lim st _ :=
        (A.pool_of_vmPreserved (hinv1.2.trans (hvm_m1.trans hinv2.2))).symm
      refine step_etv_encode_varint_call_prog A lim st hvarint
        (BitVec.ofNat 64 (v1StatePBEncodedLen v1)) (sp - 120#64) cap ptr sp
        ((blkPl_426).base + 1800#64)
        (bs ++ [0x1a#8]) (by simpa only [List.length_append, List.length_singleton] using hfit)
        (F := v1StatePBPinnedAt A.repAlloc g (a + 128#64) v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F)
        (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (hinv_m1.trans hinv2.1) (by rw [hpool2]; sep_ac_rfl) ?_
      intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
      rcases hcsm2 with ⟨_, hm2_20, hm2_21, _, _, _, _, _, hm2_27, hm2_28, hm2_fp, _⟩
      simp only [arm64_norm, hm20, hm21, hm27, hm28, hmfp]
        at hm2_20 hm2_21 hm2_27 hm2_28 hm2_fp
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sm2 hpcm2 hrunm2 hspm2 htrm2 hm2_20 hm2_21 hm2_27 hm2_28 hm2_fp hinv_m2)

/-- Step `+1800 .. +1808` (`Block 426`) when `v1.innerState = none` (`x28 = noneCap2`), exposing
`VmPreserved s sm` across the branch. -/
theorem step_encodeToVec_inner_v1_none_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    {s0 s : State}
    (sp : BitVec 64)
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = noneCap2) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm → VmPreserved s sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm P Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1808#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv.1) hinv.2

theorem step_encodeToVec_inner_v1_none_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {s0 s : State}
    (sp : BitVec 64)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = noneCap2) (hinv0 : StepInv s0 s)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm (A.pool lim st sm ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  refine step_encodeToVec_inner_v1_none_placed H sp hpc hrun hsp htr hx28 hinv0 ?_
  intro sm hpcm hrunm hspm htrm hx27m hfpm hinvm hvm
  rw [← A.pool_of_vmPreserved hvm]
  exact hnext sm hpcm hrunm hspm htrm hx27m hfpm hinvm

/-- Step `+1800 .. +1880` (`Block 426`) when `v1.innerState = some is`, exposing `VmPreserved s sm`
across the jump-table index & base computation. -/
theorem step_encodeToVec_inner_to_1880_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    {roBase : BitVec 64} (hro : (blkPl_426).ρ etvJumpTableRoSym = roBase)
    {s0 s : State}
    (sp w : BitVec 64)
    (hw_beq : (w + 2#64 == 0#64) = false)
    (hw_bne : (w + 2#64 != 0#64) = true)
    {ret : BitVec 64} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = w) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1880#64 → sm.status = .Running → sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      sm.readReg64 .x9 = roBase →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = w →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm → VmPreserved s sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm P Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  apply sepWPp_of_sepWP_cs_vm (mid := (blkPl_426).base + 1880#64)
  wp_steps
  apply sepWP_done_vm (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, wp_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv.1) hinv.2

theorem step_encodeToVec_inner_to_1880_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (H : String → Option (State → State))
    {roBase : BitVec 64} (hro : (blkPl_426).ρ etvJumpTableRoSym = roBase)
    {s0 s : State}
    (sp w : BitVec 64)
    (hw_beq : (w + 2#64 == 0#64) = false)
    (hw_bne : (w + 2#64 != 0#64) = true)
    {ret : BitVec 64} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (blkPl_426).base + 1800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = w) (hinv0 : StepInv s0 s)
    (hP : P = A.pool lim st s ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1880#64 → sm.status = .Running → sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      sm.readReg64 .x9 = roBase →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = w →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm (A.pool lim st sm ∗ F) Q Qp oom) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q Qp oom := by
  subst hP
  refine step_encodeToVec_inner_to_1880_placed H hro sp w hw_beq hw_bne hpc hrun hsp htr hx28 hinv0 ?_
  intro sm hpcm hrunm hspm htrm hx8m hx9m hx20m hx21m hx27m hx28m hfpm hinvm hvm
  rw [← A.pool_of_vmPreserved hvm]
  exact hnext sm hpcm hrunm hspm htrm hx8m hx9m hx20m hx21m hx27m hx28m hfpm hinvm

end LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeaderPlacedBudget
