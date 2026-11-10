/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhasePlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Phase 2d Header & Jump-Table Dispatch (`Block 426`, `+1740 .. +1896`)

Proves `[LibsignalPlacement]` symbolic execution of the `st.inner` and `v1.innerState` header
branches (`+1740 .. +1880`) up to the `.rodata` jump-table load at `(blkPl_426).base + 1880#64`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  cap_add_two_beq_zero_false cap_add_two_bne_zero_true cap_xor_top_ult_11_false
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-- Symbol name for the `.rodata` jump table of `PqRatchetState::encode_to_vec` (`libsignalSessionLib.data[549]`). -/
abbrev etvJumpTableRoSym : String :=
  "spqr:.rodata.<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"

/-- Step `+1740 .. +1808` (`Block 426`) when `st.inner = none` (`x28 = noneCap3`). -/
theorem step_encodeToVec_inner_none_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    {s0 s : State}
    (sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = noneCap3) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv)

/-- Step `+1740 .. +1800` (`Block 426`) when `st.inner = some (.v1 v1)`:
writes outer tag `0x1a#8`, calls `V1State::encoded_len [local#2]` (`lsmpl.base 405`), and calls
`encode_varint` (`lsmpl.base 292`). -/
theorem step_encodeToVec_inner_some_hdr_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {roV1 : BitVec 64}
    {s0 s : State}
    (hv1Len : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 405)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A roV1)))
    (hvarint : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H) (lsmpl.base 292)
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (a sp cap ptr : BitVec 64) (g : V1StatePBGhost) (v1 : V1State) (bs : List (BitVec 8))
    (hv1_len : v1StatePBEncodedLen v1 < 2 ^ 64)
    (hfit : bs.length + 1 +
      (Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))).length ≤ cap.toNat)
    (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1740#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g (some (.v1 v1)))
    (hinv0 : StepInv s0 s)
    (hP : P = (v1StatePBPinnedAt A g (a + 128#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
      vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1800#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x20 = a → sm.readReg64 .x21 = a + 128#64 →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = optPqRatchetInnerCap g (some (.v1 v1)) →
      sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((v1StatePBPinnedAt A g (a + 128#64) v1 ∗
          (roV1 ↦ᵣ v1StateJumpTableBytes) ∗
          vecU8At A (sp - 120#64) cap ptr
            ((bs ++ [0x1a#8]) ++ Proto.encodeVarint (BitVec.ofNat 64 (v1StatePBEncodedLen v1))) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_pure
    ((optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 == 0#64) = false ∧
      (optPqRatchetInnerCap g (some (.v1 v1)) + 3#64 != 0#64) = true)
    (fun R' hm => by
      have hm' : s.mem ⊨ optPqRatchetInnerPBPinnedAt A g (a + 128#64) (some (.v1 v1)) ∗
          ((roV1 ↦ᵣ v1StateJumpTableBytes) ∗
           vecU8At A (sp - 120#64) cap ptr bs ∗ A.pool ∗
           stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F ∗ R') := by
        dsimp only [optPqRatchetInnerPBPinnedAt]; convert hm using 1; ac_rfl
      exact optPqRatchetInnerPBPinnedAt_cap_bounds hm')
    fun ⟨hw_beq3, hw_bne3⟩ => ?_
  have hlt1 : bs.length < cap.toNat := by omega
  refine sepWPp_extract_vecU8At_bounds (v := sp - 120#64) (cap := cap) (ptr := ptr) (bs := bs)
    (F := v1StatePBPinnedAt A g (a + 128#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗ F)
    (by ac_rfl) fun _ hcap hptr => ?_
  have hbeq_false := cap_beq_len_false_of_lt hlt1 hcap
  rw [vecU8At_expose_one A (sp - 120#64) cap ptr bs hlt1 hcap hptr]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  rw [h112, h104]
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 405); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  have hpack := vecU8At_pack_one A (sp - 120#64) cap ptr bs 0x1a#8 hlt1 hcap hptr
  rw [h112, h104] at hpack
  refine step_etv_v1State_encLen_call_placed hres A hv1Len
    (a + 128#64) sp ((blkPl_426).base + 1792#64) g v1 hv1_len
    (F := vecU8At A (sp - 120#64) cap ptr (bs ++ [0x1a#8]) ∗ A.pool ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv1)
    (by rw [← hpack]; ac_rfl) ?_
  intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx0m1 hcsm1 hinv_m1
  rcases hcsm1 with ⟨_, hm20, hm21, _, _, _, _, _, hm27, hm28, hmfp, _⟩
  simp only [arm64_norm, hx20, hx21, hx28] at hm20 hm21 hm27 hm28 hmfp
  apply SepWPp.of_sepWP_cs (mid := lsmpl.base 292); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv2
  refine step_etv_encode_varint_call_prog A hvarint
    (BitVec.ofNat 64 (v1StatePBEncodedLen v1)) (sp - 120#64) cap ptr sp ((blkPl_426).base + 1800#64)
    (bs ++ [0x1a#8]) (by simpa only [List.length_append, List.length_singleton] using hfit)
    (F := v1StatePBPinnedAt A g (a + 128#64) v1 ∗
      (roV1 ↦ᵣ v1StateJumpTableBytes) ∗ F)
    (by simp only [arm64_norm]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv_m1.trans hinv2) (by ac_rfl) ?_
  intro sm2 hpcm2 hrunm2 hspm2 htrm2 hcsm2 hinv_m2
  rcases hcsm2 with ⟨_, hm2_20, hm2_21, _, _, _, _, _, hm2_27, hm2_28, hm2_fp, _⟩
  simp only [arm64_norm, hm20, hm21, hm27, hm28, hmfp] at hm2_20 hm2_21 hm2_27 hm2_28 hm2_fp
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext sm2 hpcm2 hrunm2 hspm2 htrm2 hm2_20 hm2_21 hm2_27 hm2_28 hm2_fp hinv_m2)

/-- Step `+1800 .. +1808` (`Block 426`) when `v1.innerState = none` (`x28 = noneCap2`). -/
theorem step_encodeToVec_inner_v1_none_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    {s0 s : State}
    (sp : BitVec 64)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = noneCap2) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1808#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .fp = s.readReg64 .fp →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1808#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hinv0.trans hinv)

/-- Step `+1800 .. +1880` (`Block 426`) when `v1.innerState = some is`:
branches to `+1856`, computes jump-table index in `x8`, and loads `.rodata` jump-table base
address `roBase` (`= (blkPl_426).ρ etvJumpTableRoSym`) into `x9` via `blkPC_426_pairStep_0x750`. -/
theorem step_encodeToVec_inner_to_1880_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    {roBase : BitVec 64} (hro : (blkPl_426).ρ etvJumpTableRoSym = roBase)
    {s0 s : State}
    (sp w : BitVec 64)
    (hw_beq : (w + 2#64 == 0#64) = false)
    (hw_bne : (w + 2#64 != 0#64) = true)
    {R : SepProp} {ret : BitVec 64} {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1800#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64) (htr : s.trace = s0.trace)
    (hx28 : s.readReg64 .x28 = w) (hinv0 : StepInv s0 s)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_426).base + 1880#64 → sm.status = .Running → sm.sp = sp - 144#64 → sm.trace = s0.trace →
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
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm P
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1880#64)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (hinv0.trans hinv)

end CryptoVerification.SpqrV1.Prost.EncodeToVec
