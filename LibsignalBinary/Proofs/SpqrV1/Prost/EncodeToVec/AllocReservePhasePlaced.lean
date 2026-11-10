/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodeToVecCodeSym
import ProofLib.SepLogic.WPp

/-!
# `PqRatchetState::encode_to_vec` (Block `426`): Placed Buffer Allocation, Epilogue, and Call Wrappers

Relocatable `[LibsignalPlacement]` epilogue (`+1808..+1856`), initial `Vec<u8>` allocation
(`+516..+580` / `+792..+812`), and program-polymorphic exact-capacity callee wrappers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (ofNat_length_beq_zero_of_lt bv_u32VarintField_nonzero bv_bytesField_nonempty
   bv_add_ofNat_comm bv_add_ofNat_eq adds_no_overflow_of_eq cmp_ls_false_of_lt)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

/-! ## 1. Epilogue (`+1808..+1856`) -/

theorem step_encodeToVec_epilogue_placed [LibsignalPlacement]
    {resStack : Nat} (hres : resStack + 320 < 2 ^ 64)
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State} (sret sp cap ptr v0 v1 v2 : BitVec 64) (bs : List (BitVec 8))
    {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 1808#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx27 : s.readReg64 .x27 = sret)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A (sp - 120#64) cap ptr bs ∗
      memRegion sret 24 ∗
      ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
      encodeToVecSavedRegs sp s0 ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hret : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      StepInv s0 sf →
      Q sf ((vecU8 A sret bs ∗ stackAt sp (encodeToVecStackOf resStack)) ∗ F)) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP; unfold encodeToVecSavedRegs
  rw [vecU8At_expose_header A (sp - 120#64) cap ptr bs, memRegion_24_eq sret]
  have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
  have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
  rw [h112, h104]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun s2_v => SepWPp.exists_elim fun s1_v => SepWPp.exists_elim fun s0_v => ?_
  apply SepWPp.of_sepWP_cs (mid := s0.readReg64 .lr); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hret _ (by simp only [arm64_norm])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by epochEncLen_cc_close) (hinv0.trans hinv1)))
  refine sepConj_mono_left ?_
  refine Entails.trans ?_
    (sepConj_mono_right (stackAt_encodeToVec_recombine hres sp v0 v1 v2 cap ptr (BitVec.ofNat 64 bs.length) s0))
  unfold vecU8 encodeToVecLocalSlots encodeToVecSavedRegs
  refine Entails.trans ?_
    (sepConj_mono_left (Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))))
  rw [vecU8At_expose_header A sret cap ptr bs]
  exact Entails.of_eq (by ac_rfl)

/-! ## 2. Initial Buffer Allocation (`+516..+580` and `+792..+812`) -/

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_beq_zero_false_of_pos {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n = 0 at ht
  omega

theorem step_encodeToVec_alloc_placed [LibsignalPlacement] {resStack : Nat}
    (A : RustAlloc) (H : String → Option (State → State))
    {s0 s : State}
    (hshim : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStepInv s0 (shimStackSpecOf resStack)))
    (halloc : subroutine_ok ((blkPC_426).rebase (blkPl_426).base H)
      ((blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (withStepInv s0 (rustAllocStackSpecOf resStack A)))
    (hhandle : ((blkPC_426).rebase (blkPl_426).base H).externAt?
      ((blkPl_426).ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked)
    (sret a sp v0 v1 v2 v3 v4 v5 : BitVec 64) (g : PqRatchetStatePBGhost) (st : PqRatchetState)
    (hlen : pqRatchetStatePBEncodedLen st < 2 ^ 63) (halign : sp &&& 15#64 = 0#64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_426).base + 516#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = optChainCap g.chain st.chain)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = a + 128#64)
    (hx22 : s.readReg64 .x22 = a + 48#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st))
    (hx25 : s.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation)
    (hx27 : s.readReg64 .x27 = sret)
    (hx28 : s.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner)
    (hfp : s.readReg64 .fp = sp - 96#64)
    (hinv0 : StepInv s0 s)
    (hP : P = (pqRatchetStatePBPinnedAt A g a st ∗
      A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
      encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
      encodeToVecSavedRegs sp s0) ∗ F)
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      sm.pc = (if st.versionNegotiation.isSome then (blkPl_426).base + 580#64 else (blkPl_426).base + 1212#64) →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      (st.versionNegotiation.isSome → sm.readReg64 .x0 = ptr) →
      sm.readReg64 .x19 = optChainCap g.chain st.chain →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = a + 128#64 →
      sm.readReg64 .x22 = a + 48#64 →
      sm.readReg64 .x25 = optVersionNegCap g.vn st.versionNegotiation →
      sm.readReg64 .x27 = sret →
      sm.readReg64 .x28 = optPqRatchetInnerCap g.inner st.inner →
      sm.readReg64 .fp = sp - 96#64 →
      StepInv s0 sm →
      SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret sm
        ((pqRatchetStatePBPinnedAt A g a st ∗
          vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr [] ∗
          A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
          ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ∗
          encodeToVecSavedRegs sp s0) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_426).rebase (blkPl_426).base H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  subst hP
  have hbit63 := getLsbD_63_ofNat_eq_false hlen
  have helem63 := getElem_63_ofNat_eq_false hlen
  refine sepWPp_extract_pure
    ((optVersionNegCap g.vn st.versionNegotiation + 1#64 == 0#64) = !st.versionNegotiation.isSome ∧
     (optVersionNegCap g.vn st.versionNegotiation + 1#64 != 0#64) = st.versionNegotiation.isSome)
    (fun R' hm => by
      unfold pqRatchetStatePBPinnedAt at hm
      rw [optVersionNegotiationPBPinnedAt_eq] at hm
      have hm' : s.mem ⊨ optVersionNegRest A g.vn a st.versionNegotiation ∗
          ((a ↦₆₄ optVersionNegCap g.vn st.versionNegotiation) ∗
           optChainPBPinnedAt A g.chain (a + 48#64) st.chain ∗
           optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner ∗
           A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack) ∗
           encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗
           encodeToVecSavedRegs sp s0 ∗ F ∗ R') := by
        convert hm using 1; ac_rfl
      exact optVersionNegRest_cap_bounds hm')
    fun ⟨hvn_eq, hvn_ne⟩ => ?_
  by_cases hzero : pqRatchetStatePBEncodedLen st = 0
  · obtain ⟨hvn_none, _, _, _⟩ := pqRatchetState_fields_none_of_encodedLen_zero hzero
    have hx23_0 : s.readReg64 .x23 = 0#64 := by rw [hx23, hzero]
    rw [hvn_none] at hvn_eq hvn_ne
    simp only [Option.isSome_none, Bool.not_false] at hvn_eq hvn_ne
    unfold encodeToVecLocalSlots
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1212#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.weaken_pre ?_
      (hnext _ 1#64
        (by rw [hvn_none]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *])
        (fun h => by rw [hvn_none] at h; cases h)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv0.trans hinv1))
    rw [hzero, ← vecU8At_empty_zero A (sp - 120#64)]
    have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
    have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
    rw [h112, h104]
    exact Entails.of_eq (by ac_rfl)
  · have hpos : 0 < pqRatchetStatePBEncodedLen st := Nat.pos_of_ne_zero hzero
    have hcbz_f := ofNat_beq_zero_false_of_pos hpos hlen
    apply SepWPp.of_sepWP_cs (mid := (blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2"); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv1
    refine SepWPp.call_cs (x := ())
      (F := pqRatchetStatePBPinnedAt A g a st ∗ A.pool ∗
        encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗ encodeToVecSavedRegs sp s0 ∗ F)
      hshim (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
      (by simp only [State.spAligned, arm64_norm, hsp, beq_iff_eq]; exact halign)
      (ret_pc := (blkPl_426).base + 544#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
    · intro R' hm
      simp only [arm64_norm] at hm
      simp only [withStepInv, shimStackSpecOf, arm64_norm, hsp, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hinv0.trans hinv1, ?_⟩
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
    · intro sf code R' _ hm; exact allowPanic_not_exited hm
    · intro sf _ hm
      simp only [withStepInv, shimStackSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hm
      exact hm.1.elim
    · intro s1 hpcs1 hruns1 hsps1 hcss1 hinv_s1
      simp only [arm64_norm, hsp] at hsps1
      obtain ⟨hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_24, hs1_25, hs1_26, hs1_27, hs1_28, hs1_fp, _⟩ :=
        calleeSavedPreserved_writeLr_setPC hcss1
      rw [hx19] at hs1_19; rw [hx20] at hs1_20; rw [hx21] at hs1_21; rw [hx22] at hs1_22; rw [hx23] at hs1_23
      rw [hx25] at hs1_25; rw [hx27] at hs1_27; rw [hx28] at hs1_28; rw [hfp] at hs1_fp
      dsimp only [withStepInv, shimStackSpecOf]
      simp only [arm64_norm, hsp, sepConj_assoc]
      refine SepWPp.pure_elim fun htrs1 => ?_
      have htrs1' : s1.trace = s0.trace := htrs1.trans htr
      apply SepWPp.of_sepWP_cs (mid := (blkPl_426).ρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc"); wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hinv2
      have htoNat_len : (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)).toNat = pqRatchetStatePBEncodedLen st := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine SepWPp.call_cs (x := pqRatchetStatePBEncodedLen st)
        (F := pqRatchetStatePBPinnedAt A g a st ∗
          encodeToVecLocalSlots sp v0 v1 v2 v3 v4 v5 ∗ encodeToVecSavedRegs sp s0 ∗ F)
        halloc (by simp only [arm64_norm]) (by simp only [arm64_norm, *])
        (by simp only [State.spAligned, arm64_norm, hsps1, beq_iff_eq]; exact halign)
        (ret_pc := (blkPl_426).base + 560#64) (by simp only [arm64_norm]) ?_ ?_ ?_ ?_
      · intro R' hm
        simp only [arm64_norm] at hm
        simp only [withStepInv, rustAllocStackSpecOf, arm64_norm, hsps1, htoNat_len,
          sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨(hinv0.trans hinv1).trans (hinv_s1.trans hinv2), hpos, hlen⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
      · intro sf code R' _ hm; exact allowPanic_not_exited hm
      · intro sf _ hm
        simp only [withStepInv, rustAllocStackSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hm
        exact hm.1.elim
      · intro s2 hpcs2 hruns2 hsps2 hcss2 hinv_s2
        simp only [arm64_norm, hsps1] at hsps2
        obtain ⟨hs2_19, hs2_20, hs2_21, hs2_22, hs2_23, hs2_24, hs2_25, hs2_26, hs2_27, hs2_28, hs2_fp, _⟩ :=
          calleeSavedPreserved_writeLr_setPC hcss2
        simp only [arm64_norm, hs1_19, hs1_20, hs1_21, hs1_22, hs1_23, hs1_25, hs1_27, hs1_28, hs1_fp]
          at hs2_19 hs2_20 hs2_21 hs2_22 hs2_23 hs2_25 hs2_27 hs2_28 hs2_fp
        have hinv_s2' : StepInv s0 s2 :=
          ((hinv0.trans hinv1).trans (hinv_s1.trans hinv2)).trans hinv_s2
        dsimp only [withStepInv, rustAllocStackSpecOf]
        simp only [arm64_norm, hsps1]
        by_cases hoom : s2.readReg64 .x0 = 0#64
        · simp only [hoom, ↓reduceIte]
          refine SepWPp.pure_elim fun htrs2 => ?_
          have htrs2' : s2.trace = s0.trace ++ [allocFailedEvent] := by rw [htrs2, htrs1']
          apply SepWPp.of_sepWP (mid := (blkPl_426).ρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"); wp_steps
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm_pan => ?_
          exact encodeToVecOnPanic_of_trace
            (by simpa only [Rust.panicked, wp_norm, arm64_norm] using htrs2') hm_pan
        · have hoom_f : (s2.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
          simp only [hoom, ↓reduceIte, sepConj_assoc]
          refine SepWPp.pure_elim fun htrs2 => ?_
          have htrs2' : s2.trace = s0.trace := htrs2.trans htrs1'
          unfold encodeToVecLocalSlots
          cases hvn_case : st.versionNegotiation with
          | none =>
            rw [hvn_case] at hvn_eq hvn_ne
            simp only [Option.isSome_none, Bool.not_false] at hvn_eq hvn_ne
            apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 1212#64); wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            intro hinv3
            refine SepWPp.weaken_pre ?_
              (hnext _ (s2.readReg64 .x0)
                (by rw [hvn_case]; simp only [Bool.false_eq_true, ↓reduceIte, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (fun h => by rw [hvn_case] at h; cases h)
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3))
            rw [← vecU8At_empty_of_alloc A (sp - 120#64) (s2.readReg64 .x0) (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
            have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
            have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
            rw [h112, h104]
            exact Entails.of_eq (by ac_rfl)
          | some vn =>
            rw [hvn_case] at hvn_eq hvn_ne
            simp only [Option.isSome_some, Bool.not_true] at hvn_eq hvn_ne
            apply SepWPp.of_sepWP_cs (mid := (blkPl_426).base + 580#64); wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            intro hinv3
            refine SepWPp.weaken_pre ?_
              (hnext _ (s2.readReg64 .x0)
                (by rw [hvn_case]; simp only [↓reduceIte, arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (fun _ => by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (hinv_s2'.trans hinv3))
            rw [← vecU8At_empty_of_alloc A (sp - 120#64) (s2.readReg64 .x0) (pqRatchetStatePBEncodedLen st) hpos hlen hoom]
            have h112 : (sp - 120#64) + 8#64 = sp - 112#64 := by bv_omega
            have h104 : (sp - 120#64) + 16#64 = sp - 104#64 := by bv_omega
            rw [h112, h104]
            exact Entails.of_eq (by ac_rfl)

/-! ## 3. Exact-Capacity Callee Call Wrappers for Any `Program` -/

theorem step_etv_encode_varint_call_prog {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc
      (withStepInv s0 (encodeVarintExactSpecOf resStack A)))
    (val v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeVarint val).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v cap ptr (bs ++ Proto.encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := ⟨val, v, cap, ptr, bs⟩) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeVarintExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, encodeVarintExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeVarintExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_memcpy_call_prog
    {prog : Program}
    {call_pc : BitVec 64} {s0 s : State}
    (hmemcpy : subroutine_ok prog call_pc etvMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hinv0 : StepInv s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [etvMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [etvMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [etvMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_chainParams_call_prog {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hcp : subroutine_ok prog call_pc
      (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)))
    (tag : BitVec 32) (p : ChainParamsPB) (v cap ptr sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    (htag1 : 1 ≤ tag.toNat) (htag2 : tag.toNat < 2 ^ 29)
    (hfit : bs.length + (Proto.encodeMessage ChainParamsPB.encodeRaw tag p).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hw1 : s.readReg32 .x1 = p.maxJump)
    (hw2 : s.readReg32 .x2 = p.maxOooKeys)
    (hx3 : s.readReg64 .x3 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (vecU8At A v cap ptr bs ∗ A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v cap ptr (bs ++ Proto.encodeMessage ChainParamsPB.encodeRaw tag p) ∗ A.pool ∗
          stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := ⟨tag, p, v, cap, ptr, bs⟩) (F := F)
    hcp hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeChainParamsExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hw1, hw2, hx3, htag1, htag2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, encodeChainParamsExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeChainParamsExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_epoch_encLen_call_prog {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hep : subroutine_ok prog call_pc
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)))
    (a sp ret_pc : BitVec 64) (g : ChainEpochPBGhost) (ep : ChainEpochPB)
    (hlen : chainEpochPBEncodedLen ep < 2 ^ 64)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = a)
    (hinv0 : StepInv s0 s)
    (hP : P = (chainEpochPBPinnedAt A g a ep ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((chainEpochPBPinnedAt A g a ep ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := (a, g, ep)) (F := F)
    hep hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, epochEncLenStackSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hlen⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [withStepInv, epochEncLenStackSpecOf, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, epochEncLenStackSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hx0m hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_epochDirection_call_prog {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hed : subroutine_ok prog call_pc
      (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)))
    (tag : BitVec 32) (dirA v cap ptr sp ret_pc : BitVec 64)
    (g : EpochDirectionPBGhost) (dir : EpochDirectionPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage EpochDirectionPB.encodeRaw tag dir).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = dirA)
    (hx2 : s.readReg64 .x2 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (epochDirectionPBPinnedAt A g dirA dir ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((epochDirectionPBPinnedAt A g dirA dir ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage EpochDirectionPB.encodeRaw tag dir) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := ⟨tag, dirA, g, dir, v, cap, ptr, bs⟩) (F := F)
    hed hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, encodeEpochDirectionExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, encodeEpochDirectionExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, encodeEpochDirectionExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

theorem step_etv_encode_auth_call_prog {resStack : Nat}
    {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (hauth : subroutine_ok prog call_pc
      (withStepInv s0 (authEncodeExactSpecOf resStack A)))
    (authA v cap ptr sp ret_pc : BitVec 64)
    (g : AuthenticatorPBGhost) (auth : AuthenticatorPB) (bs : List (BitVec 8))
    (hfit : bs.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth).length ≤ cap.toNat)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 144#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = authA)
    (hx1 : s.readReg64 .x1 = v)
    (hinv0 : StepInv s0 s)
    (hP : P = (authenticatorPBPinnedAt A g authA auth ∗ vecU8At A v cap ptr bs ∗ A.pool ∗
      stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp - 144#64 →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      StepInv s0 sm →
      SepWPp prog ret sm
        ((authenticatorPBPinnedAt A g authA auth ∗
          vecU8At A v cap ptr (bs ++ Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 auth) ∗
          A.pool ∗ stackAt (sp - 144#64) (encodeToVecCalleeStackOf resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_144_aligned halign
  refine SepWPp.call_cs (x := ⟨authA, g, auth, v, cap, ptr, bs⟩) (F := F)
    hauth hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP] at hm
    simp only [withStepInv, authEncodeExactSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withStepInv, authEncodeExactSpecOf, encodeToVecOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withStepInv, authEncodeExactSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm (hinv0.trans hinv_call))

end CryptoVerification.SpqrV1.Prost.EncodeToVec
