/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX
public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.KyberBaseKeyPqStateX
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ReceiverChainsPendingPreKeyXPlaced
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable `SessionStructure::clone` Fields 7–9 (Block `80`)

Verifies cloning of `pending_kyber_pre_key`, `alice_base_key`, and `pq_ratchet_state`
(`+592..+924`) in Block `80` (`SessionStructure::clone`) under `[LibsignalPlacement]`.
-/

namespace CryptoVerification.E2E.Record.Serialization.SessionCloneAux

open Arm64 Arm64.Obj ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
  CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (ChainCloneLocal1Ok SenderChainCloneLocal1Ok)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open Proofs.libsignal
open Proofs.libsignal.Hooks2
open Proofs.libsignal.Stage1X
open ProofLib.ProgramReflection

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
  updateCalleeSavedVRegs
  Arm64.State.calleeSavedVRegs_writeReg64_gpr
  Arm64.State.calleeSavedVRegs_writeReg32_gpr
  Arm64.State.calleeSavedVRegs_setPC
  Arm64.State.calleeSavedVRegs_setPState
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section Placed

/-! ## Field 7: `pending_kyber_pre_key` (`+592 ∨ +648 → +608 ∨ +884 ∨ +720`) -/

theorem sc_pendingKyber_2a4_pos_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gk : TailVecGhost} {kw0 kw1 : BitVec 32}
    {v10 v40 : BitVec 64} {F : SepProp}
    (htail : gk.tail.length = 32 - 24)
    (htail_pts : ∀ a : BitVec 64,
      (a ↦ₛ gk.tail) = ((a ↦₃₂ kw0) ∗ ((a + 4#64) ↦₃₂ kw1)))
    (htail_val : gk.tail = unpack32 kw0 ++ unpack32 kw1)
    (hpos : 0 < gk.vec.bytes.length)
    (hlen_le : gk.vec.bytes.length ≤ gk.vec.cap.toNat)
    (hcap_lt : gk.vec.cap.toNat < 2 ^ 63)
    (hptr : gk.vec.ptr ≠ 0)
    (hpc : s.pc = (blkPl_80).base + 676#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 gk.vec.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v28' : BitVec 32),
      (s1.pc = (blkPl_80).base + 608#64 ∨
       s1.pc = (blkPl_80).base + 884#64 ∨
       s1.pc = (blkPl_80).base + 720#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      s1.calleeSavedVRegs = s.calleeSavedVRegs →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗
          (⌜gk.tail.length = 32 - 24⌝ ∗
            vecGhostAt A gk.vec (x.src + 0x128#64) ∗
            ((x.src + 0x128#64 + BitVec.ofNat 64 24) ↦ₛ gk.tail)) ∗
          (⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length ∧
              ∃ kw1' : BitVec 32, gk.tail = unpack32 v28' ++ unpack32 kw1'⌝ ∗
            vecU8Buf A kybCap' kybPtr' gk.vec.bytes) ∗
          ((s.sp + 0x10#64) ↦₆₄ kybPtr') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x40#64) ↦₆₄ kybCap') ∗
          stackAt s.sp Stage1X.extHookStack ∗
          F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗
        ((x.src + 0x128#64) ↦₆₄ gk.vec.cap) ∗
        ((x.src + 0x130#64) ↦₆₄ gk.vec.ptr) ∗
        ((x.src + 0x138#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length) ∗
        (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
        A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
        memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length)
          (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
        ((x.src + 0x140#64) ↦₃₂ kw0) ∗
        ((x.src + 0x144#64) ↦₃₂ kw1) ∗
        ((s.sp + 0x10#64) ↦₆₄ v10) ∗
        ((s.sp + 0x28#64) ↦₃₂ kw0) ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗
        stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  intro hcl
  have hshim := sc_shim_placed_ok_at_x hC
  have halloc := sc_alloc_placed_ok_at_x hC
  have hmemcpy := sc_memcpy_placed_ok_at_x hC
  have h130 : x.src + 0x128#64 + 8#64 = x.src + 0x130#64 := by bv_arith
  have h138 : x.src + 0x128#64 + 16#64 = x.src + 0x138#64 := by bv_arith
  have h140 : x.src + 0x128#64 + BitVec.ofNat 64 24 = x.src + 0x140#64 := by bv_arith
  have h144 : x.src + 0x140#64 + 4#64 = x.src + 0x144#64 := by bv_arith
  have hlen_lt : gk.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gk.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gk.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk gk.vec.bytes.length 1 := ⟨hpos, hpow2, hlen_le63⟩
  have htoNat : (BitVec.ofNat 64 gk.vec.bytes.length).toNat = gk.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 680#64)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_shim
  have hshim_state := shim_placed_ok_at_stateX hshim hcl_shim
  apply sepWPp_of_sepWP_lscl_sc hcl_shim (mid := (blkPl_80).base + 684#64)
  wp_steps
  wp_call hshim_state ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_alloc
  have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
  apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := (blkPl_80).base + 696#64)
  wp_steps
  wp_call halloc_state (gk.vec.bytes.length, 1)
  clear halloc halloc_state
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 1140#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_panic
    refine sc_panic_0x474_placed_x hC x s0 _ _ R ?_ ?_ ?_ hcl_panic
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · change sf_1.trace = s0.trace ++ [allocFailedEvent]
      rw [htrace_alloc_oom, hpost, htr]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod, htrace_alloc_ok⟩ => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 716#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_memcpy
    have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_memcpy
    apply sepWPp_of_sepWP_lscl_sc hcl_memcpy (mid := (blkPl_80).base + 720#64)
    wp_steps
    wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), gk.vec.ptr, gk.vec.bytes)
    clear hmemcpy hmemcpy_state
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_post_memcpy
    have hsp_eq : sf.sp = s.sp := by sc_close3X
    have hsf1_sp : sf_1.sp = s.sp := by sc_close3X
    refine SepWPp.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gk.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) kw0
        (Or.inr (Or.inr (by sc_close3X))) (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
        hcl_post_memcpy)
    have h_rfl : (⌜BitVec.ofNat 64 gk.vec.bytes.length = BitVec.ofNat 64 gk.vec.bytes.length ∧
        ∃ kw1' : BitVec 32, gk.tail = unpack32 kw0 ++ unpack32 kw1'⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨rfl, kw1, htail_val⟩
    have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp :=
      segClone_pure_eq_emp htail
    have h_pure2 : (⌜gk.vec.bytes.length ≤ gk.vec.cap.toNat ∧ gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_pos A gk.vec (x.src + 0x128#64) hpos, h130, h138,
        h140, htail_pts (x.src + 0x140#64), h144,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) gk.vec.bytes hpos hlen_lt hoom64,
        h_rfl, h_pure1, h_pure2]
    simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Field 7 (`+592 ∨ +648 → +608 ∨ +884 ∨ +720`) on `lsProg_80 H`. -/
theorem sc_pendingKyber_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v10 v40 : BitVec 64} {v28 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 592#64 ∨
           s.pc = (blkPl_80).base + 648#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v28' : BitVec 32),
      (s1.pc = (blkPl_80).base + 608#64 ∨
       s1.pc = (blkPl_80).base + 884#64 ∨
       s1.pc = (blkPl_80).base + 720#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → s1.calleeSavedVRegs = s.calleeSavedVRegs →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗ optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
          ScOptKybClone A x.G.kyber kybCap' kybPtr' v28' ∗
          ((s.sp + 0x10#64) ↦₆₄ kybPtr') ∗ ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x40#64) ↦₆₄ kybCap') ∗ stackAt s.sp Stage1X.extHookStack ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗ optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
        ((s.sp + 0x10#64) ↦₆₄ v10) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗ stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  cases hkyb : x.G.kyber with
  | none =>
    clear hC
    rw [hkyb] at hnext
    dsimp only [optTailVecAt, ScOptKybClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    rcases hpc with hpc | hpc
    · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 608#64)
      wp_steps
      refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v10 v28
          (Or.inl (by sc_close3X)) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 608#64)
      wp_steps
      refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v10 v28
          (Or.inl (by sc_close3X)) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  | some gk =>
    rw [hkyb] at hnext
    dsimp only [optTailVecAt, ScOptKybClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPpLsCl_pure_2nd fun htail => ?_
    obtain ⟨kw0, kw1, htail_val, htail_pts⟩ := exists_unpack32_pair_of_length_8 htail
    have h130 : x.src + 0x128#64 + 8#64 = x.src + 0x130#64 := by bv_arith
    have h138 : x.src + 0x128#64 + 16#64 = x.src + 0x138#64 := by bv_arith
    have h140 : x.src + 0x128#64 + BitVec.ofNat 64 24 = x.src + 0x140#64 := by bv_arith
    have h144 : x.src + 0x140#64 + 4#64 = x.src + 0x144#64 := by bv_arith
    rw [h140, htail_pts (x.src + 0x140#64), h144]
    rcases eq_nil_or_length_pos gk.vec.bytes with hnil | hpos
    · clear hC
      rw [vecGhostAt_eq_of_nil A gk.vec (x.src + 0x128#64) hnil, h130, h138]
      simp only [sepConj_assoc]
      refine sepWPpLsCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length ∧
          ∃ kw1' : BitVec 32, gk.tail = unpack32 kw0 ++ unpack32 kw1'⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨rfl, kw1, htail_val⟩
      have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      rcases hpc with hpc | hpc
      · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 884#64)
        wp_steps
        refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
        refine SepWPpLsCl.weaken_pre ?_
          (hnext _ 0#64 1#64 kw0
            (Or.inr (Or.inl (by sc_close3X))) (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X))
        rw [vecGhostAt_eq_of_nil A gk.vec (x.src + 0x128#64) hnil, h130, h138,
            h140, htail_pts (x.src + 0x140#64), h144, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
      · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 884#64)
        wp_steps
        refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
        refine SepWPpLsCl.weaken_pre ?_
          (hnext _ 0#64 1#64 kw0
            (Or.inr (Or.inl (by sc_close3X))) (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X))
        rw [vecGhostAt_eq_of_nil A gk.vec (x.src + 0x128#64) hnil, h130, h138,
            h140, htail_pts (x.src + 0x140#64), h144, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gk.vec (x.src + 0x128#64) hpos, h130, h138]
      simp only [sepConj_assoc]
      refine sepWPpLsCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hlen_lt : gk.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gk.vec.bytes.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gk.vec.bytes.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hsub : ∀ (s_2a4 : State), _ := fun s_2a4 =>
        sc_pendingKyber_2a4_pos_placed_x hC (x := x) (R := R) (s0 := s0) (s := s_2a4) (ret := ret) (Q := Q)
          (gk := gk) (kw0 := kw0) (kw1 := kw1) (v10 := v10) (v40 := v40) (F := F)
          htail htail_pts htail_val hpos hlen_le hcap_lt hptr
      clear hC
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      suffices h_at_2a4 : ∀ s_2a4 : State,
          s_2a4.pc = (blkPl_80).base + 676#64 →
          s_2a4.status = .Running →
          s_2a4.sp = s.sp →
          s_2a4.spAligned = true →
          s_2a4.readReg64 .x19 = s.readReg64 .x19 →
          s_2a4.readReg64 .x21 = BitVec.ofNat 64 gk.vec.bytes.length →
          s_2a4.readReg64 .x23 = s.readReg64 .x23 →
          s_2a4.readReg64 .x24 = s.readReg64 .x24 →
          s_2a4.readReg64 .x25 = x.src →
          s_2a4.readReg64 .x26 = s.readReg64 .x26 →
          s_2a4.readReg64 .x27 = s.readReg64 .x27 →
          s_2a4.readReg64 .x28 = s.readReg64 .x28 →
          s_2a4.readReg64 .x29 = s.readReg64 .x29 →
          s_2a4.trace = s0.trace →
          s_2a4.calleeSavedVRegs = s.calleeSavedVRegs →
          SepWPpLsCl lsmpl (lsProg_80 H) ret s_2a4
            (A.pool ∗
              ((x.src + 0x128#64) ↦₆₄ gk.vec.cap) ∗
              ((x.src + 0x130#64) ↦₆₄ gk.vec.ptr) ∗
              ((x.src + 0x138#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length) ∗
              (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
              A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
              memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length)
                (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
              ((x.src + 0x140#64) ↦₃₂ kw0) ∗
              ((x.src + 0x144#64) ↦₃₂ kw1) ∗
              ((s_2a4.sp + 0x10#64) ↦₆₄ v10) ∗
              ((s_2a4.sp + 0x28#64) ↦₃₂ kw0) ∗
              ((s_2a4.sp + 0x40#64) ↦₆₄ v40) ∗
              stackAt s_2a4.sp Stage1X.extHookStack ∗ F)
            Q (scPanicPostX A x R s0) by
        clear hsub
        rcases hpc with hpc | hpc
        · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 676#64)
          wp_steps
          refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
          exact h_at_2a4 _ (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X)
        · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 676#64)
          wp_steps
          refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
          exact h_at_2a4 _ (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
            (by sc_close3X) (by sc_close3X) (by sc_close3X)
      intro s_2a4 hpc2a4 hrun2a4 hsp2a4 hspA2a4 hx19_2a4 hx21_2a4 hx23_2a4 hx24_2a4 hx25_2a4 hx26_2a4 hx27_2a4 hx28_2a4 hx29_2a4 htr2a4 hvregs2a4
      refine hsub s_2a4 hpc2a4 hrun2a4 hspA2a4 hx21_2a4 hx25_2a4 htr2a4
        fun s1 kybCap' kybPtr' v28' hpc1 hrun1 hsp1 hspA1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 => ?_
      clear hsub
      rw [hsp2a4]
      exact hnext s1 kybCap' kybPtr' v28'
        hpc1 hrun1 (hsp1.trans hsp2a4) hspA1
        (hx19_1.trans hx19_2a4) (hx23_1.trans hx23_2a4) (hx24_1.trans hx24_2a4) hx25_1
        (hx26_1.trans hx26_2a4) (hx27_1.trans hx27_2a4) (hx28_1.trans hx28_2a4)
        (hx29_1.trans hx29_2a4) htr1 (hvregs1.trans hvregs2a4)

/-! ## Field 8: `alice_base_key` (`+608 ∨ +884 ∨ +720 → +912 / +780`) -/

theorem sc_aliceBaseKey_2e4_pos_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v30 : BitVec 64} {F : SepProp}
    (halice : 0 < x.G.alice.bytes.length)
    (hlen_le : x.G.alice.bytes.length ≤ x.G.alice.cap.toNat)
    (hcap_lt : x.G.alice.cap.toNat < 2 ^ 63)
    (hptr : x.G.alice.ptr ≠ 0)
    (hpc : s.pc = (blkPl_80).base + 740#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.G.alice.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (blkPl_80).base + 780#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = alice'.cap → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → s1.calleeSavedVRegs = s.calleeSavedVRegs →
      alice'.bytes = x.G.alice.bytes → alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗ vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          ((s.sp + 0x30#64) ↦₆₄ alice'.ptr) ∗ stackAt s.sp Stage1X.extHookStack ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗ ((x.src + 0x60#64) ↦₆₄ x.G.alice.cap) ∗
        ((x.src + 0x68#64) ↦₆₄ x.G.alice.ptr) ∗
        ((x.src + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length) ∗
        (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗ A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
        memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
          (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗ stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  intro hcl
  have hshim := sc_shim_placed_ok_at_x hC
  have halloc := sc_alloc_placed_ok_at_x hC
  have hmemcpy := sc_memcpy_placed_ok_at_x hC
  have h68 : x.src + 0x60#64 + 8#64 = x.src + 0x68#64 := by bv_arith
  have h70 : x.src + 0x60#64 + 16#64 = x.src + 0x70#64 := by bv_arith
  have halice_lt : x.G.alice.bytes.length < 2 ^ 63 := by omega
  have halice_le63 : x.G.alice.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have halice_le64 : x.G.alice.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk x.G.alice.bytes.length 1 := ⟨halice, hpow2, halice_le63⟩
  have htoNat : (BitVec.ofNat 64 x.G.alice.bytes.length).toNat = x.G.alice.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 744#64)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_shim
  have hshim_state := shim_placed_ok_at_stateX hshim hcl_shim
  apply sepWPp_of_sepWP_lscl_sc hcl_shim (mid := (blkPl_80).base + 748#64)
  wp_steps
  wp_call hshim_state ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_alloc
  have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
  apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := (blkPl_80).base + 760#64)
  wp_steps
  wp_call halloc_state (x.G.alice.bytes.length, 1)
  clear halloc halloc_state
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 1140#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_panic
    refine sc_panic_0x474_placed_x hC x s0 _ _ R ?_ ?_ ?_ hcl_panic
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · change sf_1.trace = s0.trace ++ [allocFailedEvent]
      rw [htrace_alloc_oom, hpost, htr]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod, htrace_alloc_ok⟩ => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 776#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_memcpy
    have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_memcpy
    apply sepWPp_of_sepWP_lscl_sc hcl_memcpy (mid := (blkPl_80).base + 780#64)
    wp_steps
    wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.ptr, x.G.alice.bytes)
    clear hmemcpy hmemcpy_state
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_post_memcpy
    have hsp_eq : sf.sp = s.sp := by sc_close3X
    have hsf1_sp : sf_1.sp = s.sp := by sc_close3X
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨BitVec.ofNat 64 x.G.alice.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.bytes⟩
        (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X) rfl rfl hcl_post_memcpy)
    rw [vecGhostAt_eq_of_pos A x.G.alice (x.src + 0x60#64) halice, h68, h70,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.alice.bytes halice halice_lt hoom64]
    have h_pure_emp :
        (⌜x.G.alice.bytes.length ≤ x.G.alice.cap.toNat ∧
            x.G.alice.cap.toNat < 2 ^ 63 ∧ x.G.alice.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [h_pure_emp]
    simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Field 8 (`+608 ∨ +884 ∨ +720 → +912 / +780`) on `lsProg_80 H`. -/
theorem sc_aliceBaseKey_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v30 : BitVec 64} {v3c w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 608#64 ∨
           s.pc = (blkPl_80).base + 884#64 ∨
           s.pc = (blkPl_80).base + 720#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (if x.G.alice.bytes = [] then
                 (blkPl_80).base + 912#64
               else
                 (blkPl_80).base + 780#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x20).truncate 32 = w288 →
      s1.readReg64 .x21 = alice'.cap →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → s1.calleeSavedVRegs = s.calleeSavedVRegs →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗ vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
          ((s.sp + 0x30#64) ↦₆₄ alice'.ptr) ∗ ((s.sp + 0x3c#64) ↦₃₂ w28c) ∗
          stackAt s.sp Stage1X.extHookStack ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗ vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
        ((x.src + 0x150#64) ↦₃₂ w288) ∗ ((x.src + 0x154#64) ↦₃₂ w28c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗ ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  have h68 : x.src + 0x60#64 + 8#64 = x.src + 0x68#64 := by bv_arith
  have h70 : x.src + 0x60#64 + 16#64 = x.src + 0x70#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.alice.bytes with halice | halice
  · clear hC
    simp only [halice, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_nil A x.G.alice (x.src + 0x60#64) halice, h68, h70]
    simp only [sepConj_assoc]
    refine sepWPpLsCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have h_pure_emp :
        (⌜x.G.alice.cap.toNat < 2 ^ 63 ∧ x.G.alice.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    rcases hpc with hpc | hpc | hpc
    · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 912#64)
      wp_steps
      refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (x.src + 0x60#64) halice, h68, h70,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 912#64)
      wp_steps
      refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (x.src + 0x60#64) halice, h68, h70,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 912#64)
      wp_steps
      refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (x.src + 0x60#64) halice, h68, h70,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  · have halice_ne_nil : x.G.alice.bytes ≠ [] := List.ne_nil_of_length_pos halice
    simp only [halice_ne_nil, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_pos A x.G.alice (x.src + 0x60#64) halice, h68, h70]
    simp only [sepConj_assoc]
    refine sepWPpLsCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have halice_ne : BitVec.ofNat 64 x.G.alice.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos halice (by omega)
    have halice_beq : (BitVec.ofNat 64 x.G.alice.bytes.length == 0#64) = false :=
      beq_ofNat_zero_eq_false halice (by omega)
    have hsub : ∀ (s_2e4 : State) (F' : SepProp), _ := fun s_2e4 F' =>
      sc_aliceBaseKey_2e4_pos_placed_x hC (x := x) (R := R) (s0 := s0) (s := s_2e4)
        (ret := ret) (Q := Q) (v30 := v30) (F := F')
        halice hlen_le hcap_lt hptr
    clear hC
    suffices h_at_2e4 : ∀ s_2e4 : State,
        s_2e4.pc = (blkPl_80).base + 740#64 →
        s_2e4.status = .Running →
        s_2e4.sp = s.sp →
        s_2e4.spAligned = true →
        s_2e4.readReg64 .x19 = s.readReg64 .x19 →
        (s_2e4.readReg64 .x20).truncate 32 = w288 →
        s_2e4.readReg64 .x21 = BitVec.ofNat 64 x.G.alice.bytes.length →
        s_2e4.readReg64 .x23 = s.readReg64 .x23 →
        s_2e4.readReg64 .x24 = s.readReg64 .x24 →
        s_2e4.readReg64 .x25 = x.src →
        s_2e4.readReg64 .x26 = s.readReg64 .x26 →
        s_2e4.readReg64 .x27 = s.readReg64 .x27 →
        s_2e4.readReg64 .x28 = s.readReg64 .x28 →
        s_2e4.readReg64 .x29 = s.readReg64 .x29 →
        s_2e4.trace = s0.trace →
        s_2e4.calleeSavedVRegs = s.calleeSavedVRegs →
        SepWPpLsCl lsmpl (lsProg_80 H) ret s_2e4
          (A.pool ∗
            ((x.src + 0x60#64) ↦₆₄ x.G.alice.cap) ∗
            ((x.src + 0x68#64) ↦₆₄ x.G.alice.ptr) ∗
            ((x.src + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length) ∗
            (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
            A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
            memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
              (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
            ((x.src + 0x150#64) ↦₃₂ w288) ∗
            ((x.src + 0x154#64) ↦₃₂ w28c) ∗
            ((s_2e4.sp + 0x30#64) ↦₆₄ v30) ∗
            ((s_2e4.sp + 0x3c#64) ↦₃₂ w28c) ∗
            stackAt s_2e4.sp Stage1X.extHookStack ∗ F)
          Q (scPanicPostX A x R s0) by
      clear hsub
      rcases hpc with hpc | hpc | hpc
      · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 740#64)
        wp_steps
        refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
        exact h_at_2e4 _ (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
      · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 740#64)
        wp_steps
        refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
        exact h_at_2e4 _ (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
      · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 740#64)
        wp_steps
        refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
        exact h_at_2e4 _ (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
    intro s_2e4 hpc2e4 hrun2e4 hsp2e4 hspA2e4 hx19_2e4 hx20_2e4 hx21_2e4 hx23_2e4 hx24_2e4 hx25_2e4 hx26_2e4 hx27_2e4 hx28_2e4 hx29_2e4 htr2e4 hvregs2e4
    refine SepWPpLsCl.weaken_pre
      (P' := A.pool ∗
              ((x.src + 0x60#64) ↦₆₄ x.G.alice.cap) ∗
              ((x.src + 0x68#64) ↦₆₄ x.G.alice.ptr) ∗
              ((x.src + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length) ∗
              (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
              A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
              memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
                (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
              ((s_2e4.sp + 0x30#64) ↦₆₄ v30) ∗
              stackAt s_2e4.sp Stage1X.extHookStack ∗
              (((x.src + 0x150#64) ↦₃₂ w288) ∗
                ((x.src + 0x154#64) ↦₃₂ w28c) ∗
                ((s_2e4.sp + 0x3c#64) ↦₃₂ w28c) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine hsub s_2e4 _ hpc2e4 hrun2e4 hspA2e4 hx21_2e4 hx25_2e4 htr2e4
      fun s1 alice' hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx21_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 hbytes' hcap' => ?_
    clear hsub
    rw [hsp2e4]
    refine SepWPpLsCl.weaken_pre ?_
      (hnext s1 alice' hpc1 hrun1 (hsp1.trans hsp2e4) hspA1
        (hx19_1.trans hx19_2e4) (by rw [hx20_1]; exact hx20_2e4) hx21_1
        (hx23_1.trans hx23_2e4) (hx24_1.trans hx24_2e4) hx25_1
        (hx26_1.trans hx26_2e4) (hx27_1.trans hx27_2e4) (hx28_1.trans hx28_2e4)
        (hx29_1.trans hx29_2e4) htr1 (hvregs1.trans hvregs2e4) hbytes' hcap')
    exact Entails.of_eq (by ac_rfl)

/-! ## Field 9: `pq_ratchet_state` (`+912 / +780 → +924`) -/

theorem sc_pqRatchet_314_pos_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v0c : BitVec 32} {F : SepProp}
    (hpq : 0 < x.s.state.pqRatchetState.length)
    (hlen_le : x.s.state.pqRatchetState.length ≤ x.G.pq.cap.toNat)
    (hcap_lt : x.G.pq.cap.toNat < 2 ^ 63)
    (hptr : x.G.pq.ptr ≠ 0)
    (hpc : s.pc = (blkPl_80).base + 788#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.s.state.pqRatchetState.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64) (v0c' : BitVec 32),
      s1.pc = (blkPl_80).base + 924#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x20).truncate 32 = (s.readReg64 .x20).truncate 32 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqCap' →
      (s1.readReg64 .x23).truncate 32 = (s.readReg64 .x23).truncate 32 →
      (s1.readReg64 .x24).truncate 32 = (s.readReg64 .x24).truncate 32 →
      s1.readReg64 .x25 = pqPtr' →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → s1.calleeSavedVRegs = s.calleeSavedVRegs →
      pqCap' = BitVec.ofNat 64 x.s.state.pqRatchetState.length →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗ vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState ∗
          ((s.sp + 0x0c#64) ↦₃₂ v0c') ∗ stackAt s.sp Stage1X.extHookStack ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗ ((x.src + 0x78#64) ↦₆₄ x.G.pq.cap) ∗
        ((x.src + 0x80#64) ↦₆₄ x.G.pq.ptr) ∗
        ((x.src + 0x88#64) ↦₆₄ BitVec.ofNat 64 x.s.state.pqRatchetState.length) ∗
        (x.G.pq.ptr ↦ₛ x.s.state.pqRatchetState) ∗
        A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
        memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.s.state.pqRatchetState.length)
          (x.G.pq.cap.toNat - x.s.state.pqRatchetState.length) ∗
        ((s.sp + 0x0c#64) ↦₃₂ v0c) ∗ stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  intro hcl
  have hshim := sc_shim_placed_ok_at_x hC
  have halloc := sc_alloc_placed_ok_at_x hC
  have hmemcpy := sc_memcpy_placed_ok_at_x hC
  have h80 : x.src + 0x78#64 + 8#64 = x.src + 0x80#64 := by bv_arith
  have h88 : x.src + 0x78#64 + 16#64 = x.src + 0x88#64 := by bv_arith
  have hpq_lt : x.s.state.pqRatchetState.length < 2 ^ 63 := by omega
  have hpq_le63 : x.s.state.pqRatchetState.length + 1 ≤ 2 ^ 63 := by omega
  have hpq_le64 : x.s.state.pqRatchetState.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk x.s.state.pqRatchetState.length 1 := ⟨hpq, hpow2, hpq_le63⟩
  have htoNat : (BitVec.ofNat 64 x.s.state.pqRatchetState.length).toNat = x.s.state.pqRatchetState.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 812#64)
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_shim
  have hshim_state := shim_placed_ok_at_stateX hshim hcl_shim
  apply sepWPp_of_sepWP_lscl_sc hcl_shim (mid := (blkPl_80).base + 816#64)
  wp_steps
  wp_call hshim_state ()
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_alloc
  have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
  apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := (blkPl_80).base + 828#64)
  wp_steps
  wp_call halloc_state (x.s.state.pqRatchetState.length, 1)
  clear halloc halloc_state
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hcl_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace_alloc_oom => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 1188#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_panic
    refine sc_panic_0x4a4_placed_x hC x s0 _ _ R ?_ ?_ ?_ hcl_panic
    · simp only [wp_norm]
    · simp only [wp_norm]; assumption
    · change sf_1.trace = s0.trace ++ [allocFailedEvent]
      rw [htrace_alloc_oom, hpost, htr]
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod, htrace_alloc_ok⟩ => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 844#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_memcpy
    have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_memcpy
    apply sepWPp_of_sepWP_lscl_sc hcl_memcpy (mid := (blkPl_80).base + 848#64)
    wp_steps
    wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), x.G.pq.ptr, x.s.state.pqRatchetState)
    clear hmemcpy hmemcpy_state
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_post_memcpy
    apply sepWPp_of_sepWP_lscl_sc hcl_post_memcpy (mid := (blkPl_80).base + 924#64)
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl_end
    have hsp_eq : sf.sp = s.sp := by sc_close3X
    have hsf1_sp : sf_1.sp = s.sp := by sc_close3X
    refine SepWPp.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 x.s.state.pqRatchetState.length) (sf_1.readReg64 (Reg.gpr 0#5))
        ((s.readReg64 .x20).truncate 32)
        (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X)
        (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) rfl hcl_end)
    rw [vecU8At_eq_of_pos A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState hpq,
        h80, h88,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.s.state.pqRatchetState hpq hpq_lt hoom64]
    have h_pure_emp :
        (⌜x.s.state.pqRatchetState.length ≤ x.G.pq.cap.toNat ∧
            x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [h_pure_emp]
    dsimp only [Reg.x20]
    simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

/-- Field 9 (`+912 / +780 → +924`) on `lsProg_80 H`. -/
theorem sc_pqRatchet_placed_x [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v0c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.G.alice.bytes = [] then
                     (blkPl_80).base + 912#64
                   else
                     (blkPl_80).base + 780#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64) (v0c' : BitVec 32),
      s1.pc = (blkPl_80).base + 924#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x20).truncate 32 = (s.readReg64 .x20).truncate 32 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = pqCap' →
      (s1.readReg64 .x23).truncate 32 = (s.readReg64 .x23).truncate 32 →
      (s1.readReg64 .x24).truncate 32 = (s.readReg64 .x24).truncate 32 →
      s1.readReg64 .x25 = pqPtr' →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → s1.calleeSavedVRegs = s.calleeSavedVRegs →
      pqCap' = BitVec.ofNat 64 x.s.state.pqRatchetState.length →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗ vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.s.state.pqRatchetState ∗
          ((s.sp + 0x0c#64) ↦₃₂ v0c') ∗ stackAt s.sp Stage1X.extHookStack ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗ vecU8At A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState ∗
        ((s.sp + 0x0c#64) ↦₃₂ v0c) ∗ stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  have h80 : x.src + 0x78#64 + 8#64 = x.src + 0x80#64 := by bv_arith
  have h88 : x.src + 0x78#64 + 16#64 = x.src + 0x88#64 := by bv_arith
  have hpcs : s.pc = (blkPl_80).base + 912#64 ∨
              s.pc = (blkPl_80).base + 780#64 := by
    by_cases h : x.G.alice.bytes = [] <;> simp only [h, ↓reduceIte] at hpc <;> [exact Or.inl hpc; exact Or.inr hpc]
  clear hpc
  rcases eq_nil_or_length_pos x.s.state.pqRatchetState with hpq | hpq
  · clear hC
    rw [hpq, vecU8At_eq_of_nil A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr, h80, h88]
    simp only [sepConj_assoc]
    refine sepWPpLsCl_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have h_pure_emp :
        (⌜x.G.pq.cap.toNat < 2 ^ 63 ∧ x.G.pq.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
    rcases hpcs with hpc | hpc
    · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 924#64)
      wp_steps
      refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ 0#64 1#64 v0c (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by simp [hpq]))
      rw [hpq, vecU8At_eq_of_nil A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr, h80, h88,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 924#64)
      wp_steps
      refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ 0#64 1#64 v0c (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by simp [hpq]))
      rw [hpq, vecU8At_eq_of_nil A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr, h80, h88,
          vecU8Buf_nil_eq A, h_pure_emp]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  · rw [vecU8At_eq_of_pos A (x.src + 0x78#64) x.G.pq.cap x.G.pq.ptr x.s.state.pqRatchetState hpq,
        h80, h88]
    simp only [sepConj_assoc]
    refine sepWPpLsCl_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hpq_ne : BitVec.ofNat 64 x.s.state.pqRatchetState.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hpq (by omega)
    have hpq_beq : (BitVec.ofNat 64 x.s.state.pqRatchetState.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hpq (by omega)
    have hsub : ∀ (s_314 : State), _ := fun s_314 =>
      sc_pqRatchet_314_pos_placed_x hC (x := x) (R := R) (s0 := s0) (s := s_314)
        (ret := ret) (Q := Q) (v0c := v0c) (F := F)
        hpq hlen_le hcap_lt hptr
    clear hC
    suffices h_at_314 : ∀ s_314 : State,
        s_314.pc = (blkPl_80).base + 788#64 →
        s_314.status = .Running →
        s_314.sp = s.sp →
        s_314.spAligned = true →
        s_314.readReg64 .x19 = s.readReg64 .x19 →
        (s_314.readReg64 .x20).truncate 32 = (s.readReg64 .x20).truncate 32 →
        s_314.readReg64 .x21 = s.readReg64 .x21 →
        s_314.readReg64 .x22 = BitVec.ofNat 64 x.s.state.pqRatchetState.length →
        (s_314.readReg64 .x23).truncate 32 = (s.readReg64 .x23).truncate 32 →
        (s_314.readReg64 .x24).truncate 32 = (s.readReg64 .x24).truncate 32 →
        s_314.readReg64 .x25 = x.src →
        s_314.readReg64 .x26 = s.readReg64 .x26 →
        s_314.readReg64 .x27 = s.readReg64 .x27 →
        s_314.readReg64 .x28 = s.readReg64 .x28 →
        s_314.readReg64 .x29 = s.readReg64 .x29 →
        s_314.trace = s0.trace →
        s_314.calleeSavedVRegs = s.calleeSavedVRegs →
        SepWPpLsCl lsmpl (lsProg_80 H) ret s_314
          (A.pool ∗
            ((x.src + 0x78#64) ↦₆₄ x.G.pq.cap) ∗
            ((x.src + 0x80#64) ↦₆₄ x.G.pq.ptr) ∗
            ((x.src + 0x88#64) ↦₆₄ BitVec.ofNat 64 x.s.state.pqRatchetState.length) ∗
            (x.G.pq.ptr ↦ₛ x.s.state.pqRatchetState) ∗
            A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
            memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.s.state.pqRatchetState.length)
              (x.G.pq.cap.toNat - x.s.state.pqRatchetState.length) ∗
            ((s_314.sp + 0x0c#64) ↦₃₂ v0c) ∗
            stackAt s_314.sp Stage1X.extHookStack ∗ F)
          Q (scPanicPostX A x R s0) by
      clear hsub
      rcases hpcs with hpc | hpc
      · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 788#64)
        wp_steps
        refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
        exact h_at_314 _ (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
      · apply SepWPpLsCl.of_sepWP (mid := (blkPl_80).base + 788#64)
        wp_steps
        refine SepWP.done (by sc_close3X) (by sc_close3X) ?_
        exact h_at_314 _ (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
          (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X) (by sc_close3X)
    intro s_314 hpc314 hrun314 hsp314 hspA314 hx19_314 hx20_314 hx21_314 hx22_314 hx23_314 hx24_314 hx25_314 hx26_314 hx27_314 hx28_314 hx29_314 htr314 hvregs314
    refine hsub s_314 hpc314 hrun314 hspA314 hx22_314 hx25_314 htr314
      fun s1 pqCap' pqPtr' v0c' hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 hcap' => ?_
    clear hsub
    rw [hsp314]
    exact hnext s1 pqCap' pqPtr' v0c' hpc1 hrun1 (hsp1.trans hsp314) hspA1
      (hx19_1.trans hx19_314) (hx20_1.trans hx20_314) (hx21_1.trans hx21_314) hx22_1
      (hx23_1.trans hx23_314) (hx24_1.trans hx24_314) hx25_1
      (hx26_1.trans hx26_314) (hx27_1.trans hx27_314) (hx28_1.trans hx28_314)
      (hx29_1.trans hx29_314) htr1 (hvregs1.trans hvregs314) hcap'

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionCloneAux
