/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.BaseX
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.SessionClone.ChainCloneBaseX
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.ChainCloneEpilogue
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.PrologueFields1To4
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.Common
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable `SessionStructure::clone`: Prologue and Fields 1–4 (Block `80`)

Verifies the prologue (`+0 → +32`) and cloning of `local_identity_public`,
`remote_identity_public`, `root_key`, and `sender_chain` (`+32 → +572 / +336`) in Block `80` under
`[LibsignalPlacement]`.
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
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
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
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite isCalleeSavedVReg
  updateCalleeSavedVRegs
  Arm64.State.calleeSavedVRegs_writeReg64_gpr
  Arm64.State.calleeSavedVRegs_writeReg32_gpr
  Arm64.State.calleeSavedVRegs_setPC
  Arm64.State.calleeSavedVRegs_setPState

section Placed

theorem sepWPpLsCl_pure_2nd_pf {pl : Obj.MultiPlacement} {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P Q_post : SepProp} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpLsCl pl prog ret s (P ∗ Q_post) Q Qp) :
    SepWPpLsCl pl prog ret s (P ∗ ⌜φ⌝ ∗ Q_post) Q Qp :=
  fun hcl => sepWPp_pure_2nd fun hφ => h hφ hcl

/-- Prologue (`+0 → +32`) on `lsProg_80 H`. -/
theorem sc_prologue_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {x : SessionCloneGhost} {R : SepProp} {s0 : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {rv : ScSavedVals} {F : SepProp}
    (hpc : s0.pc = (blkPl_80).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_80).base + 32#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0x1d0#64 →
      s1.spAligned = true →
      s1.readReg64 .x0 = x.dst →
      s1.readReg64 .x1 = x.src →
      s1.readReg64 .x29 = s1.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (scSavedRegsAt (s0.sp - 0x1d0#64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s0
      (scSavedRegsAt (s0.sp - 0x1d0#64)
        rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25 rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗ F)
      Q (scPanicPostX A x R s0) :=
  fun hcl => sc_prologue_placed (A := A) hpc hrun hsp hcl hx0 hx1
    fun s1 hpc1 hrun1 hsp1 hspA1 hcl1 hx0_1 hx1_1 hx29_1 htr1 hv1 =>
      hnext s1 hpc1 hrun1 hsp1 hspA1 hx0_1 hx1_1 hx29_1 htr1 hv1 hcl1

/-- Clone `local_identity_public` (`+32 → +208 / +100`) on `lsProg_80 H`. -/
theorem sc_localIk_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 32#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (blkPl_80).base + 208#64
        else (blkPl_80).base + 100#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = x.dst →
      s1.readReg64 .x21 = localIk'.cap →
      s1.readReg64 .x22 = x.s.state.sessionVersion.setWidth 64 →
      s1.readReg64 .x23 = localIk'.ptr →
      s1.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          stackAt s.sp Stage1X.extHookStack ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
        ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  intro hcl
  rcases eq_nil_or_length_pos x.G.localIk.bytes with hloc | hloc
  · rw [Record.SegCloneSteps.vecGhostAt_eq_of_nil A x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have hpc_rem :
        (if ¬(BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then (blkPl_80).base + 100#64 else (blkPl_80).base + 208#64) =
        (if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
        have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
          Record.SegCloneSteps.beq_ofNat_zero_eq_false hrem (by omega)
        simp [hne, hbeq]
    apply sepWPp_of_sepWP_lscl_sc hcl
      (mid := if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64)
    wp_steps
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl1
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close) (by sc_close) rfl hsp
        rfl rfl rfl rfl rfl rfl rfl htr (by sc_close) hloc.symm (by simp [hloc]) hcl1)
    rw [Record.SegCloneSteps.vecGhostAt_eq_of_nil A x.G.localIk x.src hloc, Record.SegCloneSteps.vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · rw [Record.SegCloneSteps.vecGhostAt_eq_of_pos A x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := sc_shim_placed_ok_at_x hC
    have halloc := sc_alloc_placed_ok_at_x hC
    have hmemcpy := sc_memcpy_placed_ok_at_x hC
    have hloc_lt : x.G.localIk.bytes.length < 2 ^ 63 := by omega
    have hloc_le63 : x.G.localIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hloc_le64 : x.G.localIk.bytes.length ≤ 2 ^ 64 := by omega
    have hloc_ne : BitVec.ofNat 64 x.G.localIk.bytes.length ≠ 0#64 :=
      Record.SegCloneSteps.ofNat_ne_zero_of_pos hloc (by omega)
    have hloc_beq : (BitVec.ofNat 64 x.G.localIk.bytes.length == 0#64) = false :=
      Record.SegCloneSteps.beq_ofNat_zero_eq_false hloc (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.localIk.bytes.length 1 := ⟨hloc, hpow2, hloc_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hshim_state := shim_placed_ok_at_stateX hshim hcl
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 60#64)
    wp_steps
    wp_call hshim_state ()
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl_alloc
    have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
    apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := (blkPl_80).base + 72#64)
    wp_steps
    wp_call halloc_state (x.G.localIk.bytes.length, 1)
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl_post_alloc
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 1140#64)
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      intro hcl_p
      exact sc_panic_0x474_placed_x hC x s0 _ _ R (by sc_close) (by sc_close) (by sc_close) hcl_p
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hmod, htrace⟩ => ?_
      have hpc_rem :
          (if (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) =
          (if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) := by
        rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
        · simp [hrem]
        · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
          have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
            Record.SegCloneSteps.beq_ofNat_zero_eq_false hrem (by omega)
          simp [hne, hbeq]
      have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_post_alloc
      apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc
        (mid := if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64)
      wp_steps
      wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.ptr, x.G.localIk.bytes)
      clear hmemcpy hmemcpy_state
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      intro hcl_done
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.localIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.bytes⟩
          (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) rfl rfl hcl_done)
      rw [Record.SegCloneSteps.vecGhostAt_eq_of_pos A x.G.localIk x.src hloc,
          Record.SegCloneSteps.vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.localIk.bytes hloc hloc_lt hoom64]
      have hsp_eq : sf_1.sp = s.sp := by sc_close
      simp only [sepConj_assoc, hsp_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

/-- Clone `remote_identity_public` (`+208 / +100 → +152`) on `lsProg_80 H`. -/
theorem sc_remoteIk_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v88 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (blkPl_80).base + 208#64
      else (blkPl_80).base + 100#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (blkPl_80).base + 152#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = remoteIk'.cap →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = remoteIk'.ptr →
      s1.readReg64 .x27 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x88#64) ↦₆₄ s.readReg64 .x21) ∗
          stackAt s.sp Stage1X.extHookStack ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
        ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  intro hcl
  have h20 : x.src + 0x18#64 + 8#64 = x.src + 0x20#64 := by bv_arith
  have h28 : x.src + 0x18#64 + 16#64 = x.src + 0x28#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
  · simp only [hrem, ↓reduceIte] at hpc
    rw [hrem] at hx24
    rw [Record.SegCloneSteps.vecGhostAt_eq_of_nil A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 152#64)
    wp_steps
    refine SepWP.done rfl (by sc_close) ?_
    intro hcl1
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ rfl (by sc_close) rfl hsp
        rfl rfl rfl rfl hx24 hx25 rfl rfl rfl htr (by sc_close)
        hrem.symm (by simp [hrem]) hcl1)
    rw [Record.SegCloneSteps.vecGhostAt_eq_of_nil A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
        Record.SegCloneSteps.vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp, Reg.x21]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · have hrem_ne_nil : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
    simp only [hrem_ne_nil, ↓reduceIte] at hpc
    rw [Record.SegCloneSteps.vecGhostAt_eq_of_pos A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := sc_shim_placed_ok_at_x hC
    have halloc := sc_alloc_placed_ok_at_x hC
    have hmemcpy := sc_memcpy_placed_ok_at_x hC
    have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
    have hrem_le63 : x.G.remoteIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hrem_le64 : x.G.remoteIk.bytes.length ≤ 2 ^ 64 := by omega
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.remoteIk.bytes.length 1 := ⟨hrem, hpow2, hrem_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.remoteIk.bytes.length).toNat = x.G.remoteIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hshim_state := shim_placed_ok_at_stateX hshim hcl
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 108#64)
    wp_steps
    wp_call hshim_state ()
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl_alloc
    have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
    apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := (blkPl_80).base + 120#64)
    wp_steps
    wp_call halloc_state (x.G.remoteIk.bytes.length, 1)
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl_post_alloc
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine SepWPp.pure_elim fun htrace => ?_
      apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 1152#64)
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      intro hcl_p
      exact sc_panic_0x480_placed_x hC x s0 _ _ R (by sc_close) (by sc_close) (by sc_close) hcl_p
    · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hmod, htrace⟩ => ?_
      have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_post_alloc
      apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 152#64)
      wp_steps
      wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.ptr, x.G.remoteIk.bytes)
      clear hmemcpy hmemcpy_state
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      intro hcl_done
      have h21_eq : sf.readReg64 (Reg.gpr 21#5) = s.readReg64 .x21 := by sc_close
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.remoteIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.bytes⟩
          (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) rfl rfl hcl_done)
      rw [Record.SegCloneSteps.vecGhostAt_eq_of_pos A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
          Record.SegCloneSteps.vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.remoteIk.bytes hrem hrem_lt hoom64]
      have hsp_eq : sf_1.sp = s.sp := by sc_close
      simp only [sepConj_assoc, hsp_eq, h21_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

/-- Clone `root_key` (`+152 → +232`, 32 bytes) on `lsProg_80 H`. -/
theorem sc_rootKey_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v58 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 152#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src) (hx27 : s.readReg64 .x27 = 32#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (blkPl_80).base + 232#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗
          vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp Stage1X.extHookStack ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗
        vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        stackAt s.sp Stage1X.extHookStack ∗ F)
      Q (scPanicPostX A x R s0) := by
  intro hcl
  have hshim := sc_shim_placed_ok_at_x hC
  have halloc := sc_alloc_placed_ok_at_x hC
  have hmemcpy := sc_memcpy_placed_ok_at_x hC
  have h38 : x.src + 0x30#64 + 8#64 = x.src + 0x38#64 := by bv_arith
  have h40 : x.src + 0x30#64 + 16#64 = x.src + 0x40#64 := by bv_arith
  have hroot_len : (keyToBytes32 x.s.state.rootKey).length = 32 := by simp [keyToBytes32]
  have hroot_pos : 0 < (keyToBytes32 x.s.state.rootKey).length := by omega
  have hroot_lt : (keyToBytes32 x.s.state.rootKey).length < 2 ^ 63 := by omega
  have hroot_le64 : (keyToBytes32 x.s.state.rootKey).length ≤ 2 ^ 64 := by omega
  rw [Record.SegCloneSteps.vecU8At_eq_of_pos A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
      h38, h40]
  simp only [sepConj_assoc]
  refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have h32_pos : 0 < 32 := by decide
  have h32_le63 : 32 + 1 ≤ 2 ^ 63 := by decide
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨h32_pos, hpow2, h32_le63⟩
  have hshim_state := shim_placed_ok_at_stateX hshim hcl
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 160#64)
  wp_steps
  wp_call hshim_state ()
  refine SepWP.done (by sc_close) (by sc_close) ?_
  intro hcl_alloc
  have halloc_state := alloc_placed_ok_at_stateX halloc hcl_alloc
  apply sepWPp_of_sepWP_lscl_sc hcl_alloc (mid := (blkPl_80).base + 172#64)
  wp_steps
  wp_call halloc_state (32, 1)
  refine SepWP.done (by sc_close) (by sc_close) ?_
  intro hcl_post_alloc
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := (blkPl_80).base + 1164#64)
    wp_steps
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl_p
    exact sc_panic_0x48c_placed_x hC x s0 _ _ R (by sc_close) (by sc_close) (by sc_close) hcl_p
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hmod, htrace⟩ => ?_
    have hmem32 :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey).length := by
      rw [hroot_len]
    rw [hmem32]
    apply sepWPp_of_sepWP_lscl_sc hcl_post_alloc (mid := lsρ CryptoVerification.lsMemcpySym)
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hcl_call
    have hmemcpy_state := memcpy_placed_ok_at_stateX hmemcpy hcl_call
    apply sepWPp_of_sepWP_lscl_sc hcl_call (mid := (blkPl_80).base + 232#64)
    wp_call hmemcpy_state (sf_1.readReg64 (Reg.gpr 0#5), x.G.root.ptr, keyToBytes32 x.s.state.rootKey)
    clear hmemcpy hmemcpy_state
    wp_steps
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl_done
    refine SepWPp.weaken_pre ?_
      (hnext _ (sf_1.readReg64 (Reg.gpr 0#5))
        (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) hcl_done)
    have hbuf32 :
        vecU8Buf A 32#64 (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey) =
          A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗
            (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ keyToBytes32 x.s.state.rootKey) := by
      have h := Record.SegCloneSteps.vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey)
        hroot_pos hroot_lt hoom64
      rwa [hroot_len] at h
    rw [Record.SegCloneSteps.vecU8At_eq_of_pos A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
        h38, h40, hbuf32]
    have hsp1_eq : sf_1.sp = s.sp := by sc_close
    have hsp_eq : sf.sp = s.sp := by sc_close
    simp only [sepConj_assoc, hsp1_eq, hsp_eq]
    exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

/-- Clone `sender_chain` (`+232 → +572 / +336`) on `lsProg_80 H`. -/
theorem sc_senderChain_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hscc : SenderChainCloneLocal1PlacedOkX A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {localIk' remoteIk' : VecGhost}
    {v48 v60 v68 v70 v78 : BitVec 64} {v54 v84 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 232#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = x.s.state.sessionVersion.setWidth 64)
    (hx23 : s.readReg64 .x23 = localIk'.ptr)
    (hx24 : s.readReg64 .x24 = remoteIk'.cap)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx26 : s.readReg64 .x26 = remoteIk'.ptr)
    (hx27 : s.readReg64 .x27 = 32#64)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.s.state.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.s.state.receiverChains = []
        then (blkPl_80).base + 572#64
        else (blkPl_80).base + 336#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      OptSenderChainInline sender' x.s.state.senderChain (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      encSenderFieldMem sender' x.s.state.senderChain = encSenderFieldMem x.G.sender x.s.state.senderChain →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗
          optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
          optSenderChainHeap A sender' x.s.state.senderChain ∗
          chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          ((s.sp + 0x48#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
          ((s.sp + 0x60#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
          ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
          stackAt s.sp chainCloneStackX ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗
        optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
        chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x84#64) ↦₃₂ v84) ∗
        ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
        ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        stackAt s.sp chainCloneStackX ∗ F)
      Q (scPanicPostX A x R s0) := by
  have hcall := sc_chainClone_placed_ok_at_x (senderChainCloneSpecX A) hscc
  have hw22 : (s.readReg64 (Reg.gpr 22#5)).truncate 32 = x.s.state.sessionVersion := by
    change (s.readReg64 .x22).truncate 32 = x.s.state.sessionVersion
    rw [hx22]; exact segClone_setWidth_64_truncate_32 _
  cases hscG : x.G.sender with
  | none =>
    cases hscM : x.s.state.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      have hnone_cmn : noneCap + 1#64 = 0#64 := by decide
      clear hcall
      have hpc_rc :
          (if ¬(BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = true then (blkPl_80).base + 336#64 else (blkPl_80).base + 572#64) =
          (if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64) := by
        rcases eq_nil_or_length_pos x.s.state.receiverChains with hrc | hrc
        · simp [hrc]
        · have hne : x.s.state.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
          have hbeq : (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = false :=
            Record.SegCloneSteps.beq_ofNat_zero_eq_false hrc (by omega)
          simp [hne, hbeq]
      apply SepWPpLsCl.of_sepWP
        (mid := if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64)
      wp_steps
      refine SepWP.done (by sc_close) hrun ?_
      have hinl : OptSenderChainInline none x.s.state.senderChain
          (bytes104OfW6Q noneCap bq0 bq1 bq2 bq3 bq4 bq5) := by
        rw [hscM]
        exact OptSenderChainInline.none_of_chunks96 bq0 bq1 bq2 bq3 bq4 bq5
      have henc : encSenderFieldMem none x.s.state.senderChain =
          encSenderFieldMem x.G.sender x.s.state.senderChain := by
        rw [hscG]
      refine SepWPpLsCl.weaken_pre ?_
        (hnext _ none noneCap bq0 bq1 bq2 bq3 bq4 bq5
          (by sc_close) hrun rfl hsp rfl (by sc_close) hx25 rfl hx29 htr (by sc_close) hinl henc)
      rw [hscG, hscM]
      dsimp only [optSenderChainAt, optSenderChainHeap]
      simp only [emp_sepConj, sepConj_emp, hx23, hx24, hx26, hx27, hw22]
      exact Entails.of_eq (by ac_rfl)
    | some sc =>
      dsimp only [optSenderChainAt]
      intro _
      exact sepWPp_pure_2nd fun h => False.elim h
  | some sg =>
    cases hscM : x.s.state.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      intro _
      exact sepWPp_pure_2nd fun h => False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_cap A (x.src + 0x90#64) sg sc]
      simp only [sepConj_assoc]
      refine sepWPpLsCl_pure_2nd_pf fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcap_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcap_beq : (sg.srk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      apply SepWPpLsCl.of_sepWP (mid := (blkPl_82).base)
      wp_steps
      refine SepWP.done rfl hrun ?_
      refine SepWPpLsCl.weaken_pre
        (P' := (memRegion (s.sp + 0xf8#64) 104 ∗
            optSenderChainAt A (x.src + 0x90#64) (some sg) (some sc) ∗
            A.pool ∗ stackAt s.sp chainCloneStackX) ∗
          (chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            ((s.sp + 0x48#64) ↦₆₄ v48) ∗
            ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((s.sp + 0x60#64) ↦₆₄ v60) ∗
            ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
            ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
            ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
            ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗ F))
        ?_ ?_
      · rw [optSenderChainAt_some_eq_cap A (x.src + 0x90#64) sg sc]
        simp only [sepConj_assoc, hx23, hx24, hx26, hw22]
        rw [show (memRegion (s.sp + 0xf8#64) 104 ∗
            ⌜sg.srk.bytes.length ≤ sg.srk.cap.toNat ∧ sg.srk.cap.toNat < 2 ^ 63 ∧ sg.srk.ptr ≠ 0⌝ ∗
            ((x.src + 0x90#64) ↦₆₄ sg.srk.cap) ∗
            optSenderChainSomeRest A (x.src + 0x90#64) sg sc ∗
            A.pool ∗ stackAt s.sp chainCloneStackX ∗
            chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            ((s.sp + 0x48#64) ↦₆₄ v48) ∗
            ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((s.sp + 0x60#64) ↦₆₄ v60) ∗
            ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
            ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
            ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
            ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗ F) =
          (A.pool ∗
            ⌜sg.srk.bytes.length ≤ sg.srk.cap.toNat ∧ sg.srk.cap.toNat < 2 ^ 63 ∧ sg.srk.ptr ≠ 0⌝ ∗
            ((x.src + 0x90#64) ↦₆₄ sg.srk.cap) ∗
            optSenderChainSomeRest A (x.src + 0x90#64) sg sc ∗
            chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s.sp + 0xf8#64) 104 ∗
            ((s.sp + 0x48#64) ↦₆₄ v48) ∗
            ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
            ((s.sp + 0x60#64) ↦₆₄ v60) ∗
            ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
            ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
            ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
            ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            stackAt s.sp chainCloneStackX ∗ F) by ac_rfl]
        exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)
      · refine SepWPpLsCl.call_frame_withLsCodeLoaded (spec := senderChainCloneSpecX A)
          (x := ⟨s.sp + 0xf8#64, x.src + 0x90#64, sg, sc⟩)
          hcall rfl hrun hsp
          rfl (hspec := rfl) ⟨by sc_close, by sc_close⟩ rfl
          (fun _ _ _ _ h => allowPanic_not_exited h)
          (fun sf _ hm => sc_onPanic_of_callee_panic_x htr hm)
          fun sf hpcf_raw hrunf hspf hcsm => ?_
        have hpcf : sf.pc = (blkPl_80).base + 280#64 := by rw [hpcf_raw]; sc_close
        clear hpcf_raw hcall
        obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩ := hcsm
        dsimp only [senderChainCloneSpecX]
        simp only [sepConj_assoc]
        refine SepWPpLsCl.pure_elim fun htr_sf => ?_
        rw [sepExists_sepConj_left]
        refine SepWPpLsCl.exists_elim fun g' => ?_
        simp only [sepConj_assoc]
        refine SepWPpLsCl.pure_elim fun ⟨hsrk', hpriv'⟩ => ?_
        have hsf_sp : sf.sp = s.sp := hspf
        have hsf19 : sf.readReg64 (Reg.gpr 19#5) = s.readReg64 .x19 := hcs19
        have hsf21 : sf.readReg64 (Reg.gpr 21#5) = sf.sp + 0xf8#64 := by
          rw [hcs21, hsf_sp]; sc_close
        have hsf25 : sf.readReg64 (Reg.gpr 25#5) = x.src := hcs25.trans hx25
        have hsf27 : sf.readReg64 (Reg.gpr 27#5) = 32#64 := hcs27.trans hx27
        have hsf29 : sf.readReg64 Reg.fp = sf.sp + 0x170#64 := by
          rw [hcs29, hsf_sp]; exact hx29
        have hsf29' : sf.readReg64 (Reg.gpr 29#5) = sf.sp + 0x170#64 := hsf29
        have hsf_tr : sf.trace = s0.trace := htr_sf.trans htr
        have hsf_vregs : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
          rw [hcsv]; exact hvregs
        have hsf_spA : sf.spAligned = true := by
          unfold State.spAligned at hsp ⊢; rw [hsf_sp]; exact hsp
        clear hspf hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 hcsv htr_sf
        refine SepWPpLsCl.weaken_pre
          (sepConj_mono_left (optSenderChainAt_entails_chunks104W6Q A (s.sp + 0xf8#64) (some g') (some sc))) ?_
        simp only [sepExists_sepConj_left]
        refine SepWPpLsCl.exists_elim fun scCap' =>
          SepWPpLsCl.exists_elim fun sq0 => SepWPpLsCl.exists_elim fun sq1 =>
          SepWPpLsCl.exists_elim fun sq2 => SepWPpLsCl.exists_elim fun sq3 =>
          SepWPpLsCl.exists_elim fun sq4 => SepWPpLsCl.exists_elim fun sq5 => ?_
        simp only [sepConj_assoc]
        refine SepWPpLsCl.pure_elim fun hsc_inl => ?_
        have hinl : OptSenderChainInline (some g') x.s.state.senderChain
            (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) := by
          rw [hscM]; exact hsc_inl
        have henc : encSenderFieldMem (some g') x.s.state.senderChain =
            encSenderFieldMem x.G.sender x.s.state.senderChain := by
          simp only [hscG, hscM, encSenderFieldMem, encChainMem, senderGhostAsChain, hsrk', hpriv']
        rw [chunks104W6QAt_sp_0xf8 s.sp scCap' sq0 sq1 sq2 sq3 sq4 sq5,
            chunks96_6QAt_sp_0x90 s.sp bq0 bq1 bq2 bq3 bq4 bq5]
        simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        have hpc_rc :
            (if (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = true then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64) =
            (if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64) := by
          rcases eq_nil_or_length_pos x.s.state.receiverChains with hrc | hrc
          · simp [hrc]
          · have hne : x.s.state.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
            have hne0 : BitVec.ofNat 64 x.s.state.receiverChains.length ≠ 0#64 :=
              ChainCloneLocal1.ofNat_ne_zero_of_pos hrc (by omega)
            have hbeq : (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = false :=
              beq_false_of_ne hne0
            simp [hne, hbeq]
        apply SepWPpLsCl.of_sepWP
          (mid := if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64)
        wp_steps
        refine SepWP.done (by sc_close) hrunf ?_
        refine SepWPpLsCl.weaken_pre ?_
          (hnext _ (some g') scCap' sq0 sq1 sq2 sq3 sq4 sq5
            (by sc_close) hrunf hsf_sp hsf_spA hsf19 (by sc_close) hsf25 rfl (by sc_close) hsf_tr (by sc_close) hinl henc)
        simp only [hscG, hscM, hsf21, hsf_sp, hsf27,
            ← chunks96_6QAt_sp_0x90 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
            pointsTo128_eq_pointsTo64, cat128_extractLsb, BitVec.add_assoc, BitVec.reduceAdd]
        have h104 : ∀ R_tail : SepProp,
            ((s.sp + 0xf8#64) ↦₆₄ scCap') ∗
              ((s.sp + 256#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 264#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
              ((s.sp + 272#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 280#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
              ((s.sp + 288#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 296#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
              ((s.sp + 304#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 312#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
              ((s.sp + 320#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 328#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
              ((s.sp + 336#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 344#64) ↦₆₄ sq5.extractLsb' 64 64) ∗
              R_tail ⊢
            memRegion (s.sp + 0xf8#64) 104 ∗ R_tail := by
          intro R_tail
          have h104_eq := congrArg (· ∗ R_tail) (chunks104W6QAt_sp_0xf8 s.sp scCap' sq0 sq1 sq2 sq3 sq4 sq5)
          simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h104_eq
          rw [← h104_eq]
          exact sepConj_mono_left (chunks104W6QAt_entails_memRegion _ _ _ _ _ _ _ _)
        refine Entails.trans (h104 _) ?_
        exact Entails.of_eq (by
          simp only [chunks96_6QAt_sp_0x90, pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd]
          ac_rfl)

private theorem stackAt_chainClone_eq_alloc_x_c7_placed (sp : BitVec 64) :
    stackAt sp chainCloneStackX =
      memRegion (sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗
        stackAt sp Stage1X.extHookStack := by
  have h := stackAt_split_bottom sp Stage1X.extHookStack 208 (by decide)
  rwa [show Stage1X.extHookStack + 208 = chainCloneStackX by decide] at h

/-- Combined fields 1–4 (`+32 → +572 / +336`) on `lsProg_80 H`. -/
theorem sc_fields_1_to_4_placed_x [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hC : SerContractsXPlaced A H)
    (hscc : SenderChainCloneLocal1PlacedOkX A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v48 v58 v60 v68 v70 v78 v88 : BitVec 64} {v54 v84 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 32#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.s.state.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.s.state.receiverChains = []
        then (blkPl_80).base + 572#64
        else (blkPl_80).base + 336#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = x.dst →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      OptSenderChainInline sender' x.s.state.senderChain
        (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      encSenderFieldMem sender' x.s.state.senderChain = encSenderFieldMem x.G.sender x.s.state.senderChain →
      SepWPpLsCl lsmpl (lsProg_80 H) ret s1
        (A.pool ∗
          vecGhostAt A x.G.localIk x.src ∗
          vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          optSenderChainHeap A sender' x.s.state.senderChain ∗
          chunks96_6QAt (s.sp + 0x90#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          ((s.sp + 0x48#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.s.state.previousCounter) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗
          ((s.sp + 0x60#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x70#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x84#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((s.sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
          ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
          stackAt s.sp chainCloneStackX ∗ F)
        Q (scPanicPostX A x R s0)) :
    SepWPpLsCl lsmpl (lsProg_80 H) ret s
      (A.pool ∗
        vecGhostAt A x.G.localIk x.src ∗
        vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
        vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
        chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x84#64) ↦₃₂ v84) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
        stackAt s.sp chainCloneStackX ∗ F)
      Q (scPanicPostX A x R s0) := by
  rw [sc_vecGhostAt_0x18_eq A x.G.remoteIk x.src,
      vecU8Buf_pure_extract A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes,
      sc_vecU8At_0x30_root_eq A x.src x.G.root.cap x.G.root.ptr x.s.state.rootKey,
      stackAt_chainClone_eq_alloc_x_c7_placed s.sp]
  refine SepWPpLsCl.weaken_pre
    (P' := ⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧
              x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ ∗
            A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
            ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            stackAt s.sp Stage1X.extHookStack ∗
            (((x.src + 0x18#64) ↦₆₄ x.G.remoteIk.cap) ∗
              ((x.src + 0x20#64) ↦₆₄ x.G.remoteIk.ptr) ∗
              vecU8Buf A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes ∗
              ((x.src + 0x30#64) ↦₆₄ x.G.root.cap) ∗
              ((x.src + 0x38#64) ↦₆₄ x.G.root.ptr) ∗
              ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
              vecU8Buf A x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (s.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s.sp + 0xf8#64) 104 ∗
              ((s.sp + 0x48#64) ↦₆₄ v48) ∗ ((s.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s.sp + 0x58#64) ↦₆₄ v58) ∗ ((s.sp + 0x60#64) ↦₆₄ v60) ∗
              ((s.sp + 0x68#64) ↦₆₄ v68) ∗ ((s.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s.sp + 0x78#64) ↦₆₄ v78) ∗ ((s.sp + 0x84#64) ↦₃₂ v84) ∗
              ((s.sp + 0x88#64) ↦₆₄ v88) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPpLsCl.pure_elim fun ⟨hlen_rem, hcap_rem, _⟩ => ?_
  have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
  refine sc_localIk_placed_x hC hpc hrun hsp hx0 hx1 htr hvregs hrem_lt
    fun s1 localIk' hpc1 hrun1 hsp1 hspA1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 htr1 hvregs1 hloc_b hloc_c => ?_
  rw [← hsp1]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
            ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
            ((s1.sp + 0x88#64) ↦₆₄ v88) ∗
            stackAt s1.sp Stage1X.extHookStack ∗
            (vecGhostAt A x.G.localIk x.src ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x30#64) ↦₆₄ x.G.root.cap) ∗
              ((x.src + 0x38#64) ↦₆₄ x.G.root.ptr) ∗
              vecU8Buf A x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (s1.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s1.sp + 0xf8#64) 104 ∗
              ((s1.sp + 0x48#64) ↦₆₄ v48) ∗ ((s1.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s1.sp + 0x58#64) ↦₆₄ v58) ∗ ((s1.sp + 0x60#64) ↦₆₄ v60) ∗
              ((s1.sp + 0x68#64) ↦₆₄ v68) ∗ ((s1.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s1.sp + 0x78#64) ↦₆₄ v78) ∗ ((s1.sp + 0x84#64) ↦₃₂ v84) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ F))
    (by rw [sc_vecGhostAt_0x18_eq A x.G.remoteIk x.src]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_remoteIk_placed_x hC hpc1 hrun1 hspA1 hx24_1 hx25_1 htr1 hvregs1
    fun s2 remoteIk' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 hrem_b hrem_c => ?_
  rw [← hsp2, hx21_1]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool ∗
            vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            ((s2.sp + 0x58#64) ↦₆₄ v58) ∗
            stackAt s2.sp Stage1X.extHookStack ∗
            (vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
              chunks96_6QAt (s2.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s2.sp + 0xf8#64) 104 ∗
              ((s2.sp + 0x48#64) ↦₆₄ v48) ∗ ((s2.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s2.sp + 0x60#64) ↦₆₄ v60) ∗ ((s2.sp + 0x68#64) ↦₆₄ v68) ∗
              ((s2.sp + 0x70#64) ↦₆₄ v70) ∗ ((s2.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s2.sp + 0x84#64) ↦₃₂ v84) ∗ ((s2.sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
              ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStackX) 208 ∗ F))
    (by rw [sc_vecU8At_0x30_root_eq A x.src x.G.root.cap x.G.root.ptr x.s.state.rootKey]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_rootKey_placed_x hC hpc2 hrun2 hspA2 hx25_2 hx27_2 htr2 hvregs2
    fun s3 rootPtr' hpc3 hrun3 hsp3 hspA3 hx19_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 htr3 hvregs3 => ?_
  rw [← hsp3]
  refine SepWPpLsCl.weaken_pre
    (P' := A.pool ∗
            optSenderChainAt A (x.src + 0x90#64) x.G.sender x.s.state.senderChain ∗
            chunks96_6QAt (s3.sp + 0x90#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s3.sp + 0xf8#64) 104 ∗
            ((s3.sp + 0x48#64) ↦₆₄ v48) ∗ ((s3.sp + 0x54#64) ↦₃₂ v54) ∗
            ((s3.sp + 0x60#64) ↦₆₄ v60) ∗ ((s3.sp + 0x68#64) ↦₆₄ v68) ∗
            ((s3.sp + 0x70#64) ↦₆₄ v70) ∗ ((s3.sp + 0x78#64) ↦₆₄ v78) ∗
            ((s3.sp + 0x84#64) ↦₃₂ v84) ∗
            ((x.src + 0x58#64) ↦₆₄ BitVec.ofNat 64 x.s.state.receiverChains.length) ∗
            ((x.src + 0x14c#64) ↦₃₂ x.s.state.previousCounter) ∗
            stackAt s3.sp chainCloneStackX ∗
            (vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              ((s3.sp + 0x58#64) ↦₆₄ rootPtr') ∗
              ((s3.sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗ F))
    (by rw [stackAt_chainClone_eq_alloc_x_c7_placed s3.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  have hx19_3' : s3.readReg64 .x19 = x.dst := by rw [hx19_3, hx19_2, hx19_1]
  have hx22_3' : s3.readReg64 .x22 = x.s.state.sessionVersion.setWidth 64 := by rw [hx22_3, hx22_2, hx22_1]
  have hx23_3' : s3.readReg64 .x23 = localIk'.ptr := by rw [hx23_3, hx23_2, hx23_1]
  have hx24_3' : s3.readReg64 .x24 = remoteIk'.cap := by rw [hx24_3, hx24_2]
  have hx26_3' : s3.readReg64 .x26 = remoteIk'.ptr := by rw [hx26_3, hx26_2]
  have hx29_3' : s3.readReg64 .x29 = s3.sp + 0x170#64 := by rw [hx29_3, hx29_2, hx29_1, hx29, hsp3, hsp2, hsp1]
  refine sc_senderChain_placed_x hscc hpc3 hrun3 hspA3 hx22_3' hx23_3' hx24_3' hx25_3 hx26_3' hx27_3 hx29_3' htr3 hvregs3 hrc_lt
    fun s4 sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 hpc4 hrun4 hsp4 hspA4 hx19_4 hx21_4 hx25_4 hx26_4 hx29_4 htr4 hvregs4 hinl henc => ?_
  have hsp_eq : s3.sp = s.sp := by rw [hsp3, hsp2, hsp1]
  rw [hsp_eq] at hx21_4 hx29_4 ⊢
  refine SepWPpLsCl.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s4 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc4 hrun4 (by rw [hsp4, hsp_eq]) hspA4
      (by rw [hx19_4, hx19_3']) hx21_4 hx25_4 hx26_4 hx29_4
      htr4 hvregs4 hloc_b hloc_c hrem_b hrem_c hinl henc)

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionCloneAux
