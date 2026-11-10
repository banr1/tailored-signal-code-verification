/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::clone` (`0x240f0`): prologue, identity keys, `root_key`, and `sender_chain`
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization.SessionCloneAux

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1
  (ChainCloneLocal1Ok ChainCloneLocal1Ok_trap SenderChainCloneLocal1Ok SenderChainCloneLocal1Ok_trap)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[arm64_norm, wp_norm]
theorem fp_add_neg_112 (sp : BitVec 64) :
    (sp + 0x170#64) + bv% (2 ^ 64 - 112) = sp + 0x100#64 := by bv_omega

/-- Clears continuation hypotheses and simplifies step side conditions. -/
macro "sc_close" : tactic =>
  `(tactic| (
    try clear hnext
    try clear hshim
    try clear halloc
    try clear hmemcpy
    try clear hcall
    try clear hpanic
    first
    | rfl
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, Reg.fp, Reg.lr] at *
       try simp (config := { decide := true }) only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        updateCalleeSavedVRegs]
       simp (config := { decide := true }) only [*, reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        updateCalleeSavedVRegs,
        State.setPC, State.setPState, bv_sub_add_lit,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_add, List.length_cons]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, Reg.fp, Reg.lr] at *
       try simp only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        updateCalleeSavedVRegs]
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32, bv_sub_add_lit,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        updateCalleeSavedVRegs]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30, Reg.fp, Reg.lr] at *
       subst_vars
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32, bv_sub_add_lit,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        updateCalleeSavedVRegs]
       done)))

theorem sc_vecGhostAt_0x18_eq (A : RustAlloc) (g : VecGhost) (src : BitVec 64) :
    vecGhostAt A g (src + 0x18#64) =
      ((src + 0x18#64) ↦₆₄ g.cap) ∗ ((src + 0x20#64) ↦₆₄ g.ptr) ∗
      ((src + 0x28#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      vecU8Buf A g.cap g.ptr g.bytes := by
  unfold vecGhostAt
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  have h1 : src + 0x18#64 + 8#64 = src + 0x20#64 := by bv_arith
  have h2 : src + 0x18#64 + 16#64 = src + 0x28#64 := by bv_arith
  rw [h1, h2]
  ac_rfl

theorem sc_vecU8At_0x30_root_eq (A : RustAlloc) (src cap ptr : BitVec 64) (rk : RootKey) :
    vecU8At A (src + 0x30#64) cap ptr (keyToBytes32 rk) =
      ((src + 0x30#64) ↦₆₄ cap) ∗ ((src + 0x38#64) ↦₆₄ ptr) ∗
      ((src + 0x40#64) ↦₆₄ 32#64) ∗
      vecU8Buf A cap ptr (keyToBytes32 rk) := by
  rw [vecU8At_eq_header_sep_buf]
  unfold vecHeader
  have h1 : src + 0x30#64 + 8#64 = src + 0x38#64 := by bv_arith
  have h2 : src + 0x30#64 + 16#64 = src + 0x40#64 := by bv_arith
  have h3 : BitVec.ofNat 64 (keyToBytes32 rk).length = 32#64 := by simp [keyToBytes32]
  rw [h1, h2, h3]
  ac_rfl

private theorem sc_prologue_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {rv : ScSavedVals} {F : SepProp}
    (hpc : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src)
    (hnext : ∀ s1 : State,
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x020#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0x1d0#64 →
      s1.spAligned = true →
      s1.readReg64 .x0 = x.dst →
      s1.readReg64 .x1 = x.src →
      s1.readReg64 .x29 = s1.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (scSavedRegsAt (s0.sp - 0x1d0#64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s0
      (scSavedRegsAt (s0.sp - 0x1d0#64)
        rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25 rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hsp_sub_align : ((s0.sp - 464#64) &&& 15#64 == 0#64) = true :=
    s0.spAligned_sub 464#64 hsp
  unfold scSavedRegsAt
  simp only [sepConj_assoc]
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x000 32
  have := libsignalSessionCode_fetch_fnAddr_entry (b := b)
    (H := Rust.withPanics ext)
    hfn (by decide) (ls_decode% sessionCloneBin (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (32))
  wp_steps
  refine SepWP.done (by sc_close) hrun ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by sc_close) hrun rfl (by sc_close) (by sc_close) (by sc_close) (by sc_close) rfl (by sc_close))
  unfold scSavedRegsAt
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
  exact Entails.of_eq (by ac_rfl)

theorem sc_prologue_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {rv : ScSavedVals} {F : SepProp}
    (hpc : s0.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src)
    (hnext : ∀ s1 : State,
      s1.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x020#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0x1d0#64 →
      s1.spAligned = true →
      s1.readReg64 .x0 = x.dst →
      s1.readReg64 .x1 = x.src →
      s1.readReg64 .x29 = s1.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (trTrapProgAt b C abs) ret s1
        (scSavedRegsAt (s0.sp - 0x1d0#64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s0
      (scSavedRegsAt (s0.sp - 0x1d0#64)
        rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25 rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_prologue_ext_trap hpc hrun hsp hx0 hx1 hnext

/-- Allocates the `0x1d0`-byte frame and saves `x19..x30` (`+0x000..+0x020`). -/
theorem sc_prologue {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {rv : ScSavedVals} {F : SepProp}
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src)
    (hnext : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x020#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0x1d0#64 →
      s1.spAligned = true →
      s1.readReg64 .x0 = x.dst →
      s1.readReg64 .x1 = x.src →
      s1.readReg64 .x29 = s1.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (scSavedRegsAt (s0.sp - 0x1d0#64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s0
      (scSavedRegsAt (s0.sp - 0x1d0#64)
        rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25 rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_prologue_ext_trap hpc hrun hsp hx0 hx1 hnext

private theorem sc_localIk_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hkit : ScExternKit_trap b A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x0d0#64
        else (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x064#64) →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
        ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  rcases eq_nil_or_length_pos x.G.localIk.bytes with hloc | hloc
  · clear hkit
    rw [vecGhostAt_eq_of_nil A x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    sessionClone_fetches b (Rust.withPanics ext) hfn 0x020 20
    sessionClone_fetches b (Rust.withPanics ext) hfn 0x0c4 12
    clear hfn
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    have hpc_rem :
        (if ¬(BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then entry + bv% (100) else entry + bv% (208)) =
        (if x.G.remoteIk.bytes = [] then entry + bv% (208) else entry + bv% (100)) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
        have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
          beq_ofNat_zero_eq_false hrem (by omega)
        simp [hne, hbeq]
    apply SepWPp.of_sepWP (mid := if x.G.remoteIk.bytes = [] then entry + bv% (208) else entry + bv% (100))
    wp_steps
    refine SepWP.done (by sc_close) hrun ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close) hrun rfl hsp
        rfl rfl rfl rfl rfl rfl rfl htr (by sc_close) hloc.symm (by simp [hloc]))
    rw [vecGhostAt_eq_of_nil A x.G.localIk x.src hloc, vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · rw [vecGhostAt_eq_of_pos A x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := hkit.shim
    have halloc := hkit.alloc
    have hmemcpy := hkit.memcpy
    have hpanic : ∀ (s_p : State) (P_p : SepProp),
        s_p.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x474#64 →
        s_p.status = .Running →
        s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s_p P_p Q (scPanicPost A x R s0) :=
      fun s_p P_p => sc_panic_0x474_ext_trap hkit.panic_err x s0 s_p P_p R
    clear hkit
    have hloc_lt : x.G.localIk.bytes.length < 2 ^ 63 := by omega
    have hloc_le63 : x.G.localIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hloc_le64 : x.G.localIk.bytes.length ≤ 2 ^ 64 := by omega
    have hloc_ne : BitVec.ofNat 64 x.G.localIk.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hloc (by omega)
    have hloc_beq : (BitVec.ofNat 64 x.G.localIk.bytes.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hloc (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.localIk.bytes.length 1 := ⟨hloc, hpow2, hloc_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    sessionClone_fetches b (Rust.withPanics ext) hfn 0x020 68
    clear hfn
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (72))
    wp_steps
    wp_call hshim ()
    clear hshim
    wp_steps
    wp_call halloc (x.G.localIk.bytes.length, 1)
    clear halloc
    refine SepWP.done (by sc_close) (by sc_close) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_3rd fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (1140))
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
    · clear hpanic
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      have hpc_rem :
          (if (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then entry + bv% (208) else entry + bv% (100)) =
          (if x.G.remoteIk.bytes = [] then entry + bv% (208) else entry + bv% (100)) := by
        rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
        · simp [hrem]
        · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
          have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem (by omega)
          simp [hne, hbeq]
      apply SepWPp.of_sepWP (mid := if x.G.remoteIk.bytes = [] then entry + bv% (208) else entry + bv% (100))
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.ptr, x.G.localIk.bytes)
      clear hmemcpy
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.localIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.bytes⟩
          (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) rfl rfl)
      rw [vecGhostAt_eq_of_pos A x.G.localIk x.src hloc,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.localIk.bytes hloc hloc_lt hoom64]
      have hsp_eq : sf.sp = s.sp := by sc_close
      simp only [sepConj_assoc, hsp_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

theorem sc_localIk_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x0d0#64
        else (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x064#64) →
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
      SepWPp (trTrapProgAt b C abs) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
        ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_localIk_ext_trap (scExternKit_trap hA) hpc hrun hsp hx0 hx1 htr hvregs hrem_lt hnext

theorem sc_localIk {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x0d0#64
        else (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x064#64) →
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
        ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_localIk_ext_trap (scExternKit_kit_trap hA) hpc hrun hsp hx0 hx1 htr hvregs hrem_lt hnext

private theorem sc_remoteIk_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hkit : ScExternKit_trap b A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v88 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x0d0#64
      else (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x064#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x098#64 →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x88#64) ↦₆₄ s.readReg64 .x21) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
        ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have h20 : x.src + 0x18#64 + 8#64 = x.src + 0x20#64 := by bv_arith
  have h28 : x.src + 0x18#64 + 16#64 = x.src + 0x28#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
  · clear hkit
    simp only [hrem, ↓reduceIte] at hpc
    rw [hrem] at hx24
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    sessionClone_fetches b (Rust.withPanics ext) hfn 0x0d0 16
    clear hfn
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (152))
    wp_steps
    refine SepWP.done rfl hrun ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ rfl hrun rfl hsp
        rfl rfl rfl rfl hx24 hx25 rfl rfl rfl htr (by sc_close)
        hrem.symm (by simp [hrem]))
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
        vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp, Reg.x21]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · have hrem_ne_nil : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
    simp only [hrem_ne_nil, ↓reduceIte] at hpc
    rw [vecGhostAt_eq_of_pos A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := hkit.shim
    have halloc := hkit.alloc
    have hmemcpy := hkit.memcpy
    have hpanic : ∀ (s_p : State) (P_p : SepProp),
        s_p.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x480#64 →
        s_p.status = .Running →
        s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s_p P_p Q (scPanicPost A x R s0) :=
      fun s_p P_p => sc_panic_0x480_ext_trap hkit.panic_err x s0 s_p P_p R
    clear hkit
    have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
    have hrem_le63 : x.G.remoteIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hrem_le64 : x.G.remoteIk.bytes.length ≤ 2 ^ 64 := by omega
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.remoteIk.bytes.length 1 := ⟨hrem, hpow2, hrem_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.remoteIk.bytes.length).toNat = x.G.remoteIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    sessionClone_fetches b (Rust.withPanics ext) hfn 0x064 52
    clear hfn
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (120))
    wp_steps
    wp_call hshim ()
    clear hshim
    wp_steps
    wp_call halloc (x.G.remoteIk.bytes.length, 1)
    clear halloc
    refine SepWP.done (by sc_close) (by sc_close) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_3rd fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (1152))
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
    · clear hpanic
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (152))
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.ptr, x.G.remoteIk.bytes)
      clear hmemcpy
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      have h21_eq : sf.readReg64 (Reg.gpr 21#5) = s.readReg64 .x21 := by sc_close
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.remoteIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.bytes⟩
          (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) rfl rfl)
      rw [vecGhostAt_eq_of_pos A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.remoteIk.bytes hrem hrem_lt hoom64]
      have hsp_eq : sf.sp = s.sp := by sc_close
      simp only [sepConj_assoc, hsp_eq, h21_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

theorem sc_remoteIk_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v88 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x0d0#64
      else (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x064#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x098#64 →
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
      SepWPp (trTrapProgAt b C abs) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x88#64) ↦₆₄ s.readReg64 .x21) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
        ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_remoteIk_ext_trap (scExternKit_trap hA) hpc hrun hsp hx24 hx25 htr hvregs hnext

theorem sc_remoteIk {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v88 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x0d0#64
      else (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x064#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x098#64 →
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x88#64) ↦₆₄ s.readReg64 .x21) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
        ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_remoteIk_ext_trap (scExternKit_kit_trap hA) hpc hrun hsp hx24 hx25 htr hvregs hnext

private theorem sc_rootKey_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hkit : ScExternKit_trap b A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v58 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x098#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src) (hx27 : s.readReg64 .x27 = 32#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x0e8#64 →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
          vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
        vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hshim := hkit.shim
  have halloc := hkit.alloc
  have hmemcpy := hkit.memcpy
  have hpanic : ∀ (s_p : State) (P_p : SepProp),
      s_p.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x48c#64 →
      s_p.status = .Running →
      s_p.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s_p P_p Q (scPanicPost A x R s0) :=
    fun s_p P_p => sc_panic_0x48c_ext_trap hkit.panic_err x s0 s_p P_p R
  clear hkit
  have h38 : x.src + 0x30#64 + 8#64 = x.src + 0x38#64 := by bv_arith
  have h40 : x.src + 0x30#64 + 16#64 = x.src + 0x40#64 := by bv_arith
  have hroot_len : (keyToBytes32 x.s.state.rootKey).length = 32 := by simp [keyToBytes32]
  have hroot_pos : 0 < (keyToBytes32 x.s.state.rootKey).length := by omega
  have hroot_lt : (keyToBytes32 x.s.state.rootKey).length < 2 ^ 63 := by omega
  have hroot_le64 : (keyToBytes32 x.s.state.rootKey).length ≤ 2 ^ 64 := by omega
  rw [vecU8At_eq_of_pos A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
      h38, h40]
  simp only [sepConj_assoc]
  refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have h32_pos : 0 < 32 := by decide
  have h32_le63 : 32 + 1 ≤ 2 ^ 63 := by decide
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨h32_pos, hpow2, h32_le63⟩
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x098 44
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (172))
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (32, 1)
  clear halloc
  refine SepWP.done (by sc_close) (by sc_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1164))
    wp_steps
    refine SepWP.done (by sc_close) (by sc_close) ?_
    exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    have hmem32 :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey).length := by
      rw [hroot_len]
    rw [hmem32]
    apply SepWPp.of_sepWP (mid := entry + bv% (232))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.root.ptr, keyToBytes32 x.s.state.rootKey)
    clear hmemcpy
    wp_steps
    refine SepWP.done (by sc_close) (by sc_close) ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ (sf_1.readReg64 (Reg.gpr 0#5))
        (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close))
    have hbuf32 :
        vecU8Buf A 32#64 (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey) =
          A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗
            (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ keyToBytes32 x.s.state.rootKey) := by
      have h := vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey)
        hroot_pos hroot_lt hoom64
      rwa [hroot_len] at h
    rw [vecU8At_eq_of_pos A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
        h38, h40, hbuf32]
    have hsp1_eq : sf_1.sp = s.sp := by sc_close
    have hsp_eq : sf.sp = s.sp := by sc_close
    simp only [sepConj_assoc, hsp1_eq, hsp_eq]
    exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

theorem sc_rootKey_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v58 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x098#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src) (hx27 : s.readReg64 .x27 = 32#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x0e8#64 →
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
      SepWPp (trTrapProgAt b C abs) ret s1
        (A.pool ∗
          vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
      (A.pool ∗
        vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_rootKey_ext_trap (scExternKit_trap hA) hpc hrun hsp hx25 hx27 htr hvregs hnext

theorem sc_rootKey {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v58 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x098#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src) (hx27 : s.readReg64 .x27 = 32#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x0e8#64 →
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (A.pool ∗
          vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (A.pool ∗
        vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_rootKey_ext_trap (scExternKit_kit_trap hA) hpc hrun hsp hx25 hx27 htr hvregs hnext

private theorem sc_senderChain_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName +
        bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" -
          ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (senderChainCloneSpec A))
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {localIk' remoteIk' : VecGhost}
    {v48 v60 v68 v70 v78 : BitVec 64} {v54 v84 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x0e8#64)
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
        then (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x23c#64
        else (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x150#64) →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
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
          stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
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
        stackAt s.sp chainCloneStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hw22 : (s.readReg64 (Reg.gpr 22#5)).truncate 32 = x.s.state.sessionVersion := by
    change (s.readReg64 .x22).truncate 32 = x.s.state.sessionVersion
    rw [hx22]; exact segClone_setWidth_64_truncate_32 _
  cases hscG : x.G.sender with
  | none =>
    cases hscM : x.s.state.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      have hnone_cmn : noneCap + 1#64 = 0#64 := by decide
      sessionClone_fetches b (Rust.withPanics ext) hfn 0x0e8 40
      sessionClone_fetches b (Rust.withPanics ext) hfn 0x22c 16
      clear hfn hcall
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      have hpc_rc :
          (if ¬(BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = true then entry + bv% (336) else entry + bv% (572)) =
          (if x.s.state.receiverChains = [] then entry + bv% (572) else entry + bv% (336)) := by
        rcases eq_nil_or_length_pos x.s.state.receiverChains with hrc | hrc
        · simp [hrc]
        · have hne : x.s.state.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
          have hbeq : (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrc (by omega)
          simp [hne, hbeq]
      apply SepWPp.of_sepWP (mid := if x.s.state.receiverChains = [] then entry + bv% (572) else entry + bv% (336))
      wp_steps
      refine SepWP.done (by sc_close) hrun ?_
      have hinl : OptSenderChainInline none x.s.state.senderChain
          (bytes104OfW6Q noneCap bq0 bq1 bq2 bq3 bq4 bq5) := by
        rw [hscM]
        exact OptSenderChainInline.none_of_chunks96 bq0 bq1 bq2 bq3 bq4 bq5
      have henc : encSenderFieldMem none x.s.state.senderChain =
          encSenderFieldMem x.G.sender x.s.state.senderChain := by
        rw [hscG]
      refine SepWPp.weaken_pre ?_
        (hnext _ none noneCap bq0 bq1 bq2 bq3 bq4 bq5
          (by sc_close) hrun rfl hsp rfl (by sc_close) hx25 rfl hx29 htr (by sc_close) hinl henc)
      rw [hscG, hscM]
      dsimp only [optSenderChainAt, optSenderChainHeap]
      simp only [emp_sepConj, sepConj_emp, hx23, hx24, hx26, hx27, hw22]
      exact Entails.of_eq (by ac_rfl)
    | some sc =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_2nd fun h => False.elim h
  | some sg =>
    cases hscM : x.s.state.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_2nd fun h => False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_cap A (x.src + 0x90#64) sg sc]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcap_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcap_beq : (sg.srk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      sessionClone_fetches b (Rust.withPanics ext) hfn 0x0e8 104
      clear hfn
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      wp_steps
      refine SepWP.done rfl hrun ?_
      refine SepWPp.weaken_pre
        (P' := (memRegion (s.sp + 0xf8#64) 104 ∗
            optSenderChainAt A (x.src + 0x90#64) (some sg) (some sc) ∗
            A.pool ∗ stackAt s.sp chainCloneStack) ∗
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
            A.pool ∗ stackAt s.sp chainCloneStack ∗
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
            stackAt s.sp chainCloneStack ∗ F) by ac_rfl]
        exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)
      · refine SepWPp.call_frame (x := ⟨s.sp + 0xf8#64, x.src + 0x90#64, sg, sc⟩)
          hcall rfl hrun hsp
          (ret_pc := entry + bv% (280)) rfl
          rfl ⟨by sc_close, by sc_close⟩ rfl
          (fun _ _ _ _ h => allowPanic_not_exited h)
          (fun sf _ hm => sc_onPanic_of_callee_panic htr hm)
          fun sf hpcf hrunf hspf hcsm => ?_
        clear hcall
        obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩ := hcsm
        dsimp only [senderChainCloneSpec]
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun htr_sf => ?_
        rw [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun g' => ?_
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hsrk', hpriv'⟩ => ?_
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
        refine SepWPp.weaken_pre
          (sepConj_mono_left (optSenderChainAt_entails_chunks104W6Q A (s.sp + 0xf8#64) (some g') (some sc))) ?_
        simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun scCap' =>
          SepWPp.exists_elim fun sq0 => SepWPp.exists_elim fun sq1 =>
          SepWPp.exists_elim fun sq2 => SepWPp.exists_elim fun sq3 =>
          SepWPp.exists_elim fun sq4 => SepWPp.exists_elim fun sq5 => ?_
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun hsc_inl => ?_
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
            (if (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = true then entry + bv% (572) else entry + bv% (336)) =
            (if x.s.state.receiverChains = [] then entry + bv% (572) else entry + bv% (336)) := by
          rcases eq_nil_or_length_pos x.s.state.receiverChains with hrc | hrc
          · simp [hrc]
          · have hne : x.s.state.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
            have hne0 : BitVec.ofNat 64 x.s.state.receiverChains.length ≠ 0#64 :=
              ofNat_ne_zero_of_pos hrc (by omega)
            have hbeq : (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = false :=
              beq_false_of_ne hne0
            simp [hne, hbeq]
        apply SepWPp.of_sepWP
          (mid := if x.s.state.receiverChains = [] then entry + bv% (572) else entry + bv% (336))
        wp_steps
        refine SepWP.done (by sc_close) hrunf ?_
        refine SepWPp.weaken_pre ?_
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

theorem sc_senderChain_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hscc : SenderChainCloneLocal1Ok_trap b C A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {localIk' remoteIk' : VecGhost}
    {v48 v60 v68 v70 v78 : BitVec 64} {v54 v84 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x0e8#64)
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
        then (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x23c#64
        else (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x150#64) →
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
      SepWPp (trTrapProgAt b C abs) ret s1
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
          stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
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
        stackAt s.sp chainCloneStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_senderChain_ext_trap (sc_senderChainClone_ok_at_trap hscc) hpc hrun hsp hx22 hx23 hx24 hx25 hx26 hx27 hx29 htr hvregs hrc_lt hnext

theorem sc_senderChain {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hscc : SenderChainCloneLocal1Ok b C A ctl abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {localIk' remoteIk' : VecGhost}
    {v48 v60 v68 v70 v78 : BitVec 64} {v54 v84 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x0e8#64)
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
        then (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x23c#64
        else (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x150#64) →
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
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
          stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
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
        stackAt s.sp chainCloneStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_senderChain_ext_trap (sc_senderChainClone_ok_at hscc) hpc hrun hsp hx22 hx23 hx24 hx25 hx26 hx27 hx29 htr hvregs hrc_lt hnext

private theorem sc_fields_1_to_4_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hkit : ScExternKit_trap b A ext)
    (hcall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName +
        bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" -
          ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (senderChainCloneSpec A))
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v48 v58 v60 v68 v70 v78 v88 : BitVec 64} {v54 v84 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.s.state.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.s.state.receiverChains = []
        then (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x23c#64
        else (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x150#64) →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
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
          stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
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
        stackAt s.sp chainCloneStack ∗ F)
      Q (scPanicPost A x R s0) := by
  rw [sc_vecGhostAt_0x18_eq A x.G.remoteIk x.src,
      vecU8Buf_pure_extract A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes,
      sc_vecU8At_0x30_root_eq A x.src x.G.root.cap x.G.root.ptr x.s.state.rootKey,
      stackAt_chainClone_eq_alloc s.sp]
  refine SepWPp.weaken_pre
    (P' := ⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧
              x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ ∗
            A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
            ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            stackAt s.sp allocHookStack ∗
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
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hlen_rem, hcap_rem, _⟩ => ?_
  have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
  refine sc_localIk_ext_trap hkit hpc hrun hsp hx0 hx1 htr hvregs hrem_lt
    fun s1 localIk' hpc1 hrun1 hsp1 hspA1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 htr1 hvregs1 hloc_b hloc_c => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
            ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
            ((s1.sp + 0x88#64) ↦₆₄ v88) ∗
            stackAt s1.sp allocHookStack ∗
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
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [sc_vecGhostAt_0x18_eq A x.G.remoteIk x.src]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_remoteIk_ext_trap hkit hpc1 hrun1 hspA1 hx24_1 hx25_1 htr1 hvregs1
    fun s2 remoteIk' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 hrem_b hrem_c => ?_
  rw [← hsp2, hx21_1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            ((s2.sp + 0x58#64) ↦₆₄ v58) ∗
            stackAt s2.sp allocHookStack ∗
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
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [sc_vecU8At_0x30_root_eq A x.src x.G.root.cap x.G.root.ptr x.s.state.rootKey]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_rootKey_ext_trap hkit hpc2 hrun2 hspA2 hx25_2 hx27_2 htr2 hvregs2
    fun s3 rootPtr' hpc3 hrun3 hsp3 hspA3 hx19_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 htr3 hvregs3 => ?_
  rw [← hsp3]
  refine SepWPp.weaken_pre
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
            stackAt s3.sp chainCloneStack ∗
            (vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              ((s3.sp + 0x58#64) ↦₆₄ rootPtr') ∗
              ((s3.sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗ F))
    (by rw [stackAt_chainClone_eq_alloc s3.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  have hx19_3' : s3.readReg64 .x19 = x.dst := by rw [hx19_3, hx19_2, hx19_1]
  have hx22_3' : s3.readReg64 .x22 = x.s.state.sessionVersion.setWidth 64 := by rw [hx22_3, hx22_2, hx22_1]
  have hx23_3' : s3.readReg64 .x23 = localIk'.ptr := by rw [hx23_3, hx23_2, hx23_1]
  have hx24_3' : s3.readReg64 .x24 = remoteIk'.cap := by rw [hx24_3, hx24_2]
  have hx26_3' : s3.readReg64 .x26 = remoteIk'.ptr := by rw [hx26_3, hx26_2]
  have hx29_3' : s3.readReg64 .x29 = s3.sp + 0x170#64 := by rw [hx29_3, hx29_2, hx29_1, hx29, hsp3, hsp2, hsp1]
  refine sc_senderChain_ext_trap hcall hpc3 hrun3 hspA3 hx22_3' hx23_3' hx24_3' hx25_3 hx26_3' hx27_3 hx29_3' htr3 hvregs3 hrc_lt
    fun s4 sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 hpc4 hrun4 hsp4 hspA4 hx19_4 hx21_4 hx25_4 hx26_4 hx29_4 htr4 hvregs4 hinl henc => ?_
  have hsp_eq : s3.sp = s.sp := by rw [hsp3, hsp2, hsp1]
  rw [hsp_eq] at hx21_4 hx29_4 ⊢
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s4 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc4 hrun4 (by rw [hsp4, hsp_eq]) hspA4
      (by rw [hx19_4, hx19_3']) hx21_4 hx25_4 hx26_4 hx29_4
      htr4 hvregs4 hloc_b hloc_c hrem_b hrem_c hinl henc)

theorem sc_fields_1_to_4_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (hscc : SenderChainCloneLocal1Ok_trap b C A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v48 v58 v60 v68 v70 v78 v88 : BitVec 64} {v54 v84 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.s.state.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.s.state.receiverChains = []
        then (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x23c#64
        else (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x150#64) →
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
      SepWPp (trTrapProgAt b C abs) ret s1
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
          stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
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
        stackAt s.sp chainCloneStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_fields_1_to_4_ext_trap (scExternKit_trap hA) (sc_senderChainClone_ok_at_trap hscc)
    hpc hrun hsp hx0 hx1 hx29 htr hvregs hrc_lt hnext

/-- Clones `local_identity_public`, `remote_identity_public`, `root_key`, and `sender_chain` (`+0x020..+0x23c/+0x150`). -/
theorem sc_fields_1_to_4 {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (hscc : SenderChainCloneLocal1Ok b C A ctl abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v48 v58 v60 v68 v70 v78 v88 : BitVec 64} {v54 v84 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.s.state.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.s.state.receiverChains = []
        then (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x23c#64
        else (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x150#64) →
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
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
          stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
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
        stackAt s.sp chainCloneStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_fields_1_to_4_ext_trap (scExternKit_kit_trap hA) (sc_senderChainClone_ok_at hscc)
    hpc hrun hsp hx0 hx1 hx29 htr hvregs hrc_lt hnext

/-! ## Relocatable `[LibsignalPlacement]` proofs (block `80`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (SenderChainCloneLocal1PlacedOk)

theorem sc_prologue_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {rv : ScSavedVals} {F : SepProp}
    (hpc : s0.pc = (blkPl_80).base)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src)
    (hnext : ∀ s1 : State,
      s1.pc = (blkPl_80).base + 0x020#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0x1d0#64 →
      s1.spAligned = true →
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.readReg64 .x0 = x.dst →
      s1.readReg64 .x1 = x.src →
      s1.readReg64 .x29 = s1.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (lsProg_80 H) ret s1
        (scSavedRegsAt (s0.sp - 0x1d0#64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s0
      (scSavedRegsAt (s0.sp - 0x1d0#64)
        rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25 rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗ F)
      Q (scPanicPost A x R s0) := by
  have hsp_sub_align : ((s0.sp - 464#64) &&& 15#64 == 0#64) = true :=
    s0.spAligned_sub 464#64 hsp
  unfold scSavedRegsAt
  simp only [sepConj_assoc]
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 32#64)
  wp_steps
  refine SepWP.done (by sc_close) hrun ?_
  intro hcl1
  refine SepWPp.weaken_pre ?_
    (hnext _ (by sc_close) hrun rfl (by sc_close) hcl1
      (by sc_close) (by sc_close) (by sc_close) rfl (by sc_close))
  unfold scSavedRegsAt
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
  exact Entails.of_eq (by ac_rfl)

theorem sc_localIk_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hkit : ScExternKit_placed A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (blkPl_80).base + 0x0d0#64
        else (blkPl_80).base + 0x064#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      LibsignalCodeLoaded lsmpl s1.mem →
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
      SepWPp (lsProg_80 H) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
        ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  rcases eq_nil_or_length_pos x.G.localIk.bytes with hloc | hloc
  · clear hkit
    rw [vecGhostAt_eq_of_nil A x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    have hpc_rem :
        (if ¬(BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then (blkPl_80).base + 100#64 else (blkPl_80).base + 208#64) =
        (if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
        have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
          beq_ofNat_zero_eq_false hrem (by omega)
        simp [hne, hbeq]
    apply sepWPp_of_sepWP_lscl_sc hcl
      (mid := if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64)
    wp_steps
    refine SepWP.done (by sc_close) hrun ?_
    intro hcl1
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close) hrun rfl hsp hcl1
        rfl rfl rfl rfl rfl rfl rfl htr (by sc_close) hloc.symm (by simp [hloc]))
    rw [vecGhostAt_eq_of_nil A x.G.localIk x.src hloc, vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · rw [vecGhostAt_eq_of_pos A x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := hkit.shim
    have halloc := hkit.alloc
    have hmemcpy := hkit.memcpy
    have hpanic : ∀ (s_p : State) (P_p : SepProp),
        s_p.pc = (blkPl_80).base + 0x474#64 →
        s_p.status = .Running →
        s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (lsProg_80 H) ret s_p P_p Q (scPanicPost A x R s0) :=
      fun s_p P_p => sc_panic_0x474_placed hkit.panic_err x s0 s_p P_p R
    clear hkit
    have hloc_lt : x.G.localIk.bytes.length < 2 ^ 63 := by omega
    have hloc_le63 : x.G.localIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hloc_le64 : x.G.localIk.bytes.length ≤ 2 ^ 64 := by omega
    have hloc_ne : BitVec.ofNat 64 x.G.localIk.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hloc (by omega)
    have hloc_beq : (BitVec.ofNat 64 x.G.localIk.bytes.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hloc (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.localIk.bytes.length 1 := ⟨hloc, hpow2, hloc_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 72#64)
    wp_steps
    wp_call hshim ()
    clear hshim
    wp_steps
    wp_call halloc (x.G.localIk.bytes.length, 1)
    clear halloc
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl1
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_3rd fun htrace => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_80).base + 1140#64)
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
    · clear hpanic
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      have hpc_rem :
          (if (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) =
          (if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64) := by
        rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
        · simp [hrem]
        · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
          have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem (by omega)
          simp [hne, hbeq]
      apply sepWPp_of_sepWP_lscl_sc hcl1
        (mid := if x.G.remoteIk.bytes = [] then (blkPl_80).base + 208#64 else (blkPl_80).base + 100#64)
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.ptr, x.G.localIk.bytes)
      clear hmemcpy
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      intro hcl2
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.localIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.bytes⟩
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) hcl2
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) rfl rfl)
      rw [vecGhostAt_eq_of_pos A x.G.localIk x.src hloc,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.localIk.bytes hloc hloc_lt hoom64]
      have hsp_eq : sf.sp = s.sp := by sc_close
      simp only [sepConj_assoc, hsp_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

theorem sc_remoteIk_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hkit : ScExternKit_placed A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v88 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (blkPl_80).base + 0x0d0#64
      else (blkPl_80).base + 0x064#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (blkPl_80).base + 0x098#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      LibsignalCodeLoaded lsmpl s1.mem →
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
      SepWPp (lsProg_80 H) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x88#64) ↦₆₄ s.readReg64 .x21) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
        ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have h20 : x.src + 0x18#64 + 8#64 = x.src + 0x20#64 := by bv_arith
  have h28 : x.src + 0x18#64 + 16#64 = x.src + 0x28#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
  · clear hkit
    simp only [hrem, ↓reduceIte] at hpc
    rw [hrem] at hx24
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 152#64)
    wp_steps
    refine SepWP.done rfl hrun ?_
    intro hcl1
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ rfl hrun rfl hsp hcl1
        rfl rfl rfl rfl hx24 hx25 rfl rfl rfl htr (by sc_close)
        hrem.symm (by simp [hrem]))
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
        vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp, Reg.x21]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · have hrem_ne_nil : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
    simp only [hrem_ne_nil, ↓reduceIte] at hpc
    rw [vecGhostAt_eq_of_pos A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := hkit.shim
    have halloc := hkit.alloc
    have hmemcpy := hkit.memcpy
    have hpanic : ∀ (s_p : State) (P_p : SepProp),
        s_p.pc = (blkPl_80).base + 0x480#64 →
        s_p.status = .Running →
        s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (lsProg_80 H) ret s_p P_p Q (scPanicPost A x R s0) :=
      fun s_p P_p => sc_panic_0x480_placed hkit.panic_err x s0 s_p P_p R
    clear hkit
    have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
    have hrem_le63 : x.G.remoteIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hrem_le64 : x.G.remoteIk.bytes.length ≤ 2 ^ 64 := by omega
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.remoteIk.bytes.length 1 := ⟨hrem, hpow2, hrem_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.remoteIk.bytes.length).toNat = x.G.remoteIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 120#64)
    wp_steps
    wp_call hshim ()
    clear hshim
    wp_steps
    wp_call halloc (x.G.remoteIk.bytes.length, 1)
    clear halloc
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl1
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_3rd fun htrace => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_80).base + 1152#64)
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
    · clear hpanic
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      apply sepWPp_of_sepWP_lscl_sc hcl1 (mid := (blkPl_80).base + 152#64)
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.ptr, x.G.remoteIk.bytes)
      clear hmemcpy
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      intro hcl2
      have h21_eq : sf.readReg64 (Reg.gpr 21#5) = s.readReg64 .x21 := by sc_close
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.remoteIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.bytes⟩
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) hcl2
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) rfl rfl)
      rw [vecGhostAt_eq_of_pos A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.remoteIk.bytes hrem hrem_lt hoom64]
      have hsp_eq : sf.sp = s.sp := by sc_close
      simp only [sepConj_assoc, hsp_eq, h21_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

theorem sc_rootKey_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hkit : ScExternKit_placed A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v58 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 0x098#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx25 : s.readReg64 .x25 = x.src) (hx27 : s.readReg64 .x27 = 32#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (blkPl_80).base + 0x0e8#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      LibsignalCodeLoaded lsmpl s1.mem →
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
      SepWPp (lsProg_80 H) ret s1
        (A.pool ∗
          vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
      (A.pool ∗
        vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hshim := hkit.shim
  have halloc := hkit.alloc
  have hmemcpy := hkit.memcpy
  have hpanic : ∀ (s_p : State) (P_p : SepProp),
      s_p.pc = (blkPl_80).base + 0x48c#64 →
      s_p.status = .Running →
      s_p.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (lsProg_80 H) ret s_p P_p Q (scPanicPost A x R s0) :=
    fun s_p P_p => sc_panic_0x48c_placed hkit.panic_err x s0 s_p P_p R
  clear hkit
  have h38 : x.src + 0x30#64 + 8#64 = x.src + 0x38#64 := by bv_arith
  have h40 : x.src + 0x30#64 + 16#64 = x.src + 0x40#64 := by bv_arith
  have hroot_len : (keyToBytes32 x.s.state.rootKey).length = 32 := by simp [keyToBytes32]
  have hroot_pos : 0 < (keyToBytes32 x.s.state.rootKey).length := by omega
  have hroot_lt : (keyToBytes32 x.s.state.rootKey).length < 2 ^ 63 := by omega
  have hroot_le64 : (keyToBytes32 x.s.state.rootKey).length ≤ 2 ^ 64 := by omega
  rw [vecU8At_eq_of_pos A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
      h38, h40]
  simp only [sepConj_assoc]
  refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have h32_pos : 0 < 32 := by decide
  have h32_le63 : 32 + 1 ≤ 2 ^ 63 := by decide
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨h32_pos, hpow2, h32_le63⟩
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 172#64)
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (32, 1)
  clear halloc
  refine SepWP.done (by sc_close) (by sc_close) ?_
  intro hcl1
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_80).base + 1164#64)
    wp_steps
    refine SepWP.done (by sc_close) (by sc_close) ?_
    exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    have hmem32 :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey).length := by
      rw [hroot_len]
    rw [hmem32]
    apply sepWPp_of_sepWP_lscl_sc hcl1 (mid := (blkPl_80).base + 232#64)
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.root.ptr, keyToBytes32 x.s.state.rootKey)
    clear hmemcpy
    wp_steps
    refine SepWP.done (by sc_close) (by sc_close) ?_
    intro hcl2
    refine SepWPp.weaken_pre ?_
      (hnext _ (sf_1.readReg64 (Reg.gpr 0#5))
        (by sc_close) (by sc_close) (by sc_close) (by sc_close) hcl2
        (by sc_close) (by sc_close) (by sc_close) (by sc_close)
        (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close))
    have hbuf32 :
        vecU8Buf A 32#64 (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey) =
          A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗
            (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ keyToBytes32 x.s.state.rootKey) := by
      have h := vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey)
        hroot_pos hroot_lt hoom64
      rwa [hroot_len] at h
    rw [vecU8At_eq_of_pos A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
        h38, h40, hbuf32]
    have hsp1_eq : sf_1.sp = s.sp := by sc_close
    have hsp_eq : sf.sp = s.sp := by sc_close
    simp only [sepConj_assoc, hsp1_eq, hsp_eq]
    exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

theorem sc_senderChain_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (senderChainCloneSpec A)))
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {localIk' remoteIk' : VecGhost}
    {v48 v60 v68 v70 v78 : BitVec 64} {v54 v84 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 0x0e8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
        then (blkPl_80).base + 0x23c#64
        else (blkPl_80).base + 0x150#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      OptSenderChainInline sender' x.s.state.senderChain (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      encSenderFieldMem sender' x.s.state.senderChain = encSenderFieldMem x.G.sender x.s.state.senderChain →
      SepWPp (lsProg_80 H) ret s1
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
          stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
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
        stackAt s.sp chainCloneStack ∗ F)
      Q (scPanicPost A x R s0) := by
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
            beq_ofNat_zero_eq_false hrc (by omega)
          simp [hne, hbeq]
      apply sepWPp_of_sepWP_lscl_sc hcl
        (mid := if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64)
      wp_steps
      refine SepWP.done (by sc_close) hrun ?_
      intro hcl1
      have hinl : OptSenderChainInline none x.s.state.senderChain
          (bytes104OfW6Q noneCap bq0 bq1 bq2 bq3 bq4 bq5) := by
        rw [hscM]
        exact OptSenderChainInline.none_of_chunks96 bq0 bq1 bq2 bq3 bq4 bq5
      have henc : encSenderFieldMem none x.s.state.senderChain =
          encSenderFieldMem x.G.sender x.s.state.senderChain := by
        rw [hscG]
      refine SepWPp.weaken_pre ?_
        (hnext _ none noneCap bq0 bq1 bq2 bq3 bq4 bq5
          (by sc_close) hrun rfl hsp hcl1 rfl (by sc_close) hx25 rfl hx29 htr (by sc_close) hinl henc)
      rw [hscG, hscM]
      dsimp only [optSenderChainAt, optSenderChainHeap]
      simp only [emp_sepConj, sepConj_emp, hx23, hx24, hx26, hx27, hw22]
      exact Entails.of_eq (by ac_rfl)
    | some sc =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_2nd fun h => False.elim h
  | some sg =>
    cases hscM : x.s.state.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_2nd fun h => False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_cap A (x.src + 0x90#64) sg sc]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcap_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcap_beq : (sg.srk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_82).base)
      wp_steps
      refine SepWP.done (by sc_close) hrun ?_
      intro hcl1
      refine SepWPp.weaken_pre
        (P' := (memRegion (s.sp + 0xf8#64) 104 ∗
            optSenderChainAt A (x.src + 0x90#64) (some sg) (some sc) ∗
            A.pool ∗ stackAt s.sp chainCloneStack) ∗
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
            A.pool ∗ stackAt s.sp chainCloneStack ∗
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
            stackAt s.sp chainCloneStack ∗ F) by ac_rfl]
        exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)
      · refine sepWPp_call_frame_lscl_sc (x := ⟨s.sp + 0xf8#64, x.src + 0x90#64, sg, sc⟩)
          hcall hcl1 (by sc_close) hrun hsp
          (ret_pc := (blkPl_80).base + 280#64) (by sc_close)
          rfl ⟨by sc_close, by sc_close⟩ rfl
          (fun _ _ _ _ h => allowPanic_not_exited h)
          (fun sf _ hm => sc_onPanic_of_callee_panic htr hm)
          fun sf hpcf hrunf hspf hcsm hclf => ?_
        clear hcall
        obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩ := hcsm
        dsimp only [senderChainCloneSpec]
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun htr_sf => ?_
        rw [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun g' => ?_
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hsrk', hpriv'⟩ => ?_
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
        refine SepWPp.weaken_pre
          (sepConj_mono_left (optSenderChainAt_entails_chunks104W6Q A (s.sp + 0xf8#64) (some g') (some sc))) ?_
        simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun scCap' =>
          SepWPp.exists_elim fun sq0 => SepWPp.exists_elim fun sq1 =>
          SepWPp.exists_elim fun sq2 => SepWPp.exists_elim fun sq3 =>
          SepWPp.exists_elim fun sq4 => SepWPp.exists_elim fun sq5 => ?_
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun hsc_inl => ?_
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
              ofNat_ne_zero_of_pos hrc (by omega)
            have hbeq : (BitVec.ofNat 64 x.s.state.receiverChains.length == 0#64) = false :=
              beq_false_of_ne hne0
            simp [hne, hbeq]
        apply sepWPp_of_sepWP_lscl_sc hclf
          (mid := if x.s.state.receiverChains = [] then (blkPl_80).base + 572#64 else (blkPl_80).base + 336#64)
        wp_steps
        refine SepWP.done (by sc_close) hrunf ?_
        intro hcl2
        refine SepWPp.weaken_pre ?_
          (hnext _ (some g') scCap' sq0 sq1 sq2 sq3 sq4 sq5
            (by sc_close) hrunf hsf_sp hsf_spA hcl2 hsf19 (by sc_close) hsf25 rfl (by sc_close) hsf_tr (by sc_close) hinl henc)
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

theorem sc_fields_1_to_4_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hkit : ScExternKit_placed A H)
    (hcall : subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (senderChainCloneSpec A)))
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v48 v58 v60 v68 v70 v78 v88 : BitVec 64} {v54 v84 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (blkPl_80).base + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.s.state.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.s.state.receiverChains = []
        then (blkPl_80).base + 0x23c#64
        else (blkPl_80).base + 0x150#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      LibsignalCodeLoaded lsmpl s1.mem →
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
      SepWPp (lsProg_80 H) ret s1
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
          stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
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
        stackAt s.sp chainCloneStack ∗ F)
      Q (scPanicPost A x R s0) := by
  rw [sc_vecGhostAt_0x18_eq A x.G.remoteIk x.src,
      vecU8Buf_pure_extract A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes,
      sc_vecU8At_0x30_root_eq A x.src x.G.root.cap x.G.root.ptr x.s.state.rootKey,
      stackAt_chainClone_eq_alloc s.sp]
  refine SepWPp.weaken_pre
    (P' := ⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧
              x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ ∗
            A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
            ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
            ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
            stackAt s.sp allocHookStack ∗
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
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hlen_rem, hcap_rem, _⟩ => ?_
  have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
  refine sc_localIk_placed hkit hpc hrun hsp hcl hx0 hx1 htr hvregs hrem_lt
    fun s1 localIk' hpc1 hrun1 hsp1 hspA1 hcl1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 htr1 hvregs1 hloc_b hloc_c => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
            ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
            ((s1.sp + 0x88#64) ↦₆₄ v88) ∗
            stackAt s1.sp allocHookStack ∗
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
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [sc_vecGhostAt_0x18_eq A x.G.remoteIk x.src]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_remoteIk_placed hkit hpc1 hrun1 hspA1 hcl1 hx24_1 hx25_1 htr1 hvregs1
    fun s2 remoteIk' hpc2 hrun2 hsp2 hspA2 hcl2 hx19_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 hrem_b hrem_c => ?_
  rw [← hsp2, hx21_1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
            ((s2.sp + 0x58#64) ↦₆₄ v58) ∗
            stackAt s2.sp allocHookStack ∗
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
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [sc_vecU8At_0x30_root_eq A x.src x.G.root.cap x.G.root.ptr x.s.state.rootKey]; exact Entails.of_eq (by ac_rfl)) ?_
  refine sc_rootKey_placed hkit hpc2 hrun2 hspA2 hcl2 hx25_2 hx27_2 htr2 hvregs2
    fun s3 rootPtr' hpc3 hrun3 hsp3 hspA3 hcl3 hx19_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx29_3 htr3 hvregs3 => ?_
  rw [← hsp3]
  refine SepWPp.weaken_pre
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
            stackAt s3.sp chainCloneStack ∗
            (vecGhostAt A x.G.localIk x.src ∗
              vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
              vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
              ((s3.sp + 0x58#64) ↦₆₄ rootPtr') ∗
              ((s3.sp + 0x88#64) ↦₆₄ localIk'.cap) ∗
              ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗ F))
    (by rw [stackAt_chainClone_eq_alloc s3.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  have hx19_3' : s3.readReg64 .x19 = x.dst := by rw [hx19_3, hx19_2, hx19_1]
  have hx22_3' : s3.readReg64 .x22 = x.s.state.sessionVersion.setWidth 64 := by rw [hx22_3, hx22_2, hx22_1]
  have hx23_3' : s3.readReg64 .x23 = localIk'.ptr := by rw [hx23_3, hx23_2, hx23_1]
  have hx24_3' : s3.readReg64 .x24 = remoteIk'.cap := by rw [hx24_3, hx24_2]
  have hx26_3' : s3.readReg64 .x26 = remoteIk'.ptr := by rw [hx26_3, hx26_2]
  have hx29_3' : s3.readReg64 .x29 = s3.sp + 0x170#64 := by rw [hx29_3, hx29_2, hx29_1, hx29, hsp3, hsp2, hsp1]
  refine sc_senderChain_placed hcall hpc3 hrun3 hspA3 hcl3 hx22_3' hx23_3' hx24_3' hx25_3 hx26_3' hx27_3 hx29_3' htr3 hvregs3 hrc_lt
    fun s4 sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 hpc4 hrun4 hsp4 hspA4 hcl4 hx19_4 hx21_4 hx25_4 hx26_4 hx29_4 htr4 hvregs4 hinl henc => ?_
  have hsp_eq : s3.sp = s.sp := by rw [hsp3, hsp2, hsp1]
  rw [hsp_eq] at hx21_4 hx29_4 ⊢
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s4 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc4 hrun4 (by rw [hsp4, hsp_eq]) hspA4 hcl4
      (by rw [hx19_4, hx19_3']) hx21_4 hx25_4 hx26_4 hx29_4
      htr4 hvregs4 hloc_b hloc_c hrem_b hrem_c hinl henc)

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionCloneAux
