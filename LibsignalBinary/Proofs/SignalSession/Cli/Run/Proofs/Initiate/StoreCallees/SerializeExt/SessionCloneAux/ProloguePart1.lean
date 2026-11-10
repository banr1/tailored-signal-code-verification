/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart1
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneEpilogue -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::clone`: Prologue and Identity/Root Keys

Symbolic execution of the prologue (`+0x000 → +0x020`) and cloning of `local_identity_public`,
`remote_identity_public`, and `root_key` (`+0x020 → +0x0e8`).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.ChainCloneLocal1 hiding
  allocFailedIn_of_eq srk_length_pos ofNat_ne_zero_of_pos beq_ofNat_zero_eq_false sepWPp_pure_mid
  vecU8At_eq_of_nil vecU8At_eq_of_pos vecGhostAt_eq_of_nil vecGhostAt_eq_of_pos vecU8Buf_nil_eq vecU8Buf_pos_eq
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.E2E.Record.Serialization
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem sepWPpX_pure_2nd {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B) Q Qp) :
    SepWPpX img prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp :=
  SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPpX.pure_elim h)

theorem sepWPpX_pure_3rd {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPpX img prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp :=
  SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPpX.pure_elim h)

theorem SepWPpX.call_frame {α : Type} {img : Obj.Image} {prog : Program}
    {entry ret ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {s : State} {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPpX img prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (h_no_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPpX img prog ret s P Q Qp := by
  refine SepWPpX.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic hnext h_no_oom
  intro R hm
  rw [hP] at hm
  rw [hspec, sepConj_assoc]
  exact Satisfies.mono (Entails.pure_right hφ (Entails.of_eq (by ac_rfl))) hm

@[scoped arm64_norm, scoped wp_norm]
theorem fp_add_neg_112 (sp : BitVec 64) :
    (sp + 0x170#64) + bv% (2 ^ 64 - 112) = sp + 0x100#64 := by bv_omega

/-- Fast side-condition closer that clears large continuation/spec hypotheses before simplifying. -/
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

/-- Prologue (`+0x000 → +0x020`): allocate 0x1d0-byte frame, save `x19..x30` at `[sp + 0x170..0x1c8]`,
and set `x29 = sp + 0x170`. -/
theorem sc_prologue {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {rv : ScSavedVals} {F : SepProp}
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.dst) (hx1 : s0.readReg64 .x1 = x.src)
    (hnext : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x020#64 →
      s1.status = .Running →
      s1.sp = s0.sp - 0x1d0#64 →
      s1.spAligned = true →
      s1.readReg64 .x0 = x.dst →
      s1.readReg64 .x1 = x.src →
      s1.readReg64 .x29 = s1.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (scSavedRegsAt (s0.sp - 0x1d0#64)
          (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28) (s0.readReg64 .x27)
          (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
          (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19) ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s0
      (scSavedRegsAt (s0.sp - 0x1d0#64)
        rv.r29 rv.r30 rv.r28 rv.r27 rv.r26 rv.r25 rv.r24 rv.r23 rv.r22 rv.r21 rv.r20 rv.r19 ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hsp_sub_align : ((s0.sp - 464#64) &&& 15#64 == 0#64) = true :=
    s0.spAligned_sub 464#64 hsp
  unfold scSavedRegsAt
  simp only [sepConj_assoc]
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x000 32
  have := libsignalSessionCode_fetch_fnAddr_entry (b := img.base)
    (H := Rust.withPanics ext)
    hfn (by decide) (ls_decode% sessionCloneBin (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (32))
  wp_steps
  refine SepWP.done (by sc_close) hrun ?_
  refine SepWPpX.weaken_pre ?_
    (hnext _ (by sc_close) hrun rfl (by sc_close) (by sc_close) (by sc_close) (by sc_close) rfl (by sc_close))
  unfold scSavedRegsAt
  dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
    Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
  exact Entails.of_eq (by ac_rfl)

/-- Clone `local_identity_public` (`+0x020 → +0x0d0 / +0x064`). -/
theorem sc_localIk {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x020#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = x.dst) (hx1 : s.readReg64 .x1 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x0d0#64
        else (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x064#64) →
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
          stackAt s.sp extHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk x.src ∗
        ((x.src + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((x.src + 0x148#64) ↦₃₂ x.s.state.sessionVersion) ∗
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  rcases eq_nil_or_length_pos x.G.localIk.bytes with hloc | hloc
  · rw [vecGhostAt_eq_of_nil A x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x020 20
    sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x0c4 12
    clear hfn
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
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
    apply SepWPpX.of_sepWP (mid := if x.G.remoteIk.bytes = [] then entry + bv% (208) else entry + bv% (100))
    wp_steps
    refine SepWP.done (by sc_close) hrun ?_
    refine SepWPpX.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ (by sc_close) hrun rfl hsp
        rfl rfl rfl rfl rfl rfl rfl htr (by sc_close) hloc.symm (by simp [hloc]))
    rw [vecGhostAt_eq_of_nil A x.G.localIk x.src hloc, vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · rw [vecGhostAt_eq_of_pos A x.G.localIk x.src hloc]
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := sc_shim_ok_at hA (ext := ext)
    have halloc := sc_alloc_ok_at (img := img) (ext := ext) hA
    have hmemcpy := sc_memcpy_ok_at hA (ext := ext)
    dsimp only [scShimSpec] at hshim
    dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
    dsimp only [scMemcpySpec] at hmemcpy
    have hpanic : ∀ (s_p : State) (P_p : SepProp),
        s_p.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x474#64 →
        s_p.status = .Running →
        s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s_p P_p Q (scPanicPost A x R s0) :=
      fun s_p P_p => sc_panic_0x474 x s0 s_p P_p R
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
    sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x020 68
    clear hfn
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    wpx_of_sepWP (mid := entry + bv% (72))
    wpx_steps
    wpx_call hshim ()
    clear hshim
    wpx_steps
    wpx_call halloc (x.G.localIk.bytes.length, 1)
    clear halloc
    wpx_clear_invs
    refine SepWP.done (by sc_close) (by sc_close) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPpX_pure_3rd fun htrace => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (1140))
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
    · clear hpanic
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPpX_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      have hpc_rem :
          (if (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then entry + bv% (208) else entry + bv% (100)) =
          (if x.G.remoteIk.bytes = [] then entry + bv% (208) else entry + bv% (100)) := by
        rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
        · simp [hrem]
        · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
          have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem (by omega)
          simp [hne, hbeq]
      wpx_of_sepWP (mid := if x.G.remoteIk.bytes = [] then entry + bv% (208) else entry + bv% (100))
      wpx_steps
      wpx_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.ptr, x.G.localIk.bytes)
      clear hmemcpy
      wpx_steps
      wpx_clear_invs
      refine SepWP.done (by sc_close) (by sc_close) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.localIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.bytes⟩
          (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) rfl rfl)
      rw [vecGhostAt_eq_of_pos A x.G.localIk x.src hloc,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.localIk.bytes hloc hloc_lt hoom64]
      have hsp1_eq : sf_1.sp = s.sp := by sc_close
      have hsp_eq : sf.sp = s.sp := by sc_close
      simp only [sepConj_assoc, hsp1_eq, hsp_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

/-- Clone `remote_identity_public` (`+0x0d0 / +0x064 → +0x098`) and spill `x21` (`localIk'.cap`) at `[sp + 0x88]`. -/
theorem sc_remoteIk {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v88 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x0d0#64
      else (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x064#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x098#64 →
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x88#64) ↦₆₄ s.readReg64 .x21) ∗
          stackAt s.sp extHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (x.src + 0x18#64) ∗
        ((x.src + 0x40#64) ↦₆₄ 32#64) ∗
        ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have h20 : x.src + 0x18#64 + 8#64 = x.src + 0x20#64 := by bv_arith
  have h28 : x.src + 0x18#64 + 16#64 = x.src + 0x28#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
  · simp only [hrem, ↓reduceIte] at hpc
    rw [hrem] at hx24
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28]
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x0d0 16
    clear hfn
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPpX.of_sepWP (mid := entry + bv% (152))
    wp_steps
    refine SepWP.done rfl hrun ?_
    refine SepWPpX.weaken_pre ?_
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
    refine sepWPpX_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := sc_shim_ok_at hA (ext := ext)
    have halloc := sc_alloc_ok_at (img := img) (ext := ext) hA
    have hmemcpy := sc_memcpy_ok_at hA (ext := ext)
    dsimp only [scShimSpec] at hshim
    dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
    dsimp only [scMemcpySpec] at hmemcpy
    have hpanic : ∀ (s_p : State) (P_p : SepProp),
        s_p.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x480#64 →
        s_p.status = .Running →
        s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s_p P_p Q (scPanicPost A x R s0) :=
      fun s_p P_p => sc_panic_0x480 x s0 s_p P_p R
    have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
    have hrem_le63 : x.G.remoteIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hrem_le64 : x.G.remoteIk.bytes.length ≤ 2 ^ 64 := by omega
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.remoteIk.bytes.length 1 := ⟨hrem, hpow2, hrem_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.remoteIk.bytes.length).toNat = x.G.remoteIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x064 52
    clear hfn
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    wpx_of_sepWP (mid := entry + bv% (120))
    wpx_steps
    wpx_call hshim ()
    clear hshim
    wpx_steps
    wpx_call halloc (x.G.remoteIk.bytes.length, 1)
    clear halloc
    wpx_clear_invs
    refine SepWP.done (by sc_close) (by sc_close) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPpX_pure_3rd fun htrace => ?_
      apply SepWPpX.of_sepWP (mid := entry + bv% (1152))
      wp_steps
      refine SepWP.done (by sc_close) (by sc_close) ?_
      exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
    · clear hpanic
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPpX_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      wpx_of_sepWP (mid := entry + bv% (152))
      wpx_steps
      wpx_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.ptr, x.G.remoteIk.bytes)
      clear hmemcpy
      wpx_steps
      wpx_clear_invs
      refine SepWP.done (by sc_close) (by sc_close) ?_
      have h21_eq : sf.readReg64 (Reg.gpr 21#5) = s.readReg64 .x21 := by sc_close
      refine SepWPpX.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.remoteIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.bytes⟩
          (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close)
          (by sc_close) (by sc_close) (by sc_close) (by sc_close) (by sc_close) rfl rfl)
      rw [vecGhostAt_eq_of_pos A x.G.remoteIk (x.src + 0x18#64) hrem, h20, h28,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.remoteIk.bytes hrem hrem_lt hoom64]
      have hsp1_eq : sf_1.sp = s.sp := by sc_close
      have hsp_eq : sf.sp = s.sp := by sc_close
      simp only [sepConj_assoc, hsp1_eq, hsp_eq, h21_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

/-- Clone `root_key` (`+0x098 → +0x0e8`, 32 bytes) and store the new pointer at `[sp + 0x58]`. -/
theorem sc_rootKey {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v58 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x098#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src) (hx27 : s.readReg64 .x27 = 32#64)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x0e8#64 →
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
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.s.state.rootKey) ∗
          ((s.sp + 0x58#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp extHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecU8At A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hshim := sc_shim_ok_at hA (ext := ext)
  have halloc := sc_alloc_ok_at (img := img) (ext := ext) hA
  have hmemcpy := sc_memcpy_ok_at hA (ext := ext)
  dsimp only [scShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
  dsimp only [scMemcpySpec] at hmemcpy
  have hpanic : ∀ (s_p : State) (P_p : SepProp),
      s_p.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x48c#64 →
      s_p.status = .Running →
      s_p.trace = s0.trace ++ [allocFailedEvent] →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s_p P_p Q (scPanicPost A x R s0) :=
    fun s_p P_p => sc_panic_0x48c x s0 s_p P_p R
  have h38 : x.src + 0x30#64 + 8#64 = x.src + 0x38#64 := by bv_arith
  have h40 : x.src + 0x30#64 + 16#64 = x.src + 0x40#64 := by bv_arith
  have hroot_len : (keyToBytes32 x.s.state.rootKey).length = 32 := by simp [keyToBytes32]
  have hroot_pos : 0 < (keyToBytes32 x.s.state.rootKey).length := by omega
  have hroot_lt : (keyToBytes32 x.s.state.rootKey).length < 2 ^ 63 := by omega
  have hroot_le64 : (keyToBytes32 x.s.state.rootKey).length ≤ 2 ^ 64 := by omega
  rw [vecU8At_eq_of_pos A (x.src + 0x30#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.s.state.rootKey) hroot_pos,
      h38, h40]
  simp only [sepConj_assoc]
  refine sepWPpX_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have h32_pos : 0 < 32 := by decide
  have h32_le63 : 32 + 1 ≤ 2 ^ 63 := by decide
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨h32_pos, hpow2, h32_le63⟩
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x098 44
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  wpx_of_sepWP (mid := entry + bv% (172))
  wpx_steps
  wpx_call hshim ()
  clear hshim
  wpx_steps
  wpx_call halloc (32, 1)
  clear halloc
  wpx_clear_invs
  refine SepWP.done (by sc_close) (by sc_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPpX_pure_3rd fun htrace => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (1164))
    wp_steps
    refine SepWP.done (by sc_close) (by sc_close) ?_
    exact hpanic _ _ (by sc_close) (by sc_close) (by sc_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPpX_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    have hmem32 :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.s.state.rootKey).length := by
      rw [hroot_len]
    rw [hmem32]
    wpx_of_sepWP (mid := entry + bv% (232))
    wpx_steps
    wpx_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.root.ptr, keyToBytes32 x.s.state.rootKey)
    clear hmemcpy
    wpx_steps
    wpx_clear_invs
    refine SepWP.done (by sc_close) (by sc_close) ?_
    refine SepWPpX.weaken_pre ?_
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

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
