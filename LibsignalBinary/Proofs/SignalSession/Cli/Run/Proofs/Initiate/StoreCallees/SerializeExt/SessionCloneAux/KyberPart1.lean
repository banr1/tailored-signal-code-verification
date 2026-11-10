/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.BasePart2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneEpilogue -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::clone`: `pending_kyber_pre_key` and `alice_base_key` Preliminaries

Symbolic execution of `pending_kyber_pre_key` (Field 7, `+0x250 ∨ +0x288 → +0x260 ∨ +0x374 ∨ +0x2d0`)
and the positive-length clone step of `alice_base_key` (Field 8).
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

private theorem sepWPpX_pure_2nd {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B) Q Qp) :
    SepWPpX img prog ret s (A ∗ ⌜φ⌝ ∗ B) Q Qp :=
  SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPpX.pure_elim h)

private theorem sepWPpX_pure_3rd {img : Obj.Image} {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPpX img prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPpX img prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp :=
  SepWPpX.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPpX.pure_elim h)

/-- Fast side-condition closer for `Part3`. -/
macro "sc_close3" : tactic =>
  `(tactic| (
    try clear hnext
    try clear hshim
    try clear halloc
    try clear hmemcpy
    try clear hcall
    try clear hpanic
    try clear hsub
    try clear hexpose
    try clear htail_pts
    try clear h_at_2a4
    try clear h_at_2e4
    try clear h_at_314
    first
    | rfl
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
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
        State.setPC, State.setPState,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_add, List.length_cons]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
       try simp only [reduceStateReadReg64,
        State.pc_writeReg64, State.pc_writeReg32,
        State.status_writeReg64, State.status_writeReg32,
        State.sp_writeReg64_gpr,
        State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        updateCalleeSavedVRegs]
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        updateCalleeSavedVRegs]
       done)
    | (dsimp only [State.spAligned, Reg.x0, Reg.x1, Reg.x2, Reg.x8, Reg.x9, Reg.x10,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.fp] at *
       subst_vars
       simp [*, State.setPC, State.setPState, State.writeReg64, State.writeReg32,
        calleeSavedVRegs_advancePC, calleeSavedVRegs_setPC, calleeSavedVRegs_setMem,
        calleeSavedVRegs_setPState, calleeSavedVRegs_writeReg64, calleeSavedVRegs_writeReg32,
        calleeSavedVRegs_writeReg, calleeSavedVRegs_writeVReg128_ite, isCalleeSavedVReg,
        updateCalleeSavedVRegs]
       done)))

/-! ## 1. Field 7: `pending_kyber_pre_key` (`+0x250 ∨ +0x288 → +0x260 ∨ +0x374 ∨ +0x2d0`) -/

theorem sc_pendingKyber_2a4_pos {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
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
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x2a4#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 gk.vec.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v28' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x260#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x374#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x2d0#64) →
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
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
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
          stackAt s.sp extHookStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
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
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hshim := sc_shim_ok_at hA (ext := ext)
  have halloc := sc_alloc_ok_at (A := A) (img := img) (ext := ext) hA
  have hmemcpy := sc_memcpy_ok_at hA (ext := ext)
  dsimp only [scShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
  dsimp only [scMemcpySpec] at hmemcpy
  have hpanic := sc_panic_0x474 (img := img) (A := A) (ext := ext) (ret := ret) (Q := Q) x s0
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
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x2a4 44
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  wpx_of_sepWP (mid := entry + bv% (696))
  wpx_steps
  wpx_call hshim ()
  clear hshim
  wpx_steps
  wpx_call halloc (gk.vec.bytes.length, 1)
  clear halloc
  wpx_clear_invs
  refine SepWP.done (by sc_close3) (by sc_close3) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPpX_pure_3rd fun htrace => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (1140))
    wp_steps
    refine SepWP.done (by sc_close3) (by sc_close3) ?_
    exact hpanic _ _ R (by sc_close3) (by sc_close3) (by sc_close3)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPpX_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    wpx_of_sepWP (mid := entry + bv% (720))
    wpx_steps
    wpx_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gk.vec.ptr, gk.vec.bytes)
    clear hmemcpy
    wpx_clear_invs
    refine SepWP.done (by sc_close3) (by sc_close3) ?_
    have hsp_eq : sf.sp = s.sp := by sc_close3
    have hsf1_sp : sf_1.sp = s.sp := by sc_close3
    refine SepWPpX.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gk.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) kw0
        (Or.inr (Or.inr (by sc_close3))) (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3))
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

/-- Field 7 (`+0x250 ∨ +0x288 → +0x260 ∨ +0x374 ∨ +0x2d0`):
clones `pending_kyber_pre_key` into `[sp + 0x40] = kybCap'`,
`[sp + 0x10] = kybPtr'`, and `[sp + 0x28] = v28'`. -/
theorem sc_pendingKyber {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v10 v40 : BitVec 64} {v28 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x250#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x288#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v28' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x260#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x374#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x2d0#64) →
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
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
          ScOptKybClone A x.G.kyber kybCap' kybPtr' v28' ∗
          ((s.sp + 0x10#64) ↦₆₄ kybPtr') ∗
          ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x40#64) ↦₆₄ kybCap') ∗
          stackAt s.sp extHookStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        optTailVecAt A 32 (x.src + 0x128#64) x.G.kyber ∗
        ((s.sp + 0x10#64) ↦₆₄ v10) ∗
        ((s.sp + 0x28#64) ↦₃₂ v28) ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗
        stackAt s.sp extHookStack ∗
        F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x250 16
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x288 28
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x368 12
  clear hfn
  cases hkyb : x.G.kyber with
  | none =>
    rw [hkyb] at hnext
    dsimp only [optTailVecAt, ScOptKybClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    rcases hpc with hpc | hpc
    · apply SepWPpX.of_sepWP (mid := entry + bv% (608))
      wp_steps
      refine SepWP.done (by sc_close3) (by sc_close3) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v10 v28
          (Or.inl (by sc_close3)) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · apply SepWPpX.of_sepWP (mid := entry + bv% (608))
      wp_steps
      refine SepWP.done (by sc_close3) (by sc_close3) ?_
      refine SepWPpX.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v10 v28
          (Or.inl (by sc_close3)) (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3)
          (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  | some gk =>
    rw [hkyb] at hnext
    dsimp only [optTailVecAt, ScOptKybClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPpX_pure_2nd fun htail => ?_
    obtain ⟨kw0, kw1, htail_val, htail_pts⟩ := exists_unpack32_pair_of_length_8 htail
    have h130 : x.src + 0x128#64 + 8#64 = x.src + 0x130#64 := by bv_arith
    have h138 : x.src + 0x128#64 + 16#64 = x.src + 0x138#64 := by bv_arith
    have h140 : x.src + 0x128#64 + BitVec.ofNat 64 24 = x.src + 0x140#64 := by bv_arith
    have h144 : x.src + 0x140#64 + 4#64 = x.src + 0x144#64 := by bv_arith
    rw [h140, htail_pts (x.src + 0x140#64), h144]
    rcases eq_nil_or_length_pos gk.vec.bytes with hnil | hpos
    · rw [vecGhostAt_eq_of_nil A gk.vec (x.src + 0x128#64) hnil, h130, h138]
      simp only [sepConj_assoc]
      refine sepWPpX_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length ∧
          ∃ kw1' : BitVec 32, gk.tail = unpack32 kw0 ++ unpack32 kw1'⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨rfl, kw1, htail_val⟩
      have h_pure1 : (⌜gk.tail.length = 32 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gk.vec.cap.toNat < 2 ^ 63 ∧ gk.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      rcases hpc with hpc | hpc
      · apply SepWPpX.of_sepWP (mid := entry + bv% (884))
        wp_steps
        refine SepWP.done (by sc_close3) (by sc_close3) ?_
        refine SepWPpX.weaken_pre ?_
          (hnext _ 0#64 1#64 kw0
            (Or.inr (Or.inl (by sc_close3))) (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3))
        rw [vecGhostAt_eq_of_nil A gk.vec (x.src + 0x128#64) hnil, h130, h138,
            h140, htail_pts (x.src + 0x140#64), h144, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
      · apply SepWPpX.of_sepWP (mid := entry + bv% (884))
        wp_steps
        refine SepWP.done (by sc_close3) (by sc_close3) ?_
        refine SepWPpX.weaken_pre ?_
          (hnext _ 0#64 1#64 kw0
            (Or.inr (Or.inl (by sc_close3))) (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3))
        rw [vecGhostAt_eq_of_nil A gk.vec (x.src + 0x128#64) hnil, h130, h138,
            h140, htail_pts (x.src + 0x140#64), h144, hnil, vecU8Buf_nil_eq A,
            h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gk.vec (x.src + 0x128#64) hpos, h130, h138]
      simp only [sepConj_assoc]
      refine sepWPpX_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hlen_lt : gk.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gk.vec.bytes.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gk.vec.bytes.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hsub : ∀ (s_2a4 : State), _ := fun s_2a4 =>
        sc_pendingKyber_2a4_pos (img := img) (A := A)
          (ext := ext) hA (x := x) (R := R) (s0 := s0) (s := s_2a4) (ret := ret) (Q := Q)
          (gk := gk) (kw0 := kw0) (kw1 := kw1) (v10 := v10) (v40 := v40) (F := F)
          htail htail_pts htail_val hpos hlen_le hcap_lt hptr
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      suffices h_at_2a4 : ∀ s_2a4 : State,
          s_2a4.pc = entry + bv% (676) →
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
          calleeSavedVRegs s_2a4 = calleeSavedVRegs s0 →
          SepWPpX img prog ret s_2a4
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
              stackAt s_2a4.sp extHookStack ∗ F)
            Q (scPanicPost A x R s0) by
        clear hsub
        rcases hpc with hpc | hpc
        · apply SepWPpX.of_sepWP (mid := entry + bv% (676))
          wp_steps
          refine SepWP.done (by sc_close3) (by sc_close3) ?_
          exact h_at_2a4 _ (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3)
        · apply SepWPpX.of_sepWP (mid := entry + bv% (676))
          wp_steps
          refine SepWP.done (by sc_close3) (by sc_close3) ?_
          exact h_at_2a4 _ (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
            (by sc_close3) (by sc_close3) (by sc_close3)
      intro s_2a4 hpc2a4 hrun2a4 hsp2a4 hspA2a4 hx19_2a4 hx21_2a4 hx23_2a4 hx24_2a4 hx25_2a4 hx26_2a4 hx27_2a4 hx28_2a4 hx29_2a4 htr2a4 hvregs2a4
      refine hsub s_2a4 hpc2a4 hrun2a4 hspA2a4 hx21_2a4 hx25_2a4 htr2a4 hvregs2a4
        fun s1 kybCap' kybPtr' v28' hpc1 hrun1 hsp1 hspA1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 => ?_
      clear hsub
      rw [hsp2a4]
      exact hnext s1 kybCap' kybPtr' v28'
        hpc1 hrun1 (hsp1.trans hsp2a4) hspA1
        (hx19_1.trans hx19_2a4) (hx23_1.trans hx23_2a4) (hx24_1.trans hx24_2a4) hx25_1
        (hx26_1.trans hx26_2a4) (hx27_1.trans hx27_2a4) (hx28_1.trans hx28_2a4)
        (hx29_1.trans hx29_2a4) htr1 hvregs1

/-! ## 2. Field 8: `alice_base_key` (`+0x260 ∨ +0x374 ∨ +0x2d0 → +0x390 / +0x30c`) -/

theorem sc_aliceBaseKey_2e4_pos {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v30 : BitVec 64} {F : SepProp}
    (halice : 0 < x.G.alice.bytes.length)
    (hlen_le : x.G.alice.bytes.length ≤ x.G.alice.cap.toNat)
    (hcap_lt : x.G.alice.cap.toNat < 2 ^ 63)
    (hptr : x.G.alice.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x2e4#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.G.alice.bytes.length)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x30c#64 →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = alice'.cap →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      alice'.bytes = x.G.alice.bytes →
      alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecGhostAt A x.G.alice (x.src + 0x60#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          ((s.sp + 0x30#64) ↦₆₄ alice'.ptr) ∗
          stackAt s.sp extHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        ((x.src + 0x60#64) ↦₆₄ x.G.alice.cap) ∗
        ((x.src + 0x68#64) ↦₆₄ x.G.alice.ptr) ∗
        ((x.src + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length) ∗
        (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
        A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
        memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length)
          (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗
        stackAt s.sp extHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hshim := sc_shim_ok_at hA (ext := ext)
  have halloc := sc_alloc_ok_at (A := A) (img := img) (ext := ext) hA
  have hmemcpy := sc_memcpy_ok_at hA (ext := ext)
  dsimp only [scShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack, withStack, rustAllocSpec] at halloc
  dsimp only [scMemcpySpec] at hmemcpy
  have hpanic := sc_panic_0x474 (img := img) (A := A) (ext := ext) (ret := ret) (Q := Q) x s0
  have h68 : x.src + 0x60#64 + 8#64 = x.src + 0x68#64 := by bv_arith
  have h70 : x.src + 0x60#64 + 16#64 = x.src + 0x70#64 := by bv_arith
  have halice_lt : x.G.alice.bytes.length < 2 ^ 63 := by omega
  have halice_le63 : x.G.alice.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have halice_le64 : x.G.alice.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk x.G.alice.bytes.length 1 := ⟨halice, hpow2, halice_le63⟩
  have htoNat : (BitVec.ofNat 64 x.G.alice.bytes.length).toNat = x.G.alice.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x2e4 40
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  wpx_of_sepWP (mid := entry + bv% (760))
  wpx_steps
  wpx_call hshim ()
  clear hshim
  wpx_steps
  wpx_call halloc (x.G.alice.bytes.length, 1)
  clear halloc
  wpx_clear_invs
  refine SepWP.done (by sc_close3) (by sc_close3) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPpX_pure_3rd fun htrace => ?_
    apply SepWPpX.of_sepWP (mid := entry + bv% (1140))
    wp_steps
    refine SepWP.done (by sc_close3) (by sc_close3) ?_
    exact hpanic _ _ R (by sc_close3) (by sc_close3) (by sc_close3)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPpX_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    wpx_of_sepWP (mid := entry + bv% (780))
    wpx_steps
    wpx_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.ptr, x.G.alice.bytes)
    clear hmemcpy
    wpx_clear_invs
    refine SepWP.done (by sc_close3) (by sc_close3) ?_
    have hsp_eq : sf.sp = s.sp := by sc_close3
    have hsf1_sp : sf_1.sp = s.sp := by sc_close3
    refine SepWPpX.weaken_pre ?_
      (hnext _ ⟨BitVec.ofNat 64 x.G.alice.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.bytes⟩
        (by sc_close3) (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3)
        (by sc_close3) (by sc_close3) (by sc_close3) rfl rfl)
    rw [vecGhostAt_eq_of_pos A x.G.alice (x.src + 0x60#64) halice, h68, h70,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.alice.bytes halice halice_lt hoom64]
    have h_pure_emp :
        (⌜x.G.alice.bytes.length ≤ x.G.alice.cap.toNat ∧
            x.G.alice.cap.toNat < 2 ^ 63 ∧ x.G.alice.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [h_pure_emp]
    simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
