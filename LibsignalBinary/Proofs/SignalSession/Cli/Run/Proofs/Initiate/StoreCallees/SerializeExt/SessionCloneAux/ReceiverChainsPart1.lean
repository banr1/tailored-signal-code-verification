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
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionCloneAux.ChainCloneEpilogue -- shake: keep

@[expose] public section

set_option autoImplicit false

/-!
# `SessionStructure::clone`: `receiver_chains` Loop

Symbolic execution of the per-element copy and induction over the `receiver_chains` clone loop
(`+0x188 → +0x1dc`).
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

private theorem call_frame_x {α : Type} {img : Obj.Image} {prog : Program}
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
theorem fp_add_neg_104 (sp : BitVec 64) :
    (sp + 0x170#64) + bv% (2 ^ 64 - 104) = sp + 0x108#64 := by bv_omega

@[scoped arm64_norm, scoped wp_norm]
theorem fp_add_neg_24_hex (sp : BitVec 64) :
    (sp + 0x170#64) + 0xffffffffffffffe8#64 = sp + 0x158#64 := by bv_omega

/-- Fast side-condition closer for `Part2`. -/
macro "sc_close2" : tactic =>
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
    try clear h_at_200
    try clear h_at_2a4
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

/-! ## 1. Field 5: `receiver_chains` (`+0x23c / +0x150 → +0x240 / +0x1dc`) -/

/-- Copy the 104-byte cloned receiver chain from `sp + 0xf8` to `dst = x28` (`+0x1a4 → +0x1dc / +0x188`). -/
theorem sc_receiverChains_copy {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (rem : Nat) (src dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x1a4#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = off)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 rem)
    (hx24 : s.readReg64 .x24 = src + 0x68#64)
    (hx28 : s.readReg64 .x28 = dst)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : rem < 2 ^ 63)
    (hnext : ∀ s1 : State,
      s1.pc = (if rem = 0 then
                 (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x1dc#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x188#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = off + 0x68#64 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = BitVec.ofNat 64 rem →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x1a4 56
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  have hpc_rem :
      (if !(BitVec.ofNat 64 rem == 0#64) = true then entry + bv% (392) else entry + bv% (476)) =
      (if rem = 0 then entry + bv% (476) else entry + bv% (392)) := by
    rcases Nat.eq_zero_or_pos rem with rfl | hpos
    · simp
    · have hne : rem ≠ 0 := Nat.ne_of_gt hpos
      have hne0 : BitVec.ofNat 64 rem ≠ 0#64 := ofNat_ne_zero_of_pos hpos (by omega)
      have hbeq : (BitVec.ofNat 64 rem == 0#64) = false := beq_false_of_ne hne0
      simp [hne, hbeq]
  clear hrem_lt
  rw [chunks104_6QWAt_sp_0xf8 s.sp sq0 sq1 sq2 sq3 sq4 sq5 sw6] at hnext ⊢
  unfold chunks104_6QWAt at hnext ⊢
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at hnext ⊢
  apply SepWPpX.of_sepWP
    (mid := if !(BitVec.ofNat 64 rem == 0#64) = true then entry + bv% (392) else entry + bv% (476))
  wp_steps
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  refine SepWPpX.weaken_pre ?_
    (hnext _
      (by rw [← hpc_rem]; sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2))
  exact Entails.of_eq (by ac_rfl)

/-- Single iteration of the `receiver_chains` clone loop (`+0x188 → +0x1dc / +0x188`). -/
theorem sc_receiverChains_iter {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok img A ext)
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x188#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = src)
    (hx20 : s.readReg64 .x20 = off)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx22 : s.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (rem + 1))
    (hx27 : s.readReg64 .x27 = dst_base)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hmul_lt : (rem + 1) * 104 < 2 ^ 63)
    (hnext : ∀ (s1 : State) (g' : ChainGhost),
      lenField 7 (encChainMem (g', rc)) = lenField 7 (encChainMem (g, rc)) →
      s1.pc = (if rem = 0 then
                 (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x1dc#64
               else
                 (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x188#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = off + 0x68#64 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = BitVec.ofNat 64 rem →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = dst_base →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          chainAt A (g, rc) src ∗
          chainAt A (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStackX ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        chainAt A (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStackX ∗
        F)
      Q (scPanicPost A x R s0) := by
  have hfn := fnOff_sessionClone
  have hcall := sc_chainClone_ok_at (img := img) (A := A) (ext := ext) hcc
  clear hcc
  have hsub : ∀ (sf : State) (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
      (sw6 dw6 : BitVec 64) (F_copy : SepProp), _ :=
    fun sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy =>
      sc_receiverChains_copy (img := img) (A := A)
        (ext := ext) (x := x) (R := R) (s0 := s0) (s := sf) (ret := ret) (Q := Q)
        rem src (dst_base + off) off sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy
  have hsub_eq : (off + BitVec.ofNat 64 (rem + 1) * 104#64) - off =
      BitVec.ofNat 64 (rem + 1) * 104#64 := by bv_arith
  have hmul_beq : (BitVec.ofNat 64 (rem + 1) * 104#64 == 0#64) = false :=
    segClone_bv_ofNat_mul_104_beq_zero (Nat.succ_pos rem) hmul_lt
  have hrem_lt : rem < 2 ^ 63 := by omega
  clear hmul_lt
  sessionClone_fetches img.base (Rust.withPanics ext) hfn 0x188 28
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPpX.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  wp_steps
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  refine SepWPpX.weaken_pre
    (P' := (memRegion (s.sp + 0xf8#64) 104 ∗ chainAt A (g, rc) src ∗ A.pool ∗
              stackAt s.sp chainCloneStackX) ∗
            (memRegion (dst_base + off) 104 ∗ F))
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine call_frame_x (x := ⟨s.sp + 0xf8#64, src, (g, rc)⟩)
      hcall (by sc_close2) (by sc_close2) (by sc_close2)
      (ret_pc := entry + bv% (420)) (by sc_close2)
      rfl ⟨by sc_close2, by sc_close2⟩ rfl
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf _ hm => sc_onPanic_of_callee_panic (by sc_close2) hm)
      fun sf hpcf hrunf hspf hcsm => ?_
  clear hcall
  obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩ := hcsm
  dsimp only [chainCloneSpecX]
  simp only [sepConj_assoc]
  refine SepWPpX.pure_elim fun htr_sf => ?_
  rw [sepExists_sepConj_left]
  refine SepWPpX.exists_elim fun g' => ?_
  simp only [sepConj_assoc]
  refine SepWPpX.pure_elim fun ⟨hsrk', hpriv', _⟩ => ?_
  have henc_g' : lenField 7 (encChainMem (g', rc)) = lenField 7 (encChainMem (g, rc)) := by
    simp only [encChainMem, hsrk', hpriv']
  have hsf_sp : sf.sp = s.sp := hspf
  have hsf19 : sf.readReg64 .x19 = s.readReg64 .x19 := hcs19
  have hsf20 : sf.readReg64 .x20 = off := by simpa [Reg.x20, hx20] using hcs20
  have hsf21 : sf.readReg64 .x21 = sf.sp + 0xf8#64 := by
    rw [hsf_sp]; simpa [Reg.x21, hx21] using hcs21
  have hsf22 : sf.readReg64 .x22 = s.readReg64 .x22 := hcs22
  have hsf23 : sf.readReg64 .x23 = BitVec.ofNat 64 rem := by
    rw [segClone_bv_ofNat_succ_sub_one] at hcs23; exact hcs23
  have hsf24 : sf.readReg64 .x24 = src + 0x68#64 := hcs24
  have hsf25 : sf.readReg64 .x25 = s.readReg64 .x25 := hcs25
  have hsf26 : sf.readReg64 .x26 = s.readReg64 .x26 := hcs26
  have hsf27 : sf.readReg64 .x27 = dst_base := by simpa [Reg.x27, hx27] using hcs27
  have hsf28 : sf.readReg64 .x28 = dst_base + off := hcs28
  have hsf29 : sf.readReg64 .x29 = sf.sp + 0x170#64 := by
    rw [hsf_sp]; simpa [Reg.x29, hx29] using hcs29
  have hsf_tr : sf.trace = s0.trace := htr_sf.trans htr
  have hsf_vregs : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    simpa [hvregs] using hcsv
  have hsf_spA : sf.spAligned = true := by
    unfold State.spAligned at hsp ⊢; rw [hsf_sp]; exact hsp
  dsimp only [State.setPC, State.setPState, State.writeReg64]
  simp only [← hsf_sp]
  refine SepWPpX.weaken_pre
    (sepConj_mono_left (chainAt_entails_chunks104_6QW A (g', rc) (sf.sp + 0xf8#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPpX.exists_elim fun sq0 => SepWPpX.exists_elim fun sq1 =>
    SepWPpX.exists_elim fun sq2 => SepWPpX.exists_elim fun sq3 =>
    SepWPpX.exists_elim fun sq4 => SepWPpX.exists_elim fun sq5 =>
    SepWPpX.exists_elim fun sw6 => ?_
  simp only [sepConj_assoc]
  refine SepWPpX.pure_elim fun hch_inl => ?_
  refine SepWPpX.weaken_pre
    (P' := memRegion (dst_base + off) 104 ∗
            chunks104_6QWAt (sf.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
            stackAt sf.sp chainCloneStackX ∗ F)
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWPpX.weaken_pre
    (sepConj_mono_left (memRegion_104_entails_chunks104_6QWAt (dst_base + off))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPpX.exists_elim fun dq0 => SepWPpX.exists_elim fun dq1 =>
    SepWPpX.exists_elim fun dq2 => SepWPpX.exists_elim fun dq3 =>
    SepWPpX.exists_elim fun dq4 => SepWPpX.exists_elim fun dq5 =>
    SepWPpX.exists_elim fun dw6 => ?_
  refine SepWPpX.weaken_pre
    (P' := chunks104_6QWAt (sf.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chunks104_6QWAt (dst_base + off) dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗
            (chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
              stackAt sf.sp chainCloneStackX ∗ F))
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine hsub sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 _
    hpcf hrunf hsf_spA hsf20 hsf21 hsf23 hsf24 hsf28 hsf29 hsf_tr hsf_vregs hrem_lt
    fun s1 hpc1 hrun1 hsp1 hspA1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
  clear hsub
  rw [hsf_sp] at hx21_1 hx29_1 ⊢
  refine SepWPpX.weaken_pre ?_
    (hnext s1 g' henc_g'
      hpc1 hrun1 (hsp1.trans hsf_sp) hspA1
      hx1_1 (hx19_1.trans hsf19) hx20_1 hx21_1 (hx22_1.trans hsf22)
      hx23_1 (hx25_1.trans hsf25) (hx26_1.trans hsf26) (hx27_1.trans hsf27)
      hx29_1 htr1 hvregs1)
  have h104 := chunks104_6QWAt_entails_memRegion (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6
  have hdst_chain := chainAt_of_chunks104_6QW A (g', rc) (dst_base + off) hch_inl
  refine Entails.trans (sepConj_mono_left h104) ?_
  refine Entails.trans
    (Q := memRegion (s.sp + 0xf8#64) 104 ∗
          (chunks104_6QWAt (dst_base + off) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ chainHeap A (g', rc)) ∗
          chainAt A (g, rc) src ∗ A.pool ∗ stackAt s.sp chainCloneStackX ∗ F)
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hdst_chain)) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Induction over `rcs_tl` for the `receiver_chains` clone loop (`+0x188 → +0x1dc`). -/
theorem sc_receiverChains_loop {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok img A ext)
    (x : SessionCloneGhost) (R : SepProp) (s0 : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (dst_base : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length →
      (rcs_tl.length + 1) * 104 < 2 ^ 63 →
      (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x188#64 →
      s.status = .Running →
      s.spAligned = true →
      s.readReg64 .x1 = src →
      s.readReg64 .x20 = off →
      s.readReg64 .x21 = s.sp + 0xf8#64 →
      s.readReg64 .x22 = off + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 →
      s.readReg64 .x23 = BitVec.ofNat 64 (rcs_tl.length + 1) →
      s.readReg64 .x27 = dst_base →
      s.readReg64 .x29 = s.sp + 0x170#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (s1 : State) (gs' : List ChainGhost),
        gs'.length = (rc :: rcs_tl).length →
        ((gs'.zip (rc :: rcs_tl)).map fun gc => lenField 7 (encChainMem gc)) =
          (((g :: gs_tl).zip (rc :: rcs_tl)).map fun gc => lenField 7 (encChainMem gc)) →
        s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessionCloneName + 0x1dc#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        s1.spAligned = true →
        s1.readReg64 .x19 = s.readReg64 .x19 →
        s1.readReg64 .x21 = s.sp + 0xf8#64 →
        s1.readReg64 .x25 = s.readReg64 .x25 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = dst_base →
        s1.readReg64 .x29 = s.sp + 0x170#64 →
        s1.trace = s0.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s0 →
        SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s1
          (A.pool ∗
            arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0xf8#64) 104 ∗
            stackAt s.sp chainCloneStackX ∗
            F)
          Q (scPanicPost A x R s0)) →
      SepWPpX img (tripleRatchetProgAtExt img.base ext) ret s
        (A.pool ∗
          arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStackX ∗
          F)
        Q (scPanicPost A x R s0) := by
  induction rcs_tl with
  | nil =>
    intro s rc g gs_tl src off F hgs hmul_lt _ hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hnext
    cases gs_tl with
    | cons _ _ => simp at hgs
    | nil =>
      simp only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil,
        sepConj_emp, List.length_nil, Nat.zero_add, Nat.one_mul] at *
      refine sc_receiverChains_iter hcc x R s0 s ret Q g rc 0 src dst_base off F
        hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hmul_lt
        fun s1 g' henc_g' hpc1 hrun1 hsp1 hspA1 _ hx19_1 _ hx21_1 _ _ hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
      simp only [↓reduceIte] at hpc1
      have h1 := hnext s1 [g'] rfl (by simp [henc_g']) hpc1 hrun1 hsp1 hspA1
        hx19_1 hx21_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1
      simpa only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil, sepConj_emp]
        using h1
  | cons rc2 rcs2 ih =>
    intro s rc g gs_tl src off F hgs hmul_lt hsz_le hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hnext
    cases gs_tl with
    | nil => simp at hgs
    | cons g2 gs2 =>
      have hgs2 : gs2.length = rcs2.length := by simpa using hgs
      have hmul2_lt : (rcs2.length + 1) * 104 < 2 ^ 63 := by simp [Nat.add_mul] at hmul_lt; omega
      have hsz2_le : (rcs2.length + 1) * 104 ≤ 2 ^ 64 := by simp [Nat.add_mul] at hsz_le; omega
      have hsplit_mr :
          memRegion (dst_base + off) (((rc2 :: rcs2).length + 1) * 104) =
            memRegion (dst_base + off) 104 ∗
              memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) := by
        refine memRegion_split' (n := 104) (k := (rcs2.length + 1) * 104) ?_
          (by bv_arith) hsz_le
        simp [List.length_cons, Nat.add_mul]; omega
      rw [List.zip_cons_cons, arrayAt_cons, hsplit_mr]
      refine SepWPpX.weaken_pre
        (P' := A.pool ∗
                chainAt A (g, rc) src ∗
                memRegion (dst_base + off) 104 ∗
                memRegion (s.sp + 0xf8#64) 104 ∗
                stackAt s.sp chainCloneStackX ∗
                (arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                  memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗ F))
        (by exact Entails.of_eq (by ac_rfl)) ?_
      refine sc_receiverChains_iter hcc x R s0 s ret Q g rc (rcs2.length + 1)
        src dst_base off _
        hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hmul_lt
        fun s1 g' henc_g' hpc1 hrun1 hsp1 hspA1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
      have hne0 : rcs2.length + 1 ≠ 0 := Nat.succ_ne_zero _
      simp only [hne0, ↓reduceIte] at hpc1
      have hx22_next : s1.readReg64 .x22 =
          (off + 0x68#64) + BitVec.ofNat 64 (rcs2.length + 1) * 104#64 := by
        rw [hx22_1, hx22, List.length_cons]
        exact segClone_off_add_succ_mul_104 off (rcs2.length + 1)
      rw [← hsp1] at hx21_1 hx29_1 ⊢
      refine SepWPpX.weaken_pre
        (P' := A.pool ∗
                arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗
                memRegion (s1.sp + 0xf8#64) 104 ∗
                stackAt s1.sp chainCloneStackX ∗
                (chainAt A (g, rc) src ∗ chainAt A (g', rc) (dst_base + off) ∗ F))
        (by exact Entails.of_eq (by ac_rfl)) ?_
      refine ih s1 rc2 g2 gs2 (src + 0x68#64) (off + 0x68#64) _
        hgs2 hmul2_lt hsz2_le hpc1 hrun1 hspA1 hx1_1 hx20_1 hx21_1 hx22_next hx23_1 hx27_1 hx29_1 htr1 hvregs1
        fun s2 gs2' hgs2' henc2' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 => ?_
      rw [hsp1] at hx21_2 hx29_2 ⊢
      refine SepWPpX.weaken_pre ?_
        (hnext s2 (g' :: gs2') (by simp [hgs2']) (by simp [henc_g', henc2'])
          hpc2 hrun2 (hsp2.trans hsp1) hspA2
          (hx19_2.trans hx19_1) hx21_2 (hx25_2.trans hx25_1) (hx26_2.trans hx26_1)
          hx27_2 hx29_2 htr2 hvregs2)
      simp only [List.zip_cons_cons, arrayAt_cons]
      have hd_add : dst_base + off + BitVec.ofNat 64 104 = dst_base + (off + 0x68#64) := by
        bv_arith
      rw [hd_add]
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
