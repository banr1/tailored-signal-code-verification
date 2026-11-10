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
# `SessionStructure::clone` (`0x240f0`): `receiver_chains` and `pending_pre_key`
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
theorem fp_add_neg_104 (sp : BitVec 64) :
    (sp + 0x170#64) + bv% (2 ^ 64 - 104) = sp + 0x108#64 := by bv_omega

@[arm64_norm, wp_norm]
theorem fp_add_neg_24_hex (sp : BitVec 64) :
    (sp + 0x170#64) + 0xffffffffffffffe8#64 = sp + 0x158#64 := by bv_omega

/-- Discharges arithmetic and alignment side conditions for `receiver_chains` and `pending_pre_key`. -/
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

/-! ## `receiver_chains` clone loop (`+0x23c/+0x150..+0x240/+0x1dc`) -/

private theorem sc_receiverChains_copy_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (rem : Nat) (src dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64) (F : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x1a4#64)
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
                 (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x1dc#64
               else
                 (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x188#64) →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x1a4 56
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
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
  apply SepWPp.of_sepWP
    (mid := if !(BitVec.ofNat 64 rem == 0#64) = true then entry + bv% (392) else entry + bv% (476))
  wp_steps
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by rw [← hpc_rem]; sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2))
  exact Entails.of_eq (by ac_rfl)

theorem sc_receiverChains_copy_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (rem : Nat) (src dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64) (F : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x1a4#64)
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
                 (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x1dc#64
               else
                 (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x188#64) →
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
      SepWPp (trTrapProgAt b C abs) ret s1
        (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
      (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_receiverChains_copy_ext_trap rem src dst off sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5
    sw6 dw6 F hpc hrun hsp hx20 hx21 hx23 hx24 hx28 hx29 htr hvregs hrem_lt hnext

theorem sc_receiverChains_copy {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (rem : Nat) (src dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64) (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x1a4#64)
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
                 (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x1dc#64
               else
                 (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x188#64) →
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_receiverChains_copy_ext_trap rem src dst off sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5
    sw6 dw6 F hpc hrun hsp hx20 hx21 hx23 hx24 hx28 hx29 htr hvregs hrem_lt hnext

private theorem sc_receiverChains_iter_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName +
        bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" -
          ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (chainCloneSpec A))
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x188#64)
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
                 (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x1dc#64
               else
                 (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x188#64) →
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
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
          chainAt A (g, rc) src ∗
          chainAt A (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
        chainAt A (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hsub : ∀ (sf : State) (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
      (sw6 dw6 : BitVec 64) (F_copy : SepProp), _ :=
    fun sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy =>
      sc_receiverChains_copy_ext_trap (b := b) (A := A) (ext := ext)
        (x := x) (R := R) (s0 := s0) (s := sf) (ret := ret) (Q := Q)
        rem src (dst_base + off) off sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy
  have hsub_eq : (off + BitVec.ofNat 64 (rem + 1) * 104#64) - off =
      BitVec.ofNat 64 (rem + 1) * 104#64 := by bv_arith
  have hmul_beq : (BitVec.ofNat 64 (rem + 1) * 104#64 == 0#64) = false :=
    segClone_bv_ofNat_mul_104_beq_zero (Nat.succ_pos rem) hmul_lt
  have hrem_lt : rem < 2 ^ 63 := by omega
  clear hmul_lt
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x188 28
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
  wp_steps
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  refine SepWPp.weaken_pre
    (P' := (memRegion (s.sp + 0xf8#64) 104 ∗ chainAt A (g, rc) src ∗ A.pool ∗
              stackAt s.sp chainCloneStack) ∗
            (memRegion (dst_base + off) 104 ∗ F))
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.call_frame (x := ⟨s.sp + 0xf8#64, src, (g, rc)⟩)
      hcall (by sc_close2) (by sc_close2) (by sc_close2)
      (ret_pc := entry + bv% (420)) (by sc_close2)
      rfl ⟨by sc_close2, by sc_close2⟩ rfl
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf _ hm => sc_onPanic_of_callee_panic (by sc_close2) hm)
      fun sf hpcf hrunf hspf hcsm => ?_
  clear hcall
  obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩ := hcsm
  dsimp only [chainCloneSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g' => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hsrk', hpriv', _⟩ => ?_
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
  refine SepWPp.weaken_pre
    (sepConj_mono_left (chainAt_entails_chunks104_6QW A (g', rc) (sf.sp + 0xf8#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun sq0 => SepWPp.exists_elim fun sq1 =>
    SepWPp.exists_elim fun sq2 => SepWPp.exists_elim fun sq3 =>
    SepWPp.exists_elim fun sq4 => SepWPp.exists_elim fun sq5 =>
    SepWPp.exists_elim fun sw6 => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hch_inl => ?_
  refine SepWPp.weaken_pre
    (P' := memRegion (dst_base + off) 104 ∗
            chunks104_6QWAt (sf.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
            stackAt sf.sp chainCloneStack ∗ F)
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.weaken_pre
    (sepConj_mono_left (memRegion_104_entails_chunks104_6QWAt (dst_base + off))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun dq0 => SepWPp.exists_elim fun dq1 =>
    SepWPp.exists_elim fun dq2 => SepWPp.exists_elim fun dq3 =>
    SepWPp.exists_elim fun dq4 => SepWPp.exists_elim fun dq5 =>
    SepWPp.exists_elim fun dw6 => ?_
  refine SepWPp.weaken_pre
    (P' := chunks104_6QWAt (sf.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chunks104_6QWAt (dst_base + off) dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗
            (chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
              stackAt sf.sp chainCloneStack ∗ F))
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine hsub sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 _
    hpcf hrunf hsf_spA hsf20 hsf21 hsf23 hsf24 hsf28 hsf29 hsf_tr hsf_vregs hrem_lt
    fun s1 hpc1 hrun1 hsp1 hspA1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
  clear hsub
  rw [hsf_sp] at hx21_1 hx29_1 ⊢
  refine SepWPp.weaken_pre ?_
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
          chainAt A (g, rc) src ∗ A.pool ∗ stackAt s.sp chainCloneStack ∗ F)
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hdst_chain)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem sc_receiverChains_iter_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok_trap b C A abs)
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x188#64)
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
                 (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x1dc#64
               else
                 (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x188#64) →
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
      SepWPp (trTrapProgAt b C abs) ret s1
        (A.pool ∗
          chainAt A (g, rc) src ∗
          chainAt A (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
      (A.pool ∗
        chainAt A (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (scPanicPost A x R s0) :=
  sc_receiverChains_iter_ext_trap (sc_chainClone_ok_at_trap hcc) x R s0 s ret Q g rc rem
    src dst_base off F hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hmul_lt hnext

theorem sc_receiverChains_iter {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok b C A ctl abs)
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x188#64)
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
                 (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x1dc#64
               else
                 (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x188#64) →
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
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (A.pool ∗
          chainAt A (g, rc) src ∗
          chainAt A (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (A.pool ∗
        chainAt A (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (scPanicPost A x R s0) :=
  sc_receiverChains_iter_ext_trap (sc_chainClone_ok_at hcc) x R s0 s ret Q g rc rem
    src dst_base off F hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hmul_lt hnext

private theorem sc_receiverChains_loop_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hcall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName +
        bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" -
          ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (chainCloneSpec A))
    (x : SessionCloneGhost) (R : SepProp) (s0 : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop) (dst_base : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length → (rcs_tl.length + 1) * 104 < 2 ^ 63 → (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x188#64 →
      s.status = .Running → s.spAligned = true → s.readReg64 .x1 = src → s.readReg64 .x20 = off →
      s.readReg64 .x21 = s.sp + 0xf8#64 → s.readReg64 .x22 = off + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 →
      s.readReg64 .x23 = BitVec.ofNat 64 (rcs_tl.length + 1) → s.readReg64 .x27 = dst_base →
      s.readReg64 .x29 = s.sp + 0x170#64 → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (s1 : State) (gs' : List ChainGhost),
        gs'.length = (rc :: rcs_tl).length →
        ((gs'.zip (rc :: rcs_tl)).map fun gc => lenField 7 (encChainMem gc)) =
          (((g :: gs_tl).zip (rc :: rcs_tl)).map fun gc => lenField 7 (encChainMem gc)) →
        s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x1dc#64 →
        s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x21 = s.sp + 0xf8#64 →
        s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = dst_base → s1.readReg64 .x29 = s.sp + 0x170#64 →
        s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
        SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
          (A.pool ∗ arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0xf8#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
          Q (scPanicPost A x R s0)) →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
        (A.pool ∗ arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0) := by
  induction rcs_tl with
  | nil =>
    intro s rc g gs_tl src off F hgs hmul_lt _ hpc hrun hsp hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hnext
    cases gs_tl with
    | cons _ _ => simp at hgs
    | nil =>
      simp only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil,
        sepConj_emp, List.length_nil, Nat.zero_add, Nat.one_mul] at *
      refine sc_receiverChains_iter_ext_trap hcall x R s0 s ret Q g rc 0 src dst_base off F
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
      refine SepWPp.weaken_pre
        (P' := A.pool ∗
                chainAt A (g, rc) src ∗
                memRegion (dst_base + off) 104 ∗
                memRegion (s.sp + 0xf8#64) 104 ∗
                stackAt s.sp chainCloneStack ∗
                (arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                  memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗ F))
        (by exact Entails.of_eq (by ac_rfl)) ?_
      refine sc_receiverChains_iter_ext_trap hcall x R s0 s ret Q g rc (rcs2.length + 1)
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
      refine SepWPp.weaken_pre
        (P' := A.pool ∗
                arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗
                memRegion (s1.sp + 0xf8#64) 104 ∗
                stackAt s1.sp chainCloneStack ∗
                (chainAt A (g, rc) src ∗ chainAt A (g', rc) (dst_base + off) ∗ F))
        (by exact Entails.of_eq (by ac_rfl)) ?_
      refine ih s1 rc2 g2 gs2 (src + 0x68#64) (off + 0x68#64) _
        hgs2 hmul2_lt hsz2_le hpc1 hrun1 hspA1 hx1_1 hx20_1 hx21_1 hx22_next hx23_1 hx27_1 hx29_1 htr1 hvregs1
        fun s2 gs2' hgs2' henc2' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 => ?_
      rw [hsp1] at hx21_2 hx29_2 ⊢
      refine SepWPp.weaken_pre ?_
        (hnext s2 (g' :: gs2') (by simp [hgs2']) (by simp [henc_g', henc2'])
          hpc2 hrun2 (hsp2.trans hsp1) hspA2
          (hx19_2.trans hx19_1) hx21_2 (hx25_2.trans hx25_1) (hx26_2.trans hx26_1)
          hx27_2 hx29_2 htr2 hvregs2)
      simp only [List.zip_cons_cons, arrayAt_cons]
      have hd_add : dst_base + off + BitVec.ofNat 64 104 = dst_base + (off + 0x68#64) := by
        bv_arith
      rw [hd_add]
      exact Entails.of_eq (by ac_rfl)

theorem sc_receiverChains_loop_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok_trap b C A abs)
    (x : SessionCloneGhost) (R : SepProp) (s0 : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (dst_base : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length →
      (rcs_tl.length + 1) * 104 < 2 ^ 63 →
      (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x188#64 →
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
        s1.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x1dc#64 →
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
        SepWPp (trTrapProgAt b C abs) ret s1
          (A.pool ∗
            arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0xf8#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            F)
          Q (scPanicPost A x R s0)) →
      SepWPp (trTrapProgAt b C abs) ret s
        (A.pool ∗
          arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0) :=
  sc_receiverChains_loop_ext_trap (sc_chainClone_ok_at_trap hcc) x R s0 ret Q dst_base rcs_tl

theorem sc_receiverChains_loop {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hcc : ChainCloneLocal1Ok b C A ctl abs)
    (x : SessionCloneGhost) (R : SepProp) (s0 : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (dst_base : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length →
      (rcs_tl.length + 1) * 104 < 2 ^ 63 →
      (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x188#64 →
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
        s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x1dc#64 →
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
        SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
          (A.pool ∗
            arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0xf8#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            F)
          Q (scPanicPost A x R s0)) →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s
        (A.pool ∗
          arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0) :=
  sc_receiverChains_loop_ext_trap (sc_chainClone_ok_at hcc) x R s0 ret Q dst_base rcs_tl

private theorem sc_receiverChains_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hkit : ScExternKit_trap b A ext)
    (hcall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics ext))
      ((libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName +
        bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#1]" -
          ls_off% "<libsignal_protocol::proto::storage::SessionStructure as core::clone::Clone>::clone"))
      (chainCloneSpec A))
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (F : SepProp)
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x23c#64
                   else
                     (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x150#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.s.state.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length →
      ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
        ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) →
      s1.pc = (if x.s.state.receiverChains = [] then
                 (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x240#64
               else
                 (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x1dc#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = chainsCap' →
      s1.readReg64 .x27 = chainsPtr' →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
          ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
        ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hshim := hkit.shim
  have halloc := hkit.alloc
  have hpanic := sc_panic_0x498_ext_trap (A := A) hkit.panic_err (ret := ret) (Q := Q) x s0
  clear hkit
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x150 56
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x23c 4
  clear hfn
  cases hrc_eq : x.s.state.receiverChains with
  | nil =>
    clear hshim halloc hpanic hcall
    simp only [hrc_eq, ↓reduceIte, List.length_nil] at hpc hx26 hchains_len ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (576))
    wp_steps
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ 0#64 8#64 [] (by simp [hrc_eq]) (by simp [hrc_eq]) (by simp [hrc_eq])
        (by simp only [hrc_eq, ↓reduceIte]; sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2))
    simp only [hrc_eq, List.zip_nil_right, segClone_vecBuf_chain_nil_eq]
    exact Entails.of_eq (by ac_rfl)
  | cons rc rcs_tl =>
    have hsub := sc_receiverChains_loop_ext_trap hcall x R s0 ret Q
    clear hcall
    have hne : x.s.state.receiverChains ≠ [] := by simp [hrc_eq]
    simp only [hne, ↓reduceIte] at hpc hnext
    rw [hrc_eq] at hx26
    cases hgs_eq : x.G.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hgs_tl : gs_tl.length = rcs_tl.length := by
        rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hexpose :=
        segClone_vecBuf_expose_arrayAt A (stride := 104) 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
          ((g :: gs_tl).zip (rc :: rcs_tl))
      refine SepWPp.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (hexpose _))) ?_
      refine sepWPp_pure_3rd fun hmul_lt => ?_
      have hzip_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs_tl]
      rw [hzip_len] at hmul_lt
      have hpos : 0 < (rc :: rcs_tl).length := by simp
      have hpos_mul : 0 < (rc :: rcs_tl).length * 104 := by simp [List.length_cons]
      have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by simp [List.length_cons] at hmul_lt; omega
      have hsz_le63 : (rc :: rcs_tl).length * 104 + 8 ≤ 2 ^ 63 := by
        simp [List.length_cons] at hmul_lt ⊢; omega
      have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat =
          (rc :: rcs_tl).length * 104 :=
        segClone_bv_ofNat_mul_104_toNat hmul_lt
      have hpow2 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      have hlay : LayoutOk ((rc :: rcs_tl).length * 104) 8 :=
        ⟨hpos_mul, hpow2, hsz_le63⟩
      rw [stackAt_chainClone_eq_alloc s.sp]
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (364))
      wp_steps
      wp_call hshim ()
      clear hshim
      wp_steps
      wp_call halloc ((rc :: rcs_tl).length * 104, 8)
      clear halloc
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
      · clear hsub hnext
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPp_pure_3rd fun htrace => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (1176))
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        exact hpanic _ _ R (by sc_close2) (by sc_close2) (by sc_close2)
      · clear hpanic
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (392))
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        have hsf_sp : sf.sp = s.sp := by sc_close2
        have hsf1_sp : sf_1.sp = s.sp := by sc_close2
        set ptr' := sf_1.readReg64 (Reg.gpr 0#5)
        have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
        have hsz_eq : (rc :: rcs_tl).length * 104 = (rcs_tl.length + 1) * 104 := rfl
        refine SepWPp.weaken_pre
          (P' := A.pool ∗
                  arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                  memRegion (sf_1.sp + 0xf8#64) 104 ∗
                  stackAt sf_1.sp chainCloneStack ∗
                  (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                    ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
                    segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr
                      ((g :: gs_tl).zip (rc :: rcs_tl)) ∗ F))
          (by rw [hsf1_sp, hsf_sp, hptr_zero, ← hsz_eq, stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl)) ?_
        refine hsub ptr' rcs_tl _
          rc g gs_tl x.G.chainsPtr 0#64 _
          hgs_tl (by simpa [List.length_cons] using hmul_lt) hsz_le
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2)
          (by sc_close2)
          (by sc_close2) (by sc_close2)
          (by dsimp only [ptr']; sc_close2)
          (by sc_close2)
          (by sc_close2)
          (by sc_close2)
          fun s2 gs' hgs' henc' hpc2 hrun2 hsp2 hspA2 hx19_2 hx21_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 => ?_
        clear hsub
        dsimp only [Reg.x19, Reg.x25, Reg.x26] at hx19_2 hx25_2 hx26_2
        simp (config := { decide := true }) only [State.sp_setPC, State.sp_writeReg64_gpr,
          State.readReg64_setPC, State.readReg64_writeReg64, reduceStateReadReg64] at hsp2 hx19_2 hx21_2 hx25_2 hx26_2 hx29_2
        rw [hsf1_sp] at hsp2 hx21_2 hx29_2
        rw [hptr_zero]
        refine SepWPp.weaken_pre ?_
          (hnext s2 (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' gs'
            (by rw [hrc_eq]; exact hgs') (by rw [hrc_eq])
            (by rw [hgs_eq, hrc_eq]; exact henc')
            hpc2 hrun2 (by sc_close2) hspA2
            (by sc_close2) hx21_2 (by sc_close2)
            (by sc_close2) hx27_2 hx29_2 htr2 hvregs2)
        dsimp only [State.setPC, State.setPState, State.writeReg64]
        simp only [hgs_eq, hrc_eq, hsf1_sp]
        have hreasm :=
          segClone_vecBuf_reassemble_arrayAt A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
            ((g :: gs_tl).zip (rc :: rcs_tl))
        have hnew_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
          simp [hgs']
        have hnew_pos : 0 < (gs'.zip (rc :: rcs_tl)).length := by rw [hnew_len]; exact hpos
        have hnew_lt : (gs'.zip (rc :: rcs_tl)).length * 104 < 2 ^ 63 := by rw [hnew_len]; exact hmul_lt
        have hnew_buf := segClone_vecBuf_chain_of_arrayAt A ptr' (gs'.zip (rc :: rcs_tl)) hnew_pos hnew_lt hoom64
        rw [hnew_len] at hnew_buf
        refine Entails.trans
          (Q := (arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
                (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                  arrayAt (chainAt A) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
                A.pool ∗ ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
                memRegion (s.sp + 0xf8#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
          (Entails.of_eq (by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hreasm (sepConj_mono_left hnew_buf)) ?_
        exact Entails.of_eq (by ac_rfl)

theorem sc_receiverChains_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (hcc : ChainCloneLocal1Ok_trap b C A abs)
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (F : SepProp)
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x23c#64
                   else
                     (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x150#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.s.state.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length →
      ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
        ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) →
      s1.pc = (if x.s.state.receiverChains = [] then
                 (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x240#64
               else
                 (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x1dc#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = chainsCap' →
      s1.readReg64 .x27 = chainsPtr' →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (trTrapProgAt b C abs) ret s1
        (A.pool ∗
          ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
      (A.pool ∗
        ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (scPanicPost A x R s0) :=
  sc_receiverChains_ext_trap (scExternKit_trap hA) (sc_chainClone_ok_at_trap hcc)
    x R s0 s ret Q F hpc hrun hsp hx21 hx25 hx26 hx29 htr hvregs hchains_len hnext

/-- Allocates and clones the `receiver_chains` array (`+0x23c/+0x150..+0x240/+0x1dc`). -/
theorem sc_receiverChains {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    (hcc : ChainCloneLocal1Ok b C A ctl abs)
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (F : SepProp)
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x23c#64
                   else
                     (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x150#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.s.state.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length →
      ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
        ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) →
      s1.pc = (if x.s.state.receiverChains = [] then
                 (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x240#64
               else
                 (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x1dc#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = chainsCap' →
      s1.readReg64 .x27 = chainsPtr' →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (A.pool ∗
          ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (A.pool ∗
        ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (scPanicPost A x R s0) :=
  sc_receiverChains_ext_trap (scExternKit_kit_trap hA) (sc_chainClone_ok_at hcc)
    x R s0 s ret Q F hpc hrun hsp hx21 hx25 hx26 hx29 htr hvregs hchains_len hnext

/-! ## `pending_pre_key` (`+0x240/+0x1dc..+0x250/+0x288`) -/

private theorem sc_pendingPreKey_200_pos_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hkit : ScExternKit_trap b A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 : BitVec 64}
    {v18 v20 : BitVec 64} {F : SepProp}
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4)))
    (htail_val : gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4)
    (hpos : 0 < gp.vec.bytes.length)
    (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63)
    (hptr : gp.vec.ptr ≠ 0)
    (hpc : s.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x200#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx23 : (s.readReg64 .x23).truncate 32 = tw0)
    (hx24 : (s.readReg64 .x24).truncate 32 = tw1)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x250#64 ∨
       s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x288#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' → s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' → s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗
          (⌜gp.tail.length = 48 - 24⌝ ∗
            vecGhostAt A gp.vec (x.src + 0xf8#64) ∗
            ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
              ∃ tw4' : BitVec 32,
                gp.tail = unpack32 w23' ++ unpack32 w24' ++ unpack64 v18' ++ unpack32 v2c' ++ unpack32 tw4'⌝ ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗ ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗ stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗
        ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗ ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
        ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗ (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
          (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗ ((s.sp + 0x2c#64) ↦₃₂ tw3) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  have hshim := hkit.shim
  have halloc := hkit.alloc
  have hmemcpy := hkit.memcpy
  have hpanic := sc_panic_0x4b0_ext_trap (A := A) hkit.panic_err (ret := ret) (Q := Q) x s0
  clear hkit
  have h100 : x.src + 0xf8#64 + 8#64 = x.src + 0x100#64 := by bv_arith
  have h108 : x.src + 0xf8#64 + 16#64 = x.src + 0x108#64 := by bv_arith
  have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gp.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk gp.vec.bytes.length 1 := ⟨hpos, hpow2, hlen_le63⟩
  have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x200 44
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x280 8
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (532))
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (gp.vec.bytes.length, 1)
  clear halloc
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1200))
    wp_steps
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    exact hpanic _ _ R (by sc_close2) (by sc_close2) (by sc_close2)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (648))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gp.vec.ptr, gp.vec.bytes)
    clear hmemcpy
    wp_steps
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    have hsp_eq : sf.sp = s.sp := by sc_close2
    have hsf1_sp : sf_1.sp = s.sp := by sc_close2
    refine SepWPp.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gp.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) td2 tw0 tw1 tw3
        (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2))
    have h_rfl : (⌜BitVec.ofNat 64 gp.vec.bytes.length = BitVec.ofNat 64 gp.vec.bytes.length ∧
        ∃ tw4' : BitVec 32,
          gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4'⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨rfl, tw4, htail_val⟩
    have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
      segClone_pure_eq_emp htail
    have h_pure2 : (⌜gp.vec.bytes.length ≤ gp.vec.cap.toNat ∧ gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_pos A gp.vec (x.src + 0xf8#64) hpos, h100, h108,
        htail_eq,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) gp.vec.bytes hpos hlen_lt hoom64,
        h_rfl, h_pure1, h_pure2]
    simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

theorem sc_pendingPreKey_200_pos_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 : BitVec 64}
    {v18 v20 : BitVec 64} {F : SepProp}
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4)))
    (htail_val : gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4)
    (hpos : 0 < gp.vec.bytes.length)
    (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63)
    (hptr : gp.vec.ptr ≠ 0)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x200#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx23 : (s.readReg64 .x23).truncate 32 = tw0)
    (hx24 : (s.readReg64 .x24).truncate 32 = tw1)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x250#64 ∨
       s1.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x288#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (trTrapProgAt b C abs) ret s1
        (A.pool ∗
          (⌜gp.tail.length = 48 - 24⌝ ∗
            vecGhostAt A gp.vec (x.src + 0xf8#64) ∗
            ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
              ∃ tw4' : BitVec 32,
                gp.tail = unpack32 w23' ++ unpack32 w24' ++ unpack64 v18' ++ unpack32 v2c' ++ unpack32 tw4'⌝ ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗
          ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
      (A.pool ∗
        ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗
        ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
        ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
        (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
          (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((x.src + 0x110#64) ↦₃₂ tw0) ∗
        ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗
        ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ tw3) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_pendingPreKey_200_pos_ext_trap (scExternKit_trap hA)
    htail htail_eq htail_val hpos hlen_le hcap_lt hptr
    hpc hrun hsp hx23 hx24 hx25 hx28 htr hvregs hnext

theorem sc_pendingPreKey_200_pos {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 : BitVec 64}
    {v18 v20 : BitVec 64} {F : SepProp}
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4)))
    (htail_val : gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4)
    (hpos : 0 < gp.vec.bytes.length)
    (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63)
    (hptr : gp.vec.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x200#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx23 : (s.readReg64 .x23).truncate 32 = tw0)
    (hx24 : (s.readReg64 .x24).truncate 32 = tw1)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x250#64 ∨
       s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x288#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (A.pool ∗
          (⌜gp.tail.length = 48 - 24⌝ ∗
            vecGhostAt A gp.vec (x.src + 0xf8#64) ∗
            ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
              ∃ tw4' : BitVec 32,
                gp.tail = unpack32 w23' ++ unpack32 w24' ++ unpack64 v18' ++ unpack32 v2c' ++ unpack32 tw4'⌝ ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗
          ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (A.pool ∗
        ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗
        ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
        ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
        (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
          (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((x.src + 0x110#64) ↦₃₂ tw0) ∗
        ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗
        ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4) ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ tw3) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) :=
  sc_pendingPreKey_200_pos_ext_trap (scExternKit_kit_trap hA)
    htail htail_eq htail_val hpos hlen_le hcap_lt hptr
    hpc hrun hsp hx23 hx24 hx25 hx28 htr hvregs hnext

private theorem sc_pendingPreKey_ext_trap {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hkit : ScExternKit_trap b A ext)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v18 v20 : BitVec 64} {v2c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x240#64
                   else
                     (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x1dc#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x250#64 ∨
       s1.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr sessionCloneName + 0x288#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' → s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' → s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s1
        (A.pool ∗ optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
          ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗ ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗ stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (libsignalSessionCode.rebase b (Rust.withPanics ext)) ret s
      (A.pool ∗ optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hfn := libsignalSessionCode_fnOff_sym_240f0
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x1dc 36
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x240 16
  sessionClone_fetches b (Rust.withPanics ext) hfn 0x278 16
  clear hfn
  cases hpend : x.G.pending with
  | none =>
    clear hkit
    rw [hpend] at hnext
    dsimp only [optTailVecAt, ScOptPendClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    by_cases hrc : x.s.state.receiverChains = []
    · simp only [hrc, ↓reduceIte] at hpc
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (592))
      wp_steps
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v20 v18
          ((s.readReg64 .x23).truncate 32) ((s.readReg64 .x24).truncate 32) v2c
          (Or.inl (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · simp only [hrc, ↓reduceIte] at hpc
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (592))
      wp_steps
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v20 v18
          ((s.readReg64 .x23).truncate 32) ((s.readReg64 .x24).truncate 32) v2c
          (Or.inl (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  | some gp =>
    rw [hpend] at hnext
    dsimp only [optTailVecAt, ScOptPendClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, htail_val, htail_pts⟩ := exists_tail24_decomp htail
    have h100 : x.src + 0xf8#64 + 8#64 = x.src + 0x100#64 := by bv_arith
    have h108 : x.src + 0xf8#64 + 16#64 = x.src + 0x108#64 := by bv_arith
    have h110 : x.src + 0xf8#64 + BitVec.ofNat 64 24 = x.src + 0x110#64 := by bv_arith
    have h114 : x.src + 0x110#64 + 4#64 = x.src + 0x114#64 := by bv_arith
    have h118 : x.src + 0x110#64 + 8#64 = x.src + 0x118#64 := by bv_arith
    have h120 : x.src + 0x110#64 + 16#64 = x.src + 0x120#64 := by bv_arith
    have h124 : x.src + 0x110#64 + 20#64 = x.src + 0x124#64 := by bv_arith
    have htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
        (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
          ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
          ((x.src + 0x124#64) ↦₃₂ tw4)) := by
      rw [h110, htail_pts (x.src + 0x110#64), h114, h118, h120, h124]
    rw [htail_eq]
    rcases eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · clear hkit
      rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length ∧
          ∃ tw4' : BitVec 32,
            gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4'⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨rfl, tw4, htail_val⟩
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      by_cases hrc : x.s.state.receiverChains = []
      · simp only [hrc, ↓reduceIte] at hpc
        generalize_entry (libsignalSessionCode.rebase b
          (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
        generalize_entry (libsignalSessionCode.rebase b
          (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
        examples_hide_fetches
        apply SepWPp.of_sepWP (mid := entry + bv% (648))
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw0 tw1 tw3
            (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2))
        rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108,
            htail_eq, hnil, vecU8Buf_nil_eq A, h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
      · simp only [hrc, ↓reduceIte] at hpc
        generalize_entry (libsignalSessionCode.rebase b
          (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
        generalize_entry (libsignalSessionCode.rebase b
          (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
        examples_hide_fetches
        apply SepWPp.of_sepWP (mid := entry + bv% (648))
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw0 tw1 tw3
            (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2))
        rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108,
            htail_eq, hnil, vecU8Buf_nil_eq A, h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gp.vec (x.src + 0xf8#64) hpos, h100, h108]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hsub := fun (s_200 : State) =>
        sc_pendingPreKey_200_pos_ext_trap hkit (x := x) (R := R) (s0 := s0) (s := s_200) (ret := ret) (Q := Q)
          (gp := gp) (tw0 := tw0) (tw1 := tw1) (tw3 := tw3) (tw4 := tw4) (td2 := td2)
          (v18 := v18) (v20 := v20) (F := F)
          htail htail_eq htail_val hpos hlen_le hcap_lt hptr
      clear hkit
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)).fnAddr sessionCloneName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase b
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      suffices h_at_200 : ∀ s_200 : State,
          s_200.pc = entry + bv% (512) →
          s_200.status = .Running →
          s_200.sp = s.sp →
          s_200.spAligned = true →
          s_200.readReg64 .x19 = s.readReg64 .x19 →
          (s_200.readReg64 .x23).truncate 32 = tw0 →
          (s_200.readReg64 .x24).truncate 32 = tw1 →
          s_200.readReg64 .x25 = x.src →
          s_200.readReg64 .x26 = s.readReg64 .x26 →
          s_200.readReg64 .x27 = s.readReg64 .x27 →
          s_200.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length →
          s_200.readReg64 .x29 = s.readReg64 .x29 →
          s_200.trace = s0.trace →
          calleeSavedVRegs s_200 = calleeSavedVRegs s0 →
          SepWPp prog ret s_200
            (A.pool ∗
              ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗
              ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
              ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
              (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
              A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
              memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
                (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
              ((x.src + 0x110#64) ↦₃₂ tw0) ∗
              ((x.src + 0x114#64) ↦₃₂ tw1) ∗
              ((x.src + 0x118#64) ↦₆₄ td2) ∗
              ((x.src + 0x120#64) ↦₃₂ tw3) ∗
              ((x.src + 0x124#64) ↦₃₂ tw4) ∗
              ((s_200.sp + 0x18#64) ↦₆₄ v18) ∗
              ((s_200.sp + 0x20#64) ↦₆₄ v20) ∗
              ((s_200.sp + 0x2c#64) ↦₃₂ tw3) ∗
              stackAt s_200.sp allocHookStack ∗ F)
            Q (scPanicPost A x R s0) by
        clear hsub
        by_cases hrc : x.s.state.receiverChains = []
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPp.of_sepWP (mid := entry + bv% (512))
          wp_steps
          refine SepWP.done (by sc_close2) (by sc_close2) ?_
          exact h_at_200 _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPp.of_sepWP (mid := entry + bv% (512))
          wp_steps
          refine SepWP.done (by sc_close2) (by sc_close2) ?_
          exact h_at_200 _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      intro s_200 hpc200 hrun200 hsp200 hspA200 hx19_200 hx23_200 hx24_200 hx25_200 hx26_200 hx27_200 hx28_200 hx29_200 htr200 hvregs200
      refine hsub s_200 hpc200 hrun200 hspA200 hx23_200 hx24_200 hx25_200 hx28_200 htr200 hvregs200
        fun s1 pendCap' pendPtr' v18' w23' w24' v2c' hpc1 hrun1 hsp1 hspA1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 => ?_
      clear hsub
      rw [hsp200]
      exact hnext s1 pendCap' pendPtr' v18' w23' w24' v2c'
        hpc1 hrun1 (hsp1.trans hsp200) hspA1
        (hx19_1.trans hx19_200) hx23_1 hx24_1 hx25_1
        (hx26_1.trans hx26_200) (hx27_1.trans hx27_200) hx28_1 (hx29_1.trans hx29_200) htr1 hvregs1

theorem sc_pendingPreKey_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v18 v20 : BitVec 64} {v2c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x240#64
                   else
                     (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x1dc#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x250#64 ∨
       s1.pc = (trTrapProgAt b C abs).fnAddr sessionCloneName + 0x288#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (trTrapProgAt b C abs) ret s1
        (A.pool ∗
          optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
          ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗
          ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (trTrapProgAt b C abs) ret s
      (A.pool ∗
        optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗
        F)
      Q (scPanicPost A x R s0) :=
  sc_pendingPreKey_ext_trap (scExternKit_trap hA) hpc hrun hsp hx25 htr hvregs hnext

/-- Clones `pending_pre_key` into registers and stack spill slots (`+0x240/+0x1dc..+0x250/+0x288`). -/
theorem sc_pendingPreKey {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v18 v20 : BitVec 64} {v2c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x240#64
                   else
                     (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x1dc#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x250#64 ∨
       s1.pc = (tripleRatchetProgAt b C ctl abs).fnAddr sessionCloneName + 0x288#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret s1
        (A.pool ∗
          optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
          ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗
          ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (A.pool ∗
        optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗
        F)
      Q (scPanicPost A x R s0) :=
  sc_pendingPreKey_ext_trap (scExternKit_kit_trap hA) hpc hrun hsp hx25 htr hvregs hnext

/-! ## Relocatable `[LibsignalPlacement]` proofs (block `80`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed
open CryptoVerification.LibsignalTripleRatchet.ChainCloneLocal1 (ChainCloneLocal1PlacedOk)

theorem sc_receiverChains_copy_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    (rem : Nat) (src dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64) (F : SepProp)
    (hpc : s.pc = (blkPl_80).base + 0x1a4#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
                 (blkPl_80).base + 0x1dc#64
               else
                 (blkPl_80).base + 0x188#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      LibsignalCodeLoaded lsmpl s1.mem →
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
      SepWPp (lsProg_80 H) ret s1
        (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
      (chunks104_6QWAt (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗ F)
      Q (scPanicPost A x R s0) := by
  have hpc_rem :
      (if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_80).base + 392#64 else (blkPl_80).base + 476#64) =
      (if rem = 0 then (blkPl_80).base + 476#64 else (blkPl_80).base + 392#64) := by
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
  apply sepWPp_of_sepWP_lscl_sc hcl
    (mid := if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_80).base + 392#64 else (blkPl_80).base + 476#64)
  wp_steps
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  intro hcl1
  refine SepWPp.weaken_pre ?_
    (hnext _
      (by rw [← hpc_rem]; sc_close2) (by sc_close2) (by sc_close2) (by sc_close2) hcl1
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2))
  exact Entails.of_eq (by ac_rfl)

theorem sc_receiverChains_iter_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (src dst_base off : BitVec 64)
    (F : SepProp)
    (hpc : s.pc = (blkPl_80).base + 0x188#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
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
                 (blkPl_80).base + 0x1dc#64
               else
                 (blkPl_80).base + 0x188#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      LibsignalCodeLoaded lsmpl s1.mem →
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
      SepWPp (lsProg_80 H) ret s1
        (A.pool ∗
          chainAt A (g, rc) src ∗
          chainAt A (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
      (A.pool ∗
        chainAt A (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (scPanicPost A x R s0) := by
  have hsub : ∀ (sf : State) (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
      (sw6 dw6 : BitVec 64) (F_copy : SepProp), _ :=
    fun sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy =>
      sc_receiverChains_copy_placed (A := A) (H := H)
        (x := x) (R := R) (s0 := s0) (s := sf) (ret := ret) (Q := Q)
        rem src (dst_base + off) off sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 F_copy
  have hsub_eq : (off + BitVec.ofNat 64 (rem + 1) * 104#64) - off =
      BitVec.ofNat 64 (rem + 1) * 104#64 := by bv_arith
  have hmul_beq : (BitVec.ofNat 64 (rem + 1) * 104#64 == 0#64) = false :=
    segClone_bv_ofNat_mul_104_beq_zero (Nat.succ_pos rem) hmul_lt
  have hrem_lt : rem < 2 ^ 63 := by omega
  clear hmul_lt
  apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_82).base)
  wp_steps
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  intro hcl1
  refine SepWPp.weaken_pre
    (P' := (memRegion (s.sp + 0xf8#64) 104 ∗ chainAt A (g, rc) src ∗ A.pool ∗
              stackAt s.sp chainCloneStack) ∗
            (memRegion (dst_base + off) 104 ∗ F))
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine sepWPp_call_frame_lscl_sc (x := ⟨s.sp + 0xf8#64, src, (g, rc)⟩)
      hcall hcl1 (by sc_close2) (by sc_close2) (by sc_close2)
      (ret_pc := (blkPl_80).base + 420#64) (by sc_close2)
      rfl ⟨by sc_close2, by sc_close2⟩ rfl
      (fun _ _ _ _ h => allowPanic_not_exited h)
      (fun sf _ hm => sc_onPanic_of_callee_panic (by sc_close2) hm)
      fun sf hpcf hrunf hspf hcsm hclf => ?_
  clear hcall
  obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩ := hcsm
  dsimp only [chainCloneSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g' => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hsrk', hpriv', _⟩ => ?_
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
  refine SepWPp.weaken_pre
    (sepConj_mono_left (chainAt_entails_chunks104_6QW A (g', rc) (sf.sp + 0xf8#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun sq0 => SepWPp.exists_elim fun sq1 =>
    SepWPp.exists_elim fun sq2 => SepWPp.exists_elim fun sq3 =>
    SepWPp.exists_elim fun sq4 => SepWPp.exists_elim fun sq5 =>
    SepWPp.exists_elim fun sw6 => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hch_inl => ?_
  refine SepWPp.weaken_pre
    (P' := memRegion (dst_base + off) 104 ∗
            chunks104_6QWAt (sf.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
            stackAt sf.sp chainCloneStack ∗ F)
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.weaken_pre
    (sepConj_mono_left (memRegion_104_entails_chunks104_6QWAt (dst_base + off))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun dq0 => SepWPp.exists_elim fun dq1 =>
    SepWPp.exists_elim fun dq2 => SepWPp.exists_elim fun dq3 =>
    SepWPp.exists_elim fun dq4 => SepWPp.exists_elim fun dq5 =>
    SepWPp.exists_elim fun dw6 => ?_
  refine SepWPp.weaken_pre
    (P' := chunks104_6QWAt (sf.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chunks104_6QWAt (dst_base + off) dq0 dq1 dq2 dq3 dq4 dq5 dw6 ∗
            (chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
              stackAt sf.sp chainCloneStack ∗ F))
    (by exact Entails.of_eq (by ac_rfl)) ?_
  refine hsub sf sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6 _
    hpcf hrunf hsf_spA hclf hsf20 hsf21 hsf23 hsf24 hsf28 hsf29 hsf_tr hsf_vregs hrem_lt
    fun s1 hpc1 hrun1 hsp1 hspA1 hcl_1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
  clear hsub
  rw [hsf_sp] at hx21_1 hx29_1 ⊢
  refine SepWPp.weaken_pre ?_
    (hnext s1 g' henc_g'
      hpc1 hrun1 (hsp1.trans hsf_sp) hspA1 hcl_1
      hx1_1 (hx19_1.trans hsf19) hx20_1 hx21_1 (hx22_1.trans hsf22)
      hx23_1 (hx25_1.trans hsf25) (hx26_1.trans hsf26) (hx27_1.trans hsf27)
      hx29_1 htr1 hvregs1)
  have h104 := chunks104_6QWAt_entails_memRegion (s.sp + 0xf8#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6
  have hdst_chain := chainAt_of_chunks104_6QW A (g', rc) (dst_base + off) hch_inl
  refine Entails.trans (sepConj_mono_left h104) ?_
  refine Entails.trans
    (Q := memRegion (s.sp + 0xf8#64) 104 ∗
          (chunks104_6QWAt (dst_base + off) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ chainHeap A (g', rc)) ∗
          chainAt A (g, rc) src ∗ A.pool ∗ stackAt s.sp chainCloneStack ∗ F)
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hdst_chain)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem sc_receiverChains_loop_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hcall : subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    (x : SessionCloneGhost) (R : SepProp) (s0 : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop) (dst_base : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length → (rcs_tl.length + 1) * 104 < 2 ^ 63 → (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      s.pc = (blkPl_80).base + 0x188#64 →
      s.status = .Running → s.spAligned = true → LibsignalCodeLoaded lsmpl s.mem →
      s.readReg64 .x1 = src → s.readReg64 .x20 = off →
      s.readReg64 .x21 = s.sp + 0xf8#64 → s.readReg64 .x22 = off + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 →
      s.readReg64 .x23 = BitVec.ofNat 64 (rcs_tl.length + 1) → s.readReg64 .x27 = dst_base →
      s.readReg64 .x29 = s.sp + 0x170#64 → s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (s1 : State) (gs' : List ChainGhost),
        gs'.length = (rc :: rcs_tl).length →
        ((gs'.zip (rc :: rcs_tl)).map fun gc => lenField 7 (encChainMem gc)) =
          (((g :: gs_tl).zip (rc :: rcs_tl)).map fun gc => lenField 7 (encChainMem gc)) →
        s1.pc = (blkPl_80).base + 0x1dc#64 →
        s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
        LibsignalCodeLoaded lsmpl s1.mem →
        s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x21 = s.sp + 0xf8#64 →
        s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = dst_base → s1.readReg64 .x29 = s.sp + 0x170#64 →
        s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
        SepWPp (lsProg_80 H) ret s1
          (A.pool ∗ arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0xf8#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
          Q (scPanicPost A x R s0)) →
      SepWPp (lsProg_80 H) ret s
        (A.pool ∗ arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
        Q (scPanicPost A x R s0) := by
  induction rcs_tl with
  | nil =>
    intro s rc g gs_tl src off F hgs hmul_lt _ hpc hrun hsp hcl hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hnext
    cases gs_tl with
    | cons _ _ => simp at hgs
    | nil =>
      simp only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil,
        sepConj_emp, List.length_nil, Nat.zero_add, Nat.one_mul] at *
      refine sc_receiverChains_iter_placed hcall x R s0 s ret Q g rc 0 src dst_base off F
        hpc hrun hsp hcl hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hmul_lt
        fun s1 g' henc_g' hpc1 hrun1 hsp1 hspA1 hcl1 _ hx19_1 _ hx21_1 _ _ hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
      simp only [↓reduceIte] at hpc1
      have h1 := hnext s1 [g'] rfl (by simp [henc_g']) hpc1 hrun1 hsp1 hspA1 hcl1
        hx19_1 hx21_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1
      simpa only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil, sepConj_emp]
        using h1
  | cons rc2 rcs2 ih =>
    intro s rc g gs_tl src off F hgs hmul_lt hsz_le hpc hrun hsp hcl hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hnext
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
      refine SepWPp.weaken_pre
        (P' := A.pool ∗
                chainAt A (g, rc) src ∗
                memRegion (dst_base + off) 104 ∗
                memRegion (s.sp + 0xf8#64) 104 ∗
                stackAt s.sp chainCloneStack ∗
                (arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                  memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗ F))
        (by exact Entails.of_eq (by ac_rfl)) ?_
      refine sc_receiverChains_iter_placed hcall x R s0 s ret Q g rc (rcs2.length + 1)
        src dst_base off _
        hpc hrun hsp hcl hx1 hx20 hx21 hx22 hx23 hx27 hx29 htr hvregs hmul_lt
        fun s1 g' henc_g' hpc1 hrun1 hsp1 hspA1 hcl1 hx1_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx25_1 hx26_1 hx27_1 hx29_1 htr1 hvregs1 => ?_
      have hne0 : rcs2.length + 1 ≠ 0 := Nat.succ_ne_zero _
      simp only [hne0, ↓reduceIte] at hpc1
      have hx22_next : s1.readReg64 .x22 =
          (off + 0x68#64) + BitVec.ofNat 64 (rcs2.length + 1) * 104#64 := by
        rw [hx22_1, hx22, List.length_cons]
        exact segClone_off_add_succ_mul_104 off (rcs2.length + 1)
      rw [← hsp1] at hx21_1 hx29_1 ⊢
      refine SepWPp.weaken_pre
        (P' := A.pool ∗
                arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗
                memRegion (s1.sp + 0xf8#64) 104 ∗
                stackAt s1.sp chainCloneStack ∗
                (chainAt A (g, rc) src ∗ chainAt A (g', rc) (dst_base + off) ∗ F))
        (by exact Entails.of_eq (by ac_rfl)) ?_
      refine ih s1 rc2 g2 gs2 (src + 0x68#64) (off + 0x68#64) _
        hgs2 hmul2_lt hsz2_le hpc1 hrun1 hspA1 hcl1 hx1_1 hx20_1 hx21_1 hx22_next hx23_1 hx27_1 hx29_1 htr1 hvregs1
        fun s2 gs2' hgs2' henc2' hpc2 hrun2 hsp2 hspA2 hcl2 hx19_2 hx21_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 => ?_
      rw [hsp1] at hx21_2 hx29_2 ⊢
      refine SepWPp.weaken_pre ?_
        (hnext s2 (g' :: gs2') (by simp [hgs2']) (by simp [henc_g', henc2'])
          hpc2 hrun2 (hsp2.trans hsp1) hspA2 hcl2
          (hx19_2.trans hx19_1) hx21_2 (hx25_2.trans hx25_1) (hx26_2.trans hx26_1)
          hx27_2 hx29_2 htr2 hvregs2)
      simp only [List.zip_cons_cons, arrayAt_cons]
      have hd_add : dst_base + off + BitVec.ofNat 64 104 = dst_base + (off + 0x68#64) := by
        bv_arith
      rw [hd_add]
      exact Entails.of_eq (by ac_rfl)

theorem sc_receiverChains_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hkit : ScExternKit_placed A H)
    (hcall : subroutine_ok (lsProg_80 H) (blkPl_82).base
      (withLsCodeLoaded lsmpl (chainCloneSpec A)))
    (x : SessionCloneGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop)
    (F : SepProp)
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (blkPl_80).base + 0x23c#64
                   else
                     (blkPl_80).base + 0x150#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx21 : s.readReg64 .x21 = s.sp + 0xf8#64)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.s.state.receiverChains.length)
    (hx29 : s.readReg64 .x29 = s.sp + 0x170#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.s.state.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.s.state.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.s.state.receiverChains.length →
      ((chains'.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) =
        ((x.G.chains.zip x.s.state.receiverChains).map fun gc => lenField 7 (encChainMem gc)) →
      s1.pc = (if x.s.state.receiverChains = [] then
                 (blkPl_80).base + 0x240#64
               else
                 (blkPl_80).base + 0x1dc#64) →
      s1.status = .Running →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x21 = s.sp + 0xf8#64 →
      s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = chainsCap' →
      s1.readReg64 .x27 = chainsPtr' →
      s1.readReg64 .x29 = s.sp + 0x170#64 →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (lsProg_80 H) ret s1
        (A.pool ∗
          ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.s.state.receiverChains) ∗
          memRegion (s.sp + 0xf8#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
      (A.pool ∗
        ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.s.state.receiverChains) ∗
        memRegion (s.sp + 0xf8#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (scPanicPost A x R s0) := by
  have hshim := hkit.shim
  have halloc := hkit.alloc
  have hpanic := sc_panic_0x498_placed (A := A) hkit.panic_err (ret := ret) (Q := Q) x s0
  clear hkit
  cases hrc_eq : x.s.state.receiverChains with
  | nil =>
    clear hshim halloc hpanic hcall hcl
    simp only [hrc_eq, ↓reduceIte, List.length_nil] at hpc hx26 hchains_len ⊢
    apply SepWPp.of_sepWP (mid := (blkPl_80).base + 576#64)
    wp_steps
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ 0#64 8#64 [] (by simp [hrc_eq]) (by simp [hrc_eq]) (by simp [hrc_eq])
        (by simp only [hrc_eq, ↓reduceIte]; sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2))
    simp only [hrc_eq, List.zip_nil_right, segClone_vecBuf_chain_nil_eq]
    exact Entails.of_eq (by ac_rfl)
  | cons rc rcs_tl =>
    have hsub := sc_receiverChains_loop_placed hcall x R s0 ret Q
    clear hcall
    have hne : x.s.state.receiverChains ≠ [] := by simp [hrc_eq]
    simp only [hne, ↓reduceIte] at hpc hnext
    rw [hrc_eq] at hx26
    cases hgs_eq : x.G.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hgs_tl : gs_tl.length = rcs_tl.length := by
        rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hexpose :=
        segClone_vecBuf_expose_arrayAt A (stride := 104) 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
          ((g :: gs_tl).zip (rc :: rcs_tl))
      refine SepWPp.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (hexpose _))) ?_
      refine sepWPp_pure_3rd fun hmul_lt => ?_
      have hzip_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs_tl]
      rw [hzip_len] at hmul_lt
      have hpos : 0 < (rc :: rcs_tl).length := by simp
      have hpos_mul : 0 < (rc :: rcs_tl).length * 104 := by simp [List.length_cons]
      have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by simp [List.length_cons] at hmul_lt; omega
      have hsz_le63 : (rc :: rcs_tl).length * 104 + 8 ≤ 2 ^ 63 := by
        simp [List.length_cons] at hmul_lt ⊢; omega
      have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat =
          (rc :: rcs_tl).length * 104 :=
        segClone_bv_ofNat_mul_104_toNat hmul_lt
      have hpow2 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      have hlay : LayoutOk ((rc :: rcs_tl).length * 104) 8 :=
        ⟨hpos_mul, hpow2, hsz_le63⟩
      rw [stackAt_chainClone_eq_alloc s.sp]
      apply sepWPp_of_sepWP_lscl_sc hcl (mid := (blkPl_80).base + 364#64)
      wp_steps
      wp_call hshim ()
      clear hshim
      wp_steps
      wp_call halloc ((rc :: rcs_tl).length * 104, 8)
      clear halloc
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      intro hcl1
      by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
      · clear hsub hnext hcl1
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPp_pure_3rd fun htrace => ?_
        apply SepWPp.of_sepWP (mid := (blkPl_80).base + 1176#64)
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        exact hpanic _ _ R (by sc_close2) (by sc_close2) (by sc_close2)
      · clear hpanic
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
        apply sepWPp_of_sepWP_lscl_sc hcl1 (mid := (blkPl_80).base + 392#64)
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        intro hcl2
        have hsf_sp : sf.sp = s.sp := by sc_close2
        have hsf1_sp : sf_1.sp = s.sp := by sc_close2
        set ptr' := sf_1.readReg64 (Reg.gpr 0#5)
        have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
        have hsz_eq : (rc :: rcs_tl).length * 104 = (rcs_tl.length + 1) * 104 := rfl
        refine SepWPp.weaken_pre
          (P' := A.pool ∗
                  arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                  memRegion (sf_1.sp + 0xf8#64) 104 ∗
                  stackAt sf_1.sp chainCloneStack ∗
                  (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                    ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
                    segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr
                      ((g :: gs_tl).zip (rc :: rcs_tl)) ∗ F))
          (by rw [hsf1_sp, hsf_sp, hptr_zero, ← hsz_eq, stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl)) ?_
        refine hsub ptr' rcs_tl _
          rc g gs_tl x.G.chainsPtr 0#64 _
          hgs_tl (by simpa [List.length_cons] using hmul_lt) hsz_le
          (by sc_close2) (by sc_close2) (by sc_close2) hcl2
          (by sc_close2) (by sc_close2)
          (by sc_close2)
          (by sc_close2) (by sc_close2)
          (by dsimp only [ptr']; sc_close2)
          (by sc_close2)
          (by sc_close2)
          (by sc_close2)
          fun s2 gs' hgs' henc' hpc2 hrun2 hsp2 hspA2 _hcl2 hx19_2 hx21_2 hx25_2 hx26_2 hx27_2 hx29_2 htr2 hvregs2 => ?_
        clear hsub
        dsimp only [Reg.x19, Reg.x25, Reg.x26] at hx19_2 hx25_2 hx26_2
        simp (config := { decide := true }) only [State.sp_setPC, State.sp_writeReg64_gpr,
          State.readReg64_setPC, State.readReg64_writeReg64, reduceStateReadReg64] at hsp2 hx19_2 hx21_2 hx25_2 hx26_2 hx29_2
        rw [hsf1_sp] at hsp2 hx21_2 hx29_2
        rw [hptr_zero]
        refine SepWPp.weaken_pre ?_
          (hnext s2 (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' gs'
            (by rw [hrc_eq]; exact hgs') (by rw [hrc_eq])
            (by rw [hgs_eq, hrc_eq]; exact henc')
            hpc2 hrun2 (by sc_close2) hspA2
            (by sc_close2) hx21_2 (by sc_close2)
            (by sc_close2) hx27_2 hx29_2 htr2 hvregs2)
        dsimp only [State.setPC, State.setPState, State.writeReg64]
        simp only [hgs_eq, hrc_eq, hsf1_sp]
        have hreasm :=
          segClone_vecBuf_reassemble_arrayAt A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
            ((g :: gs_tl).zip (rc :: rcs_tl))
        have hnew_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
          simp [hgs']
        have hnew_pos : 0 < (gs'.zip (rc :: rcs_tl)).length := by rw [hnew_len]; exact hpos
        have hnew_lt : (gs'.zip (rc :: rcs_tl)).length * 104 < 2 ^ 63 := by rw [hnew_len]; exact hmul_lt
        have hnew_buf := segClone_vecBuf_chain_of_arrayAt A ptr' (gs'.zip (rc :: rcs_tl)) hnew_pos hnew_lt hoom64
        rw [hnew_len] at hnew_buf
        refine Entails.trans
          (Q := (arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
                (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗
                  arrayAt (chainAt A) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
                A.pool ∗ ((x.src + 0x50#64) ↦₆₄ x.G.chainsPtr) ∗
                memRegion (s.sp + 0xf8#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
          (Entails.of_eq (by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hreasm (sepConj_mono_left hnew_buf)) ?_
        exact Entails.of_eq (by ac_rfl)

theorem sc_pendingPreKey_200_pos_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hkit : ScExternKit_placed A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 : BitVec 64}
    {v18 v20 : BitVec 64} {F : SepProp}
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4)))
    (htail_val : gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4)
    (hpos : 0 < gp.vec.bytes.length)
    (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63)
    (hptr : gp.vec.ptr ≠ 0)
    (hpc : s.pc = (blkPl_80).base + 0x200#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx23 : (s.readReg64 .x23).truncate 32 = tw0)
    (hx24 : (s.readReg64 .x24).truncate 32 = tw1)
    (hx25 : s.readReg64 .x25 = x.src)
    (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (blkPl_80).base + 0x250#64 ∨
       s1.pc = (blkPl_80).base + 0x288#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' → s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' → s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (lsProg_80 H) ret s1
        (A.pool ∗
          (⌜gp.tail.length = 48 - 24⌝ ∗
            vecGhostAt A gp.vec (x.src + 0xf8#64) ∗
            ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length ∧
              ∃ tw4' : BitVec 32,
                gp.tail = unpack32 w23' ++ unpack32 w24' ++ unpack64 v18' ++ unpack32 v2c' ++ unpack32 tw4'⌝ ∗
            vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗ ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗ stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
      (A.pool ∗
        ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗ ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
        ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗ (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
          (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
        ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
        ((x.src + 0x124#64) ↦₃₂ tw4) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x20#64) ↦₆₄ v20) ∗ ((s.sp + 0x2c#64) ↦₃₂ tw3) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  have hshim := hkit.shim
  have halloc := hkit.alloc
  have hmemcpy := hkit.memcpy
  have hpanic := sc_panic_0x4b0_placed (A := A) hkit.panic_err (ret := ret) (Q := Q) x s0
  clear hkit
  have h100 : x.src + 0xf8#64 + 8#64 = x.src + 0x100#64 := by bv_arith
  have h108 : x.src + 0xf8#64 + 16#64 = x.src + 0x108#64 := by bv_arith
  have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gp.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk gp.vec.bytes.length 1 := ⟨hpos, hpow2, hlen_le63⟩
  have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply SepWPp.of_sepWP (mid := (blkPl_80).base + 532#64)
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (gp.vec.bytes.length, 1)
  clear halloc
  refine SepWP.done (by sc_close2) (by sc_close2) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_80).base + 1200#64)
    wp_steps
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    exact hpanic _ _ R (by sc_close2) (by sc_close2) (by sc_close2)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := (blkPl_80).base + 648#64)
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gp.vec.ptr, gp.vec.bytes)
    clear hmemcpy
    wp_steps
    refine SepWP.done (by sc_close2) (by sc_close2) ?_
    have hsp_eq : sf.sp = s.sp := by sc_close2
    have hsf1_sp : sf_1.sp = s.sp := by sc_close2
    refine SepWPp.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gp.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) td2 tw0 tw1 tw3
        (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
        (by sc_close2) (by sc_close2) (by sc_close2))
    have h_rfl : (⌜BitVec.ofNat 64 gp.vec.bytes.length = BitVec.ofNat 64 gp.vec.bytes.length ∧
        ∃ tw4' : BitVec 32,
          gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4'⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨rfl, tw4, htail_val⟩
    have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
      segClone_pure_eq_emp htail
    have h_pure2 : (⌜gp.vec.bytes.length ≤ gp.vec.cap.toNat ∧ gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
      segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩
    rw [vecGhostAt_eq_of_pos A gp.vec (x.src + 0xf8#64) hpos, h100, h108,
        htail_eq,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) gp.vec.bytes hpos hlen_lt hoom64,
        h_rfl, h_pure1, h_pure2]
    simp only [sepConj_assoc, hsp_eq, hsf1_sp, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

theorem sc_pendingPreKey_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hkit : ScExternKit_placed A H)
    {x : SessionCloneGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v18 v20 : BitVec 64} {v2c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.s.state.receiverChains = [] then
                     (blkPl_80).base + 0x240#64
                   else
                     (blkPl_80).base + 0x1dc#64))
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = x.src)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v18' : BitVec 64) (w23' w24' v2c' : BitVec 32),
      (s1.pc = (blkPl_80).base + 0x250#64 ∨
       s1.pc = (blkPl_80).base + 0x288#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → (s1.readReg64 .x23).truncate 32 = w23' →
      (s1.readReg64 .x24).truncate 32 = w24' → s1.readReg64 .x25 = x.src →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = pendCap' → s1.readReg64 .x29 = s.readReg64 .x29 →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      SepWPp (lsProg_80 H) ret s1
        (A.pool ∗ optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
          ScOptPendClone A x.G.pending pendCap' pendPtr' w23' w24' v18' v2c' ∗
          ((s.sp + 0x18#64) ↦₆₄ v18') ∗ ((s.sp + 0x20#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗ stackAt s.sp allocHookStack ∗ F)
        Q (scPanicPost A x R s0)) :
    SepWPp (lsProg_80 H) ret s
      (A.pool ∗ optTailVecAt A 48 (x.src + 0xf8#64) x.G.pending ∗
        ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x20#64) ↦₆₄ v20) ∗
        ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ stackAt s.sp allocHookStack ∗ F)
      Q (scPanicPost A x R s0) := by
  cases hpend : x.G.pending with
  | none =>
    clear hkit
    rw [hpend] at hnext
    dsimp only [optTailVecAt, ScOptPendClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    by_cases hrc : x.s.state.receiverChains = []
    · simp only [hrc, ↓reduceIte] at hpc
      apply SepWPp.of_sepWP (mid := (blkPl_80).base + 592#64)
      wp_steps
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v20 v18
          ((s.readReg64 .x23).truncate 32) ((s.readReg64 .x24).truncate 32) v2c
          (Or.inl (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
    · simp only [hrc, ↓reduceIte] at hpc
      apply SepWPp.of_sepWP (mid := (blkPl_80).base + 592#64)
      wp_steps
      refine SepWP.done (by sc_close2) (by sc_close2) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v20 v18
          ((s.readReg64 .x23).truncate 32) ((s.readReg64 .x24).truncate 32) v2c
          (Or.inl (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
          (by sc_close2) (by sc_close2) (by sc_close2))
      rw [h_rfl]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
      exact Entails.of_eq (by ac_rfl)
  | some gp =>
    rw [hpend] at hnext
    dsimp only [optTailVecAt, ScOptPendClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, htail_val, htail_pts⟩ := exists_tail24_decomp htail
    have h100 : x.src + 0xf8#64 + 8#64 = x.src + 0x100#64 := by bv_arith
    have h108 : x.src + 0xf8#64 + 16#64 = x.src + 0x108#64 := by bv_arith
    have h110 : x.src + 0xf8#64 + BitVec.ofNat 64 24 = x.src + 0x110#64 := by bv_arith
    have h114 : x.src + 0x110#64 + 4#64 = x.src + 0x114#64 := by bv_arith
    have h118 : x.src + 0x110#64 + 8#64 = x.src + 0x118#64 := by bv_arith
    have h120 : x.src + 0x110#64 + 16#64 = x.src + 0x120#64 := by bv_arith
    have h124 : x.src + 0x110#64 + 20#64 = x.src + 0x124#64 := by bv_arith
    have htail_eq : ((x.src + 0xf8#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
        (((x.src + 0x110#64) ↦₃₂ tw0) ∗ ((x.src + 0x114#64) ↦₃₂ tw1) ∗
          ((x.src + 0x118#64) ↦₆₄ td2) ∗ ((x.src + 0x120#64) ↦₃₂ tw3) ∗
          ((x.src + 0x124#64) ↦₃₂ tw4)) := by
      rw [h110, htail_pts (x.src + 0x110#64), h114, h118, h120, h124]
    rw [htail_eq]
    rcases eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · clear hkit
      rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length ∧
          ∃ tw4' : BitVec 32,
            gp.tail = unpack32 tw0 ++ unpack32 tw1 ++ unpack64 td2 ++ unpack32 tw3 ++ unpack32 tw4'⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨rfl, tw4, htail_val⟩
      have h_pure1 : (⌜gp.tail.length = 48 - 24⌝ : SepProp) = emp :=
        segClone_pure_eq_emp htail
      have h_pure2 : (⌜gp.vec.cap.toNat < 2 ^ 63 ∧ gp.vec.ptr ≠ 0⌝ : SepProp) = emp :=
        segClone_pure_eq_emp ⟨hcap_lt, hptr⟩
      by_cases hrc : x.s.state.receiverChains = []
      · simp only [hrc, ↓reduceIte] at hpc
        apply SepWPp.of_sepWP (mid := (blkPl_80).base + 648#64)
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw0 tw1 tw3
            (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2))
        rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108,
            htail_eq, hnil, vecU8Buf_nil_eq A, h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
      · simp only [hrc, ↓reduceIte] at hpc
        apply SepWPp.of_sepWP (mid := (blkPl_80).base + 648#64)
        wp_steps
        refine SepWP.done (by sc_close2) (by sc_close2) ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw0 tw1 tw3
            (Or.inr (by sc_close2)) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2))
        rw [vecGhostAt_eq_of_nil A gp.vec (x.src + 0xf8#64) hnil, h100, h108,
            htail_eq, hnil, vecU8Buf_nil_eq A, h_rfl, h_pure1, h_pure2]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
        exact Entails.of_eq (by ac_rfl)
    · rw [vecGhostAt_eq_of_pos A gp.vec (x.src + 0xf8#64) hpos, h100, h108]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 :=
        ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false :=
        beq_ofNat_zero_eq_false hpos (by omega)
      have hsub := fun (s_200 : State) =>
        sc_pendingPreKey_200_pos_placed hkit (x := x) (R := R) (s0 := s0) (s := s_200) (ret := ret) (Q := Q)
          (gp := gp) (tw0 := tw0) (tw1 := tw1) (tw3 := tw3) (tw4 := tw4) (td2 := td2)
          (v18 := v18) (v20 := v20) (F := F)
          htail htail_eq htail_val hpos hlen_le hcap_lt hptr
      clear hkit
      suffices h_at_200 : ∀ s_200 : State,
          s_200.pc = (blkPl_80).base + 0x200#64 →
          s_200.status = .Running →
          s_200.sp = s.sp →
          s_200.spAligned = true →
          s_200.readReg64 .x19 = s.readReg64 .x19 →
          (s_200.readReg64 .x23).truncate 32 = tw0 →
          (s_200.readReg64 .x24).truncate 32 = tw1 →
          s_200.readReg64 .x25 = x.src →
          s_200.readReg64 .x26 = s.readReg64 .x26 →
          s_200.readReg64 .x27 = s.readReg64 .x27 →
          s_200.readReg64 .x28 = BitVec.ofNat 64 gp.vec.bytes.length →
          s_200.readReg64 .x29 = s.readReg64 .x29 →
          s_200.trace = s0.trace →
          calleeSavedVRegs s_200 = calleeSavedVRegs s0 →
          SepWPp (lsProg_80 H) ret s_200
            (A.pool ∗
              ((x.src + 0xf8#64) ↦₆₄ gp.vec.cap) ∗
              ((x.src + 0x100#64) ↦₆₄ gp.vec.ptr) ∗
              ((x.src + 0x108#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗
              (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
              A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
              memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length)
                (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
              ((x.src + 0x110#64) ↦₃₂ tw0) ∗
              ((x.src + 0x114#64) ↦₃₂ tw1) ∗
              ((x.src + 0x118#64) ↦₆₄ td2) ∗
              ((x.src + 0x120#64) ↦₃₂ tw3) ∗
              ((x.src + 0x124#64) ↦₃₂ tw4) ∗
              ((s_200.sp + 0x18#64) ↦₆₄ v18) ∗
              ((s_200.sp + 0x20#64) ↦₆₄ v20) ∗
              ((s_200.sp + 0x2c#64) ↦₃₂ tw3) ∗
              stackAt s_200.sp allocHookStack ∗ F)
            Q (scPanicPost A x R s0) by
        clear hsub
        by_cases hrc : x.s.state.receiverChains = []
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPp.of_sepWP (mid := (blkPl_80).base + 512#64)
          wp_steps
          refine SepWP.done (by sc_close2) (by sc_close2) ?_
          exact h_at_200 _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
        · simp only [hrc, ↓reduceIte] at hpc
          apply SepWPp.of_sepWP (mid := (blkPl_80).base + 512#64)
          wp_steps
          refine SepWP.done (by sc_close2) (by sc_close2) ?_
          exact h_at_200 _ (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2)
            (by sc_close2) (by sc_close2) (by sc_close2) (by sc_close2)
      intro s_200 hpc200 hrun200 hsp200 hspA200 hx19_200 hx23_200 hx24_200 hx25_200 hx26_200 hx27_200 hx28_200 hx29_200 htr200 hvregs200
      refine hsub s_200 hpc200 hrun200 hspA200 hx23_200 hx24_200 hx25_200 hx28_200 htr200 hvregs200
        fun s1 pendCap' pendPtr' v18' w23' w24' v2c' hpc1 hrun1 hsp1 hspA1 hx19_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hvregs1 => ?_
      clear hsub
      rw [hsp200]
      exact hnext s1 pendCap' pendPtr' v18' w23' w24' v2c'
        hpc1 hrun1 (hsp1.trans hsp200) hspA1
        (hx19_1.trans hx19_200) hx23_1 hx24_1 hx25_1
        (hx26_1.trans hx26_200) (hx27_1.trans hx27_200) hx28_1 (hx29_1.trans hx29_200) htr1 hvregs1

end Placed

end CryptoVerification.E2E.Record.Serialization.SessionCloneAux
