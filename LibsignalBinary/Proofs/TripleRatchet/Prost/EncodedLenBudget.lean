/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen
meta import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLen -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Relocatable `VmPreserved` Verification of `<SignalMessage as Message>::encoded_len`

Proves `EncDefsBudget.EncodedLenPlacedOk` for `<wire::SignalMessage as prost::message::Message>::encoded_len`
(block 108) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (VmPreserved)
open CryptoGames.LibsignalSession (ProtoSignalMessage)
open CryptoVerification.LibsignalProtoCodec (encodeBytesField encodeUint32Field)
open CryptoVerification (LibsignalPlacement blkPC_108 blkPl_108)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (WireSignalMessageGhost WireLengthsFit wireSignalMessageAt
   EncLenCalleeSaved wireMsgUnpacked wireSignalMessageAt_eq_unpacked
   stackAt_encodedLen_eq wireMsgUnpacked_bounds encode_length_eq
   optVecCap optVecPayload optU32Tag optU32Payload vecU8Buf
   hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
   ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
   truncate32_zext64_lsr6
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   optU32Tag_beq_one optU32Tag_bne_one zext64_optU32Tag_truncate32
   hwVarintLen_w32_eq_encodeVarint_length hwVarintLen_w32_natShift_eq_encodeVarint_length
   bv_encodeBytesField_some_length bv_encodeUint32Field_some_length
   bv_add_ofNat_comm bv_add_ofNat_eq
   ule_zero_64 ult_zero_64 ule_ofNat_add_of_lt ult_ofNat_add_of_lt)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (encodedLenSpec EncodedLenPlacedOk)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm]
  bv_sub_add_lit BitVec.toNat_zero
  hwVarintLen_eq_encodeVarint_length hwVarintLen_bvShift_eq_encodeVarint_length
attribute [local simp, local arm64_norm]
  ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  CryptoVerification.LibsignalTripleRatchet.Prost.truncate32_ofNat64
  truncate32_zext64_lsr6
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  optU32Tag_beq_one optU32Tag_bne_one zext64_optU32Tag_truncate32
  hwVarintLen_w32_eq_encodeVarint_length hwVarintLen_w32_natShift_eq_encodeVarint_length
  ule_zero_64 ult_zero_64

private theorem sepWPp_of_sepWP_vm {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s Pre Q Qp :=
  SepWPp.of_sepWP (mid := mid) (SepWP.mono h (fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm))

private theorem step_encLen_f1_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a sp v16 v8 : BitVec 64) (m : ProtoSignalMessage)
    (hrk_beq : (optVecCap g.rk m.ratchetKey + 1#64 == 0#64) = !m.ratchetKey.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_108).base)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hP : P = (wireMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (if m.counter.isSome then (blkPl_108).base + 64#64 else (blkPl_108).base + 184#64) →
      sm.status = .Running →
      sm.sp = sp - 16#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (encodeBytesField 1 m.ratchetKey).length →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm
        ((wireMsgUnpacked A g a m ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hrk : m.ratchetKey with
  | none =>
    have hP1 : wireMsgUnpacked A g a m =
        (a ↦₆₄ noneCap) ∗ optVecPayload A g.rk a none ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hrk, optVecCap]
    rw [hP1]
    apply sepWPp_of_sepWP_vm
      (mid := if m.counter.isSome then (blkPl_108).base + 64#64 else (blkPl_108).base + 184#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by cases m.counter <;> simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP1]
      exact hnext _ hvm (by cases m.counter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hrk_beq' : (g.rk.cap + 1#64 == 0#64) = false := by
      rwa [hrk, Option.isSome_some, Bool.not_true, optVecCap] at hrk_beq
    have henc := bv_encodeBytesField_some_length (t := 1) (bs := bs) rfl
    have hP1 : wireMsgUnpacked A g a m =
        (a ↦₆₄ g.rk.cap) ∗ ((a + 8#64) ↦₆₄ g.rk.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A g.rk.cap g.rk.ptr bs ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hrk, optVecCap, optVecPayload, sepConj_assoc]
    rw [hP1]
    apply sepWPp_of_sepWP_vm
      (mid := if m.counter.isSome then (blkPl_108).base + 64#64 else (blkPl_108).base + 184#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by cases m.counter <;> simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP1]
      exact hnext _ hvm (by cases m.counter <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f2_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s1 : Nat)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.counter.isSome then (blkPl_108).base + 64#64 else (blkPl_108).base + 184#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (if m.previousCounter.isSome then (blkPl_108).base + 200#64 else (blkPl_108).base + 108#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (encodeUint32Field 2 m.counter).length) →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm P Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hcnt : m.counter with
  | none =>
    simp only [hcnt, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP2 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 96#64) none ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hcnt]
    rw [hP2]
    apply sepWPp_of_sepWP_vm
      (mid := if m.previousCounter.isSome then (blkPl_108).base + 200#64 else (blkPl_108).base + 108#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by cases m.previousCounter <;> simp_all) (by simp_all)
        ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP2]
      exact hnext _ hvm (by cases m.previousCounter <;> simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [encodeUint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    simp only [hcnt, Option.isSome_some, ↓reduceIte] at hpc
    have henc := bv_encodeUint32Field_some_length (t := 2) (v := v) rfl
    have hadd := bv_add_ofNat_comm s1 (encodeUint32Field 2 (some v)).length
    have hP2 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ 1#32) ∗ ((a + 100#64) ↦₃₂ v) ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hcnt, optU32Tag, optU32Payload, arm64_norm]
    rw [hP2]
    apply sepWPp_of_sepWP_vm
      (mid := if m.previousCounter.isSome then (blkPl_108).base + 200#64 else (blkPl_108).base + 108#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by cases m.previousCounter <;> simp_all) (by simp_all)
        ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP2]
      exact hnext _ hvm (by cases m.previousCounter <;> simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f3_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s12 : Nat)
    (hct_beq : (optVecCap g.ct m.ciphertext + 1#64 == 0#64) = !m.ciphertext.isSome)
    (hct_bne : (optVecCap g.ct m.ciphertext + 1#64 != 0#64) = m.ciphertext.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.previousCounter.isSome then (blkPl_108).base + 200#64 else (blkPl_108).base + 108#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (if m.ciphertext.isSome then (blkPl_108).base + 124#64 else (blkPl_108).base + 248#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12 + (encodeUint32Field 3 m.previousCounter).length) →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm P Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hprev : m.previousCounter with
  | none =>
    simp only [hprev, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP3 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 104#64) none := by
      simp only [wireMsgUnpacked, hprev]
    rw [hP3]
    apply sepWPp_of_sepWP_vm
      (mid := if m.ciphertext.isSome then (blkPl_108).base + 124#64 else (blkPl_108).base + 248#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by cases m.ciphertext <;> simp_all) (by simp_all)
        ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP3]
      exact hnext _ hvm (by cases m.ciphertext <;> simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [encodeUint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    simp only [hprev, Option.isSome_some, ↓reduceIte] at hpc
    have henc := bv_encodeUint32Field_some_length (t := 3) (v := v) rfl
    have hadd := bv_add_ofNat_eq s12 (encodeUint32Field 3 (some v)).length
    have hP3 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ 1#32) ∗ ((a + 108#64) ↦₃₂ v) := by
      simp only [wireMsgUnpacked, hprev, optU32Tag, optU32Payload, arm64_norm]
    rw [hP3]
    apply sepWPp_of_sepWP_vm
      (mid := if m.ciphertext.isSome then (blkPl_108).base + 124#64 else (blkPl_108).base + 248#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by cases m.ciphertext <;> simp_all) (by simp_all)
        ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP3]
      exact hnext _ hvm (by cases m.ciphertext <;> simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f4_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s123 : Nat)
    (hfit : s123 + (encodeBytesField 4 m.ciphertext).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.ciphertext.isSome then (blkPl_108).base + 124#64 else (blkPl_108).base + 248#64))
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_108).base + 256#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123 + (encodeBytesField 4 m.ciphertext).length) →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm P Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hct : m.ciphertext with
  | none =>
    simp only [hct, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_vm (mid := (blkPl_108).base + 256#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    simp only [hct, Option.isSome_some, ↓reduceIte] at hpc
    rw [hct] at hfit
    have henc := bv_encodeBytesField_some_length (t := 4) (bs := bs) rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123 (encodeBytesField 4 (some bs)).length
    have hP4 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ g.ct.cap) ∗ ((a + 32#64) ↦₆₄ g.ct.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.ct.cap g.ct.ptr bs ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hct, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP4]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_108).base + 256#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP4]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f5_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a : BitVec 64) (m : ProtoSignalMessage) (s1234 : Nat)
    (hpq_beq : (optVecCap g.pq m.pqRatchet + 1#64 == 0#64) = !m.pqRatchet.isSome)
    (hfit : s1234 + (encodeBytesField 5 m.pqRatchet).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_108).base + 256#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = wireMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_108).base + 320#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1234 + (encodeBytesField 5 m.pqRatchet).length) →
      EncLenCalleeSaved s sm →
      SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret sm P Q Qp) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) ret s P Q Qp := by
  subst hP
  cases hpq : m.pqRatchet with
  | none =>
    have hP5 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ noneCap) ∗ optVecPayload A g.pq (a + 48#64) none ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hpq, optVecCap]
    rw [hP5]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_108).base + 320#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP5]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [encodeBytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hpq_beq' : (g.pq.cap + 1#64 == 0#64) = false := by
      rwa [hpq, Option.isSome_some, Bool.not_true, optVecCap] at hpq_beq
    rw [hpq] at hfit
    have henc := bv_encodeBytesField_some_length (t := 5) (bs := bs) rfl
    have hcc := ule_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234 (encodeBytesField 5 (some bs)).length
    have hP5 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ g.pq.cap) ∗ ((a + 56#64) ↦₆₄ g.pq.ptr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.pq.cap g.pq.ptr bs ∗
        ((a + 72#64) ↦₆₄ optVecCap g.addr m.addresses) ∗ optVecPayload A g.addr (a + 72#64) m.addresses ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, hpq, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP5]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_108).base + 320#64)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP5]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

private theorem step_encLen_f6_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (g : WireSignalMessageGhost) (a sp : BitVec 64) (m : ProtoSignalMessage) (s12345 : Nat)
    (haddr_beq : (optVecCap g.addr m.addresses + 1#64 == 0#64) = !m.addresses.isSome)
    (hfit : s12345 + (encodeBytesField 6 m.addresses).length < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_108).base + 320#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 16#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12345)
    (hcs : EncLenCalleeSaved s0 s)
    (hP : P = (wireMsgUnpacked A g a m ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ F)
    (hnext : ∀ sf : State,
      VmPreserved s sf →
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (s12345 + (encodeBytesField 6 m.addresses).length) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPp ((blkPC_108).rebase (blkPl_108).base H) (s0.readReg64 .lr) s P Q Qp := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  subst hP
  cases haddr : m.addresses with
  | none =>
    have hP6 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ noneCap) ∗ optVecPayload A g.addr (a + 72#64) none ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, haddr, optVecCap]
    rw [hP6]
    apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP6]
      apply SepWPp.done (by simp_all) (by simp_all)
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [encodeBytesField]) (by encodedLen_cc_close)
  | some bs =>
    have haddr_beq' : (g.addr.cap + 1#64 == 0#64) = false := by
      rwa [haddr, Option.isSome_some, Bool.not_true, optVecCap] at haddr_beq
    rw [haddr] at hfit
    have henc := bv_encodeBytesField_some_length (t := 6) (bs := bs) rfl
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12345 (encodeBytesField 6 (some bs)).length
    have hP6 : wireMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.rk m.ratchetKey) ∗ optVecPayload A g.rk a m.ratchetKey ∗
        ((a + 24#64) ↦₆₄ optVecCap g.ct m.ciphertext) ∗ optVecPayload A g.ct (a + 24#64) m.ciphertext ∗
        ((a + 48#64) ↦₆₄ optVecCap g.pq m.pqRatchet) ∗ optVecPayload A g.pq (a + 48#64) m.pqRatchet ∗
        ((a + 72#64) ↦₆₄ g.addr.cap) ∗ ((a + 80#64) ↦₆₄ g.addr.ptr) ∗
        ((a + 88#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.addr.cap g.addr.ptr bs ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.counter) ∗ optU32Payload (a + 96#64) m.counter ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.previousCounter) ∗ optU32Payload (a + 104#64) m.previousCounter := by
      simp only [wireMsgUnpacked, haddr, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP6]
    apply sepWPp_of_sepWP_vm (mid := s0.readReg64 .lr)
    by_vm_steps
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP6]
      apply SepWPp.done (by simp_all) (by simp_all)
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by encodedLen_cc_close)

/-- Block `108` (`<SignalMessage as prost::message::Message>::encoded_len`) meets
`EncDefsBudget.encodedLenSpec A` under `[LibsignalPlacement]`. -/
theorem encoded_len_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    EncodedLenPlacedOk A H := by
  apply subroutine_ok_of_sepWPp
  intro ⟨a, g, m⟩ R s0 hpc0 hrun hpre hsp
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [encodedLenSpec, wireSignalMessageAt_eq_unpacked, stackAt_encodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v16, v8, ⟨hx0, hfit⟩, hpre⟩
  unfold WireLengthsFit at hfit
  rw [encode_length_eq] at hfit
  have hmem0 : s0.mem ⊨
      (wireMsgUnpacked A g a m ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre using 1; sep_ac_rfl
  have hmem0' : s0.mem ⊨
      wireMsgUnpacked A g a m ∗ (((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) :=
    hpre
  obtain ⟨hrk_beq, hct_beq, hct_bne, hpq_beq, haddr_beq⟩ := wireMsgUnpacked_bounds hmem0'
  refine ⟨(wireMsgUnpacked A g a m ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R, emp,
      by rwa [sepConj_emp], ?_⟩
  refine step_encLen_f1_placed (F := R) A H g a s0.sp v16 v8 m hrk_beq
    hpc0 hrun rfl halign hx0 rfl ?_
  intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  let FSave : SepProp :=
    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr) ∗ R
  have hP_save :
      (wireMsgUnpacked A g a m ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ R =
      wireMsgUnpacked A g a m ∗ FSave := by
    dsimp [FSave]; sep_ac_rfl
  refine step_encLen_f2_placed (F := FSave) A H g a m
    (encodeBytesField 1 m.ratchetKey).length
    hpc1 hrun1 hx0_1 hx8_1 hP_save ?_
  intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
  refine step_encLen_f3_placed (F := FSave) A H g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length)
    hct_beq hct_bne
    hpc2 hrun2 hx0_2 hx8_2 hP_save ?_
  intro s3 hvm3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
  refine step_encLen_f4_placed (F := FSave) A H g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length)
    (by omega) hpc3 hrun3 hx0_3 hx8_3 hP_save ?_
  intro s4 hvm4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
  refine step_encLen_f5_placed (F := FSave) A H g a m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length + (encodeBytesField 4 m.ciphertext).length)
    hpq_beq (by omega) hpc4 hrun4 hx0_4 hx8_4 hP_save ?_
  intro s5 hvm5 hpc5 hrun5 hsp5 htr5 hx0_5 hx8_5 hcs5
  have hsp5' : s5.sp = s0.sp - 16#64 := by rw [hsp5, hsp4, hsp3, hsp2, hsp1]
  have hcs5' : EncLenCalleeSaved s0 s5 :=
    hcs1.trans (hcs2.trans (hcs3.trans (hcs4.trans hcs5)))
  refine step_encLen_f6_placed (F := R) A H g a s0.sp m
    ((encodeBytesField 1 m.ratchetKey).length + (encodeUint32Field 2 m.counter).length +
      (encodeUint32Field 3 m.previousCounter).length + (encodeBytesField 4 m.ciphertext).length +
      (encodeBytesField 5 m.pqRatchet).length)
    haddr_beq (by omega) hpc5 hrun5 hsp5' halign hx0_5 hx8_5 hcs5' rfl ?_
  intro sf hvm6 hpcf hrunf hspf htrf hx0_f hcsf
  have hvm_all : VmPreserved s0 sf :=
    hvm1.trans (hvm2.trans (hvm3.trans (hvm4.trans (hvm5.trans hvm6))))
  have htr_all : sf.trace = s0.trace := by reg_chain
  rw [← encode_length_eq] at hx0_f
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  simp only [encodedLenSpec, wireSignalMessageAt_eq_unpacked, stackAt_encodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, ⟨hvm_all, hx0_f, htr_all⟩, ?_⟩
  convert hm_f using 1
  sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Prost.EncodedLenBudget
