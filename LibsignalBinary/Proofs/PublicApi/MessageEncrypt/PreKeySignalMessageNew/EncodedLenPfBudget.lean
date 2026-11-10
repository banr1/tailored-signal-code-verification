/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPf
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Compatible Stepping Proof for `PreKeySignalMessage::encoded_len`

Relocatable `[LibsignalPlacement]` stepping proof establishing `SplitBudget.preKeyMsgEncodedLenSpec A`
(preserving `VmPreserved`) for `<wire::PreKeySignalMessage as prost::message::Message>::encoded_len`
(block `119`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPfBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved trapHooks
   vmPreserved_refl_iff vmPreserved_setPC vmPreserved_advancePC vmPreserved_setPState
   vmPreserved_writeReg64 vmPreserved_writeReg32 vmPreserved_writeReg
   vmPreserved_writeVReg128 vmPreserved_writeVReg64 vmPreserved_writeVReg32
   vmPreserved_applyWriteback vmPreserved_setStatus vmPreserved_appendTrace
   vmPreserved_setFs vmPreserved_stepExclLoop tpidrEl0_applyWriteback)
open CryptoGames.LibsignalSessionApi (ProtoPreKeySignalMessage)
open CryptoGames.LibsignalSessionApi.Prost (bytesField uint32Field)
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_119 blkPC_119 blkPl_119)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (WirePreKeySignalMessageGhost)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPf
  (hwVarintLen_eq_prost_varint_length hwVarintLen_bvShift_eq_prost_varint_length
   optVecCap vecU8Buf optVecPayload optU32Tag optU32Payload
   noneCap_add_one_beq_zero noneCap_add_one_bne_zero
   optU32Tag_beq_one optU32Tag_bne_one zext64_optU32Tag_truncate32
   bv_prost_bytesField_some_length bv_prost_uint32Field_some_length bv_add_ofNat_comm
   ule_zero_64 ult_zero_64 ule_ofNat_add_of_lt ult_ofNat_add_of_lt
   EncLenCalleeSaved wirePreKeyMsgUnpacked wirePreKeySignalMessageAt_eq_unpacked
   wirePreKeyMsgUnpacked_bounds preKeyMsg_encode_length_eq stackAt_16_eq
   calleeSavedPreserved_of_encLen)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
  (preKeyMsgEncodedLenSpec PreKeyMsgEncodedLenPlacedOk)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  hwVarintLen_eq_prost_varint_length
  hwVarintLen_bvShift_eq_prost_varint_length
  noneCap_add_one_beq_zero
  noneCap_add_one_bne_zero
  optU32Tag_beq_one
  optU32Tag_bne_one
  zext64_optU32Tag_truncate32
  ule_zero_64
  ult_zero_64

private theorem sepWPp_of_sepWP_vm [LibsignalPlacement] {H : LibsignalHooks}
    {mid ret : BitVec 64} {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop}
    (hwp : SepWP ((blkPC_119).rebase (blkPl_119).base H) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → SepWPp (lsProg_119 H) ret sm Pm Q Qp))) :
    SepWPp (lsProg_119 H) ret s Pre Q Qp :=
  SepWPp.of_sepWP (SepWP.mono hwp fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm)

theorem step_encLen_f1_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a sp v16 v8 : BitVec 64) (m : ProtoPreKeySignalMessage)
    (hbk_beq : (optVecCap g.bk m.baseKey + 1#64 == 0#64) = !m.baseKey.isSome)
    (hbk_bne : (optVecCap g.bk m.baseKey + 1#64 != 0#64) = m.baseKey.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (wirePreKeyMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (if m.baseKey.isSome then (blkPl_119).base + 64#64 else (blkPl_119).base + 172#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (uint32Field 1 m.preKeyId).length →
      EncLenCalleeSaved s sm →
      SepWPp (lsProg_119 H) ret sm
        ((wirePreKeyMsgUnpacked A g a m ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hpk : m.preKeyId with
  | none =>
    have hP1 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 104#64) none ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hpk]
    rw [hP1]
    apply sepWPp_of_sepWP_vm (mid := if m.baseKey.isSome then (blkPl_119).base + 64#64 else (blkPl_119).base + 172#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by cases m.baseKey <;> simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP1]
      exact hnext _ hvm (by cases m.baseKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    have henc := bv_prost_uint32Field_some_length (t := 1) (v := v)
    have hP1 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ 1#32) ∗ ((a + 108#64) ↦₃₂ v) ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hpk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP1]
    apply sepWPp_of_sepWP_vm (mid := if m.baseKey.isSome then (blkPl_119).base + 64#64 else (blkPl_119).base + 172#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by cases m.baseKey <;> simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP1]
      exact hnext _ hvm (by cases m.baseKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f2_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s1 : Nat)
    (hik_beq : (optVecCap g.ik m.identityKey + 1#64 == 0#64) = !m.identityKey.isSome)
    (hik_bne : (optVecCap g.ik m.identityKey + 1#64 != 0#64) = m.identityKey.isSome)
    (hfit : s1 + (bytesField 2 m.baseKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.baseKey.isSome then (blkPl_119).base + 64#64 else (blkPl_119).base + 172#64))
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (if m.identityKey.isSome then (blkPl_119).base + 112#64 else (blkPl_119).base + 188#64) →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (bytesField 2 m.baseKey).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hbk : m.baseKey with
  | none =>
    simp only [hbk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP2 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk none) ∗ optVecPayload A g.bk (a + 24#64) none ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hbk]
    rw [hP2]
    apply sepWPp_of_sepWP_vm (mid := if m.identityKey.isSome then (blkPl_119).base + 112#64 else (blkPl_119).base + 188#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by cases m.identityKey <;> simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP2]
      exact hnext _ hvm (by cases m.identityKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [bytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    simp only [hbk, Option.isSome_some, ↓reduceIte] at hpc
    rw [hbk] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 2) (bs := bs) hlen
    have hadd := bv_add_ofNat_comm s1 (bytesField 2 (some bs)).length
    have hP2 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ g.bk.cap) ∗ ((a + 32#64) ↦₆₄ g.bk.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.bk.cap g.bk.ptr bs ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hbk, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP2]
    apply sepWPp_of_sepWP_vm (mid := if m.identityKey.isSome then (blkPl_119).base + 112#64 else (blkPl_119).base + 188#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by cases m.identityKey <;> simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP2]
      exact hnext _ hvm (by cases m.identityKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f3_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s12 : Nat)
    (hfit : s12 + (bytesField 3 m.identityKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.identityKey.isSome then (blkPl_119).base + 112#64 else (blkPl_119).base + 188#64))
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_119).base + 196#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12 + (bytesField 3 m.identityKey).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hik : m.identityKey with
  | none =>
    simp only [hik, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 196#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      exact ⟨by simp_all, fun hvm => hnext _ hvm (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [bytesField]) (by simp_all [EncLenCalleeSaved])⟩
  | some bs =>
    simp only [hik, Option.isSome_some, ↓reduceIte] at hpc
    rw [hik] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 3) (bs := bs) hlen
    have hcc := ule_ofNat_add_of_lt hfit
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12 (bytesField 3 (some bs)).length
    have hP3 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ g.ik.cap) ∗ ((a + 56#64) ↦₆₄ g.ik.ptr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.ik.cap g.ik.ptr bs ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hik, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP3]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 196#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP3]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f4_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s123 : Nat)
    (hmsg_beq : (optVecCap g.msg m.message + 1#64 == 0#64) = !m.message.isSome)
    (hfit : s123 + (bytesField 4 m.message).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 196#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_119).base + 260#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123 + (bytesField 4 m.message).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hmsg : m.message with
  | none =>
    have hP4 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ noneCap) ∗ optVecPayload A g.msg (a + 72#64) none ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hmsg, optVecCap]
    rw [hP4]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 260#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP4]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [bytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hmsg_beq' : (g.msg.cap + 1#64 == 0#64) = false := by
      rwa [hmsg, Option.isSome_some, Bool.not_true, optVecCap] at hmsg_beq
    rw [hmsg] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 4) (bs := bs) hlen
    have hcc := ule_ofNat_add_of_lt hfit
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123 (bytesField 4 (some bs)).length
    have hP4 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ g.msg.cap) ∗ ((a + 80#64) ↦₆₄ g.msg.ptr) ∗
        ((a + 88#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.msg.cap g.msg.ptr bs ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hmsg, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP4]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 260#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP4]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f5_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s1234 : Nat)
    (hfit : s1234 + (uint32Field 5 m.registrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 260#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_119).base + 320#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1234 + (uint32Field 5 m.registrationId).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hreg : m.registrationId with
  | none =>
    have hP5 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 96#64) none ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hreg]
    rw [hP5]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 320#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP5]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hreg] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 5) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234 (uint32Field 5 (some v)).length
    have hP5 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ 1#32) ∗ ((a + 100#64) ↦₃₂ v) ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hreg, optU32Tag, optU32Payload, arm64_norm]
    rw [hP5]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 320#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP5]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f6_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s12345 : Nat)
    (hfit : s12345 + (uint32Field 6 m.signedPreKeyId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 320#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12345)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_119).base + 380#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12345 + (uint32Field 6 m.signedPreKeyId).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hspk : m.signedPreKeyId with
  | none =>
    have hP6 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 112#64) none ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hspk]
    rw [hP6]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 380#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP6]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hspk] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 6) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12345 (uint32Field 6 (some v)).length
    have hP6 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ 1#32) ∗ ((a + 116#64) ↦₃₂ v) ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hspk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP6]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 380#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP6]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f7_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s123456 : Nat)
    (hfit : s123456 + (uint32Field 7 m.kyberPreKeyId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 380#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123456)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = (blkPl_119).base + 440#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123456 + (uint32Field 7 m.kyberPreKeyId).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hkpk : m.kyberPreKeyId with
  | none =>
    have hP7 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 120#64) none := by
      simp only [wirePreKeyMsgUnpacked, hkpk]
    rw [hP7]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 440#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP7]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all [uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hkpk] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 7) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123456 (uint32Field 7 (some v)).length
    have hP7 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ 1#32) ∗ ((a + 124#64) ↦₃₂ v) := by
      simp only [wirePreKeyMsgUnpacked, hkpk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP7]
    apply sepWPp_of_sepWP_vm (mid := (blkPl_119).base + 440#64)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP7]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f8_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a sp fp_val lr_val : BitVec 64)
    (m : ProtoPreKeySignalMessage) (s1234567 : Nat)
    (hkyber_beq : (optVecCap g.kyberCt m.kyberCiphertext + 1#64 == 0#64) = !m.kyberCiphertext.isSome)
    (hfit : s1234567 + (bytesField 8 m.kyberCiphertext).length < 2 ^ 64)
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 440#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234567)
    (hP : P = (wirePreKeyMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ fp_val) ∗ ((sp - 8#64) ↦₆₄ lr_val)) ∗ F)
    (hnext : ∀ sm : State,
      VmPreserved s sm →
      sm.pc = lr_val → sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (s1234567 + (bytesField 8 m.kyberCiphertext).length) →
      sm.readReg64 .fp = fp_val → sm.readReg64 .lr = lr_val →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) lr_val sm P Q Qp) :
    SepWPp (lsProg_119 H) lr_val s P Q Qp := by
  subst hP
  cases hkyber : m.kyberCiphertext with
  | none =>
    have hP8 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ noneCap) ∗ optVecPayload A g.kyberCt a none ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hkyber, optVecCap]
    rw [hP8]
    apply sepWPp_of_sepWP_vm (mid := lr_val)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP8]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all [bytesField]) (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hkyber_beq' : (g.kyberCt.cap + 1#64 == 0#64) = false := by
      rwa [hkyber, Option.isSome_some, Bool.not_true, optVecCap] at hkyber_beq
    rw [hkyber] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 8) (bs := bs) hlen
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234567 (bytesField 8 (some bs)).length
    have hP8 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ g.kyberCt.cap) ∗ ((a + 8#64) ↦₆₄ g.kyberCt.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.kyberCt.cap g.kyberCt.ptr bs ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hkyber, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP8]
    apply sepWPp_of_sepWP_vm (mid := lr_val)
    by_vm_steps
      wp_steps
      apply SepWP.done (by simp_all) (by simp_all)
      refine ⟨by simp_all, fun hvm => ?_⟩
      rw [← hP8]
      exact hnext _ hvm (by simp_all) (by simp_all) (by simp_all) (by simp_all)
        (by simp_all) (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

/-- Relocatable `PreKeySignalMessage::encoded_len` (block `119`) satisfies
`PreKeyMsgEncodedLenPlacedOk A H`. -/
theorem preKeyMsgEncodedLen_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} :
    PreKeyMsgEncodedLenPlacedOk A H := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  simp only [preKeyMsgEncodedLenSpec, withVmPreserved,
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split.preKeyMsgEncodedLenSpec,
    wirePreKeySignalMessageAt_eq_unpacked, stackAt_16_eq] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfits⟩, hpre⟩
  have hpre_ex : s0.mem ⊨
      (∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗ R) := by
    convert hpre using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre_ex
  rcases hpre_ex with ⟨v16, hpre_ex⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre_ex
  rcases hpre_ex with ⟨v8, hpre_ex⟩
  have hpre' : s0.mem ⊨
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre_ex using 1; sep_ac_rfl
  have hbounds_mem : s0.mem ⊨ wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      (((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) := by
    convert hpre' using 1; sep_ac_rfl
  obtain ⟨⟨hkyber_beq, _⟩, ⟨hbk_beq, hbk_bne⟩, ⟨hik_beq, hik_bne⟩, ⟨hmsg_beq, _⟩⟩ :=
    wirePreKeyMsgUnpacked_bounds hbounds_mem
  have hlen_eq := preKeyMsg_encode_length_eq x.m
  have hfits' : x.m.encode.length < 2 ^ 64 := hfits
  rw [hlen_eq] at hfits'
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hsp_align
  refine ⟨(wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ emp, R,
      by simpa [sepConj_emp] using hpre', ?_⟩
  apply step_encLen_f1_placed A H x.g x.a s0.sp v16 v8 x.m
    hbk_beq hbk_bne hpc hrun rfl halign hx0 rfl
  intro s1 hvm1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  apply SepWPp.congr_pre (show (wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ emp =
      wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) by
    simp [sepConj_emp, sepConj_assoc])
  apply step_encLen_f2_placed A H x.g x.a x.m
    (uint32Field 1 x.m.preKeyId).length hik_beq hik_bne (by omega)
    hpc1 hrun1 hx0_1 hx8_1 rfl
  intro s2 hvm2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
  apply step_encLen_f3_placed A H x.g x.a x.m
    ((uint32Field 1 x.m.preKeyId).length + (bytesField 2 x.m.baseKey).length)
    (by omega) hpc2 hrun2 hx0_2 hx8_2 rfl
  intro s3 hvm3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
  apply step_encLen_f4_placed A H x.g x.a x.m
    ((uint32Field 1 x.m.preKeyId).length + (bytesField 2 x.m.baseKey).length +
      (bytesField 3 x.m.identityKey).length)
    hmsg_beq (by omega) hpc3 hrun3 hx0_3 hx8_3 rfl
  intro s4 hvm4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
  apply step_encLen_f5_placed A H x.g x.a x.m
    ((uint32Field 1 x.m.preKeyId).length + (bytesField 2 x.m.baseKey).length +
      (bytesField 3 x.m.identityKey).length + (bytesField 4 x.m.message).length)
    (by omega) hpc4 hrun4 hx0_4 hx8_4 rfl
  intro s5 hvm5 hpc5 hrun5 hsp5 htr5 hx0_5 hx8_5 hcs5
  apply step_encLen_f6_placed A H x.g x.a x.m
    ((uint32Field 1 x.m.preKeyId).length + (bytesField 2 x.m.baseKey).length +
      (bytesField 3 x.m.identityKey).length + (bytesField 4 x.m.message).length +
      (uint32Field 5 x.m.registrationId).length)
    (by omega) hpc5 hrun5 hx0_5 hx8_5 rfl
  intro s6 hvm6 hpc6 hrun6 hsp6 htr6 hx0_6 hx8_6 hcs6
  apply step_encLen_f7_placed A H x.g x.a x.m
    ((uint32Field 1 x.m.preKeyId).length + (bytesField 2 x.m.baseKey).length +
      (bytesField 3 x.m.identityKey).length + (bytesField 4 x.m.message).length +
      (uint32Field 5 x.m.registrationId).length +
      (uint32Field 6 x.m.signedPreKeyId).length)
    (by omega) hpc6 hrun6 hx0_6 hx8_6 rfl
  intro s7 hvm7 hpc7 hrun7 hsp7 htr7 hx0_7 hx8_7 hcs7
  apply step_encLen_f8_placed A H x.g x.a s0.sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) x.m
    ((uint32Field 1 x.m.preKeyId).length + (bytesField 2 x.m.baseKey).length +
      (bytesField 3 x.m.identityKey).length + (bytesField 4 x.m.message).length +
      (uint32Field 5 x.m.registrationId).length +
      (uint32Field 6 x.m.signedPreKeyId).length +
      (uint32Field 7 x.m.kyberPreKeyId).length)
    hkyber_beq (by omega) hpc7 hrun7 (by reg_chain)
    halign hx0_7 hx8_7 (F := emp) (by simp [sepConj_emp, sepConj_assoc])
  intro sf hvm8 hpcf hrunf hspf htrf hx0_f hfpf hlrf hcs8
  have hvm_tot : VmPreserved s0 sf :=
    hvm1.trans (hvm2.trans (hvm3.trans (hvm4.trans (hvm5.trans (hvm6.trans (hvm7.trans hvm8))))))
  apply SepWPp.done hpcf hrunf
  refine ⟨?_, hspf, by reg_chain⟩
  intro hmf
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm_tot, ?_⟩
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨by rw [hx0_f, ← hlen_eq], by reg_chain⟩, ?_⟩
  have hmf' : sf.mem ⊨
      (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗ R) := by
    convert hmf using 1; sep_ac_rfl
  have hent : (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ⊢
      (∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64, ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) :=
    Entails.sepExists_right (s0.readReg64 .fp)
      (Entails.sepExists_right (s0.readReg64 .lr) (Entails.refl _))
  have hmf'' := Satisfies.mono (sepConj_mono_left hent) hmf'
  convert hmf'' using 1; sep_ac_rfl

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPfBudget
