/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.SplitBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded `PreKeySignalMessage::new` `sret` Stores and Dealloc Hook

Relocatable `[LibsignalPlacement]` `sret`-packing step (`+0x4c4..+0x580` on block `41`) with
`VmPreserved` and `subroutine_ok` projection for `rustCliDeallocBudgetSpec M A lim`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (sepWP_rebase_vmPreserved trapHooks
   vmPreserved_refl_iff vmPreserved_setPC vmPreserved_advancePC vmPreserved_setPState
   vmPreserved_writeReg64 vmPreserved_writeReg32 vmPreserved_writeReg
   vmPreserved_writeVReg128 vmPreserved_writeVReg64 vmPreserved_writeVReg32
   vmPreserved_applyWriteback vmPreserved_setStatus vmPreserved_appendTrace
   vmPreserved_setFs vmPreserved_stepExclLoop tpidrEl0_applyWriteback)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement lsRustDeallocSym ls_hook_ok_of_mem lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap signalMessageAt)
open CryptoVerification.LibsignalPublicApiRepr
  (PreKeyMsgGhost optKyberAt preKeyMsgAt)
open CryptoVerification.LibsignalPublicApi.Placed (lsProg_41 blkPC_41 blkPl_41)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
  (PreKeyMsgFrameGhost vecU8AtLen)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
  (kyberWords3At msgWords15At vecU8AtLen_exact_eq_boxU8Buf
   kyberWords3At_entails_memRegion msgWords15At_entails_memRegion
   sret_cells_entails_preKeyMsgAt sepWP_elim_optKyberAt sepWP_elim_signalMessageAt
   sepWP_elim_sret_248 entails_replace3_left)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem preKeyMsg_sret_stores_wp_placed [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (x : PreKeyMsgNewCall) (g : PreKeyMsgFrameGhost) (sp0 lenW : BitVec 64)
    (hser_bound : x.model.serialized.length < 2 ^ 42)
    (hver : g.ver32.setWidth 8 = x.ver)
    (hpre : ∀ v, x.preKeyId = some v → g.preKeyVal32 = v)
    (s : State)
    (hpc : s.pc = (blkPl_41).base + 1220#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 368#64)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = x.bkA)
    (hx19 : s.readReg64 .x19 =
      match x.kp with
      | none => noneCap
      | some k => BitVec.ofNat 64 k.ciphertext.length)
    (hx20 : (s.readReg64 .x20).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32))
    (hx21 : (s.readReg64 .x21).setWidth 32 = x.spk)
    (hx22 : s.readReg64 .x22 = 33#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 x.model.serialized.length)
    (hx24 : s.readReg64 .x24 = 33#64)
    (hx25 : (s.readReg64 .x25).setWidth 32 = g.preKeyVal32)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.model.serialized.length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length)
    (hx28 : s.readReg64 .x28 = g.bkSerPtr)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWP (lsProg_41 H)
      (if (match x.kp with
           | none => noneCap
           | some k => BitVec.ofNat 64 k.ciphertext.length).slt 1#64 then
        (blkPl_41).base + 1428#64
       else
        (blkPl_41).base + 1412#64)
      s
      (optKyberAt A x.kyA x.kyPtr x.kp ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗
       memRegion x.ret 248 ∗
       ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
       ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
       ((sp0 - 344#64) ↦₃₂ x.regId) ∗
       ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
       ((sp0 - 304#64) ↦₆₄ x.ret) ∗
       ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
       ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
       vecU8AtLen A (sp0 - 144#64) (BitVec.ofNat 64 x.model.serialized.length) g.serPtr lenW
         x.model.serialized ∗
       (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
       (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))
      (fun sm Pm =>
        VmPreserved s sm ∧
        (sm.sp = sp0 - 368#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 =
           (match x.kp with
            | none => noneCap
            | some k => BitVec.ofNat 64 k.ciphertext.length) ∧
         sm.readReg64 .x20 = g.msgCopyPtr ∧
         sm.readReg64 .x22 = 33#64 ∧
         sm.readReg64 .x24 = 33#64 ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.msg.serialized.length ∧
         sm.readReg64 .x28 = g.bkSerPtr ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         sm.trace = s.trace ∧
         calleeSavedVRegs sm = calleeSavedVRegs s) ∧
        (Pm ⊢
          memRegion x.kyA 24 ∗
          memRegion x.msgA 120 ∗
          (∃∗ g' : PreKeyMsgGhost, preKeyMsgAt A g' x.ret x.model) ∗
          ((sp0 - 368#64) ↦₆₄ g.msgCopyPtr) ∗
          ((sp0 - 360#64) ↦₆₄ x.ikA) ∗
          ((sp0 - 344#64) ↦₃₂ x.regId) ∗
          ((sp0 - 332#64) ↦₃₂ g.ver32) ∗
          ((sp0 - 304#64) ↦₆₄ x.ret) ∗
          ((sp0 - 288#64) ↦₆₄ x.msgA) ∗
          ((sp0 - 280#64) ↦₆₄ x.kyA) ∗
          ((sp0 - 144#64) ↦₆₄ BitVec.ofNat 64 x.model.serialized.length) ∗
          ((sp0 - 136#64) ↦₆₄ g.serPtr) ∗
          ((sp0 - 128#64) ↦₆₄ lenW) ∗
          (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
          (x.ikA ↦ₛ x.ik.publicKey.bytes.toList))) := by
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.msg.senderRatchetKey.bytes)
  obtain ⟨bk0, bk1, bk2, bk3, _, hbk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.baseKey.bytes)
  obtain ⟨ik0, ik1, ik2, ik3, _, hik⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.ik.publicKey.bytes)
  refine sepWP_elim_optKyberAt fun ky0 ky1 ky2 => ?_
  wp_conv_pre => rw [sepConj_assoc]
  refine sepWP_elim_signalMessageAt hrk fun addrW0 addrW1 verHi56 => ?_
  wp_conv_pre => rw [sepConj_assoc, sepConj_assoc]
  refine sepWP_elim_sret_248 fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 p0 p1
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 u0 u1 b0 => ?_
  wp_conv_pre =>
    rw [vecU8AtLen_exact_eq_boxU8Buf A (sp0 - 144#64) g.serPtr lenW x.model.serialized (by omega),
        hbk x.bkA, hik x.ikA]
    simp only [kyberWords3At, msgWords15At, sepConj_assoc, arm64_norm]
  by_vm_steps
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      ⟨by simp only [wp_norm, arm64_norm, *], ?_, ?_⟩
    · refine ⟨by simp only [wp_norm, arm64_norm, *],
        by simpa [State.spAligned, arm64_norm] using hsp_align,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
    · have hky_mem := kyberWords3At_entails_memRegion x.kyA ky0 ky1 ky2
      simp only [kyberWords3At, arm64_norm] at hky_mem
      have hmsg_mem := msgWords15At_entails_memRegion x.msgA
        x.msgG.pqCap x.msgG.pqPtr (BitVec.ofNat 64 x.msg.pqRatchet.length)
        x.msgG.ctPtr (BitVec.ofNat 64 x.msg.ciphertext.length)
        x.msgG.serPtr (BitVec.ofNat 64 x.msg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (x.msg.previousCounter ++ x.msg.counter) (verHi56 ++ x.msg.messageVersion)
      simp only [msgWords15At, arm64_norm] at hmsg_mem
      have hsret := sret_cells_entails_preKeyMsgAt A x g
        rk0 rk1 rk2 rk3 addrW0 addrW1 ky0 ky1 ky2 bk0 bk1 bk2 bk3 ik0 ik1 ik2 ik3 verHi56
        hpre hrk hbk hik
      simp only [msgWords15At, kyberWords3At, Option.isSome, sepConj_assoc, arm64_norm] at hsret
      rw [hbk x.bkA, hik x.ikA]
      exact entails_replace3_left hky_mem hmsg_mem hsret
        (by (conv => rhs; arg 1; simp only [sepConj_assoc]); sep_focus)

theorem preKeyMsg_dealloc_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_41 H) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  ls_hook_ok_of_mem (prog := lsProg_41 H) (sym := lsRustDeallocSym) hdealloc

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueBudget
