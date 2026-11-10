/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtEncryptBody
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSignalMsgNewSeg1
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSignalMsgNewSeg2
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtSignalMsgNewSeg3
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt
import LibsignalBinary.Proofs.TripleRatchet.Wire.New
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewMacAndBoxes

/-!
# Stacked `<SignalMessage>::new` on `tripleRatchetProgAtExt`

Proves `SignalMessageNewOkExt32` (`17840` B stack) on `tripleRatchetProgAtExt img.base ext` under
`AllocContractsX`, `AllocContracts4K`, and stacked `SignalMessage::compute_mac`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNew

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.Cli.LibsignalSpqrV1.M4
open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? _root_.Arm64.Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack-Frame Splits -/

theorem stackAt_17424_to_4624 (sp : BitVec 64) :
    stackAt sp Statements.computeMacStackExt32 =
      stackAt sp computeMacStack ∗ memRegion (sp - 17424#64) 12800 := by
  simp only [stackAt, Statements.computeMacStackExt32, Statements.computeMacPkStackExt32,
    newFromSliceStack, extHookStack, computeMacStack, publicKeySerializeStack, allocHookStack]
  rw [show (544 + 2 ^ 14 + 496 : Nat) = 12800 + (4096 + 32 + 496) by decide,
    ProofLib.memRegion_split _ 12800 (4096 + 32 + 496) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (12800 + (4096 + 32 + 496)) = sp - 17424#64 := by bv_arith
  have e2 : sp - 17424#64 + BitVec.ofNat 64 12800 = sp - BitVec.ofNat 64 (4096 + 32 + 496) := by
    bv_arith
  rw [e1, e2, sepConj_comm]

theorem stackAt_17424_to_16912 (sp : BitVec 64) :
    stackAt sp Statements.computeMacStackExt32 =
      stackAt sp computeMacStackX ∗ memRegion (sp - 17424#64) 512 := by
  simp only [stackAt, Statements.computeMacStackExt32, Statements.computeMacPkStackExt32,
    newFromSliceStack, extHookStack, computeMacStackX, publicKeySerializeStackX]
  rw [show (544 + 2 ^ 14 + 496 : Nat) = 512 + (2 ^ 14 + 32 + 496) by decide,
    ProofLib.memRegion_split _ 512 (2 ^ 14 + 32 + 496) (by decide)]
  have e1 : sp - BitVec.ofNat 64 (512 + (2 ^ 14 + 32 + 496)) = sp - 17424#64 := by bv_arith
  have e2 : sp - 17424#64 + BitVec.ofNat 64 512 = sp - BitVec.ofNat 64 (2 ^ 14 + 32 + 496) := by
    bv_arith
  rw [e1, e2, sepConj_comm]

theorem stackAt_17840_to_17328 (sp0 : BitVec 64) :
    stackAt sp0 ExtEncryptBody.signalMessageNewStackExt32 =
      stackAt sp0 signalMessageNewStackX ∗ memRegion ((sp0 - 416#64) - 17424#64) 512 := by
  simp only [stackAt, ExtEncryptBody.signalMessageNewStackExt32, Statements.computeMacStackExt32,
    Statements.computeMacPkStackExt32, newFromSliceStack, extHookStack,
    signalMessageNewStackX, computeMacStackX, publicKeySerializeStackX]
  rw [show (544 + 2 ^ 14 + 496 + 416 : Nat) = 512 + (2 ^ 14 + 32 + 496 + 416) by decide,
    ProofLib.memRegion_split _ 512 (2 ^ 14 + 32 + 496 + 416) (by decide)]
  have e1 : sp0 - BitVec.ofNat 64 (512 + (2 ^ 14 + 32 + 496 + 416)) =
      (sp0 - 416#64) - 17424#64 := by bv_arith
  have e2 : (sp0 - 416#64) - 17424#64 + BitVec.ofNat 64 512 =
      sp0 - BitVec.ofNat 64 (2 ^ 14 + 32 + 496 + 416) := by bv_arith
  rw [e1, e2, sepConj_comm]

theorem stackAt_signalMessageNewStackExt32_ready (sp0 : BitVec 64) :
    stackAt sp0 ExtEncryptBody.signalMessageNewStackExt32 =
      (∃∗ w408 : BitVec 64, ∃∗ w400 : BitVec 64, ∃∗ w392 : BitVec 64,
       ∃∗ w384 : BitVec 32, ∃∗ w380 : BitVec 32,
       ∃∗ w376 : BitVec 64, ∃∗ w368 : BitVec 64, ∃∗ w360 : BitVec 64,
       ∃∗ w352 : BitVec 64, ∃∗ w344 : BitVec 64,
       ∃∗ w332 : BitVec 32,
       ∃∗ w328 : BitVec 64, ∃∗ w320 : BitVec 64,
       ∃∗ w176 : BitVec 64, ∃∗ w168 : BitVec 64, ∃∗ w160 : BitVec 64,
        stackAt (sp0 - 416#64) Statements.computeMacStackExt32 ∗
        newUnusedPad sp0 ∗
        ((sp0 - 408#64) ↦₆₄ w408) ∗
        ((sp0 - 400#64) ↦₆₄ w400) ∗
        ((sp0 - 392#64) ↦₆₄ w392) ∗
        ((sp0 - 384#64) ↦₃₂ w384) ∗
        ((sp0 - 380#64) ↦₃₂ w380) ∗
        ((sp0 - 376#64) ↦₆₄ w376) ∗
        ((sp0 - 368#64) ↦₆₄ w368) ∗
        ((sp0 - 360#64) ↦₆₄ w360) ∗
        ((sp0 - 352#64) ↦₆₄ w352) ∗
        ((sp0 - 344#64) ↦₆₄ w344) ∗
        ((sp0 - 332#64) ↦₃₂ w332) ∗
        ((sp0 - 328#64) ↦₆₄ w328) ∗
        ((sp0 - 320#64) ↦₆₄ w320) ∗
        memRegion (sp0 - 312#64) 24 ∗
        memRegion (sp0 - 288#64) 112 ∗
        ((sp0 - 176#64) ↦₆₄ w176) ∗
        ((sp0 - 168#64) ↦₆₄ w168) ∗
        ((sp0 - 160#64) ↦₆₄ w160) ∗
        memRegion (sp0 - 152#64) 16 ∗
        cells (sp0 - 96#64) 12) := by
  rw [stackAt_17840_to_17328 sp0, stackAt_signalMessageNewStackX_ready sp0]
  simp only [sepExists_sepConj_left]
  refine congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ =>
    congrArg sepExists (funext fun _ => congrArg sepExists (funext fun _ => ?_))))))))))))))))
  rw [stackAt_17424_to_16912 (sp0 - 416#64)]
  ac_rfl

/-! ## Combined Phase 3 (`+0x3dc → lr`) -/

theorem new_phase3_wpp_ext32 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAX : AllocContractsX img A ext)
    (hA4K : AllocContracts4K img.base A ext)
    (hMac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((Mac.VerifyMacWithAddresses.computeMacSpecWithStack C.F A Statements.computeMacStackExt32).inImage img))
    (x : SignalMessageNewGhost)
    (sp0 serPtr rkPtr ctCopyPtr pqCap pqCopyPtr addrCap : BitVec 64)
    (verW32 : BitVec 32)
    (hver : verW32.setWidth 8 = x.messageVersion)
    (haddrCap : addrCap = if (x.addresses uuidTryParse).isSome then 36#64 else noneCap)
    (hct_bound : x.ciphertext.length ≤ 2 ^ 32)
    (hpq_bound : x.pqRatchet.length < 2 ^ 32)
    (s0 s : State)
    (hF : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signalMessageNewName + 988#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp0 : s0.sp = sp0)
    (hsp0_align : s0.spAligned = true)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = 32#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = addrCap)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (x.serPrefix6 uuidTryParse).length)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64)
    (htr : TraceVRegsEq s s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .lr)
      s
      (newUnusedPad sp0 ∗
       ((sp0 - 408#64) ↦₆₄ rkPtr) ∗
       ((sp0 - 400#64) ↦₆₄ x.ciphertextA) ∗
       ((sp0 - 392#64) ↦₆₄ pqCopyPtr) ∗
       ((sp0 - 384#64) ↦₃₂ x.counter) ∗
       ((sp0 - 380#64) ↦₃₂ x.previousCounter) ∗
       ((sp0 - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
       ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
       ((sp0 - 344#64) ↦₆₄ ctCopyPtr) ∗
       ((sp0 - 332#64) ↦₃₂ verW32) ∗
       ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 - 320#64) ↦₆₄ pqCap) ∗
       memRegion (sp0 - 312#64) 24 ∗
       cells (sp0 - 288#64) 9 ∗
       optSerializeAddressesAt A (sp0 - 216#64) (x.addresses uuidTryParse) ∗
       (∃∗ w192 : BitVec 32, (sp0 - 192#64) ↦₃₂ w192) ∗
       (∃∗ w188 : BitVec 32, (sp0 - 188#64) ↦₃₂ w188) ∗
       (∃∗ w184 : BitVec 32, (sp0 - 184#64) ↦₃₂ w184) ∗
       (∃∗ w180 : BitVec 32, (sp0 - 180#64) ↦₃₂ w180) ∗
       vecU8At A (sp0 - 176#64)
         (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
         serPtr (x.serPrefix6 uuidTryParse) ∗
       memRegion (sp0 - 152#64) 16 ∗
       newSavedRegs sp0 s0 ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
       (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
       (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
       (x.ciphertextA ↦ₛ x.ciphertext) ∗
       (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
       boxU8Buf A rkPtr x.senderRatchetKey.serialize ∗
       boxU8Buf A ctCopyPtr x.ciphertext ∗
       optPqBuf A pqCap pqCopyPtr x.pqRatchet ∗
       memRegion x.ret 120 ∗
       A.pool ∗
       stackAt (sp0 - 416#64) Statements.computeMacStackExt32)
      (fun sf Pf =>
        (sf.sp = s0.sp ∧
         CalleeSavedPreserved s0 sf ∧
         sf.trace = s0.trace) ∧
        (Pf ⊢
          (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
          (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
          (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
          (x.ciphertextA ↦ₛ x.ciphertext) ∗
          (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
          A.pool ∗
          stackAt s0.sp ExtEncryptBody.signalMessageNewStackExt32))
      (PanicAllocPost s0) := by
  refine signalMessageNew_seg3_seq_wpp_inImage' htr hF hsym
    (ExtSignalMsgNewSeg3.new_compute_mac_and_append_wpp_ext32 hMac x sp0 serPtr addrCap
      hct_bound hpq_bound s hF hsym hpc hrun hsp hsp_align hx19 hx20 hx21 hx22 hx24 hx25 hx27 hx29)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, hsp_align1, hx19_1, hx21_1, hx22_1, hx24_1, hx26_1, hx27_1, hx28_1, hx29_1, htr1⟩
  have htr1' : TraceVRegsEq s1 s0 := htr1.trans htr
  conv => arg 4; rw [stackAt_17424_to_4624 (sp0 - 416#64)]; simp only [sepConj_assoc]
  refine signalMessageNew_seg3_seq_wpp_inImage' htr1' hF1 hsym1
    (ExtSignalMsgNewSeg3.new_ct_clone_wpp_4k hA4K x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      addrCap hct_bound s1 hpc1 hrun1 hsp1 hsp_align1 hx19_1 hx21_1 hx22_1 hx24_1 hx26_1
      hx27_1 hx28_1 hx29_1)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 hF2 hsym2 ⟨hsp2, hsp_align2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx27_2, hx28_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1'
  refine SepWPp.fold (Entails.of_eq (stackAt_17424_to_4624 (sp0 - 416#64)).symm) (by sep_focus) ?_
  conv => arg 4; rw [stackAt_17424_to_16912 (sp0 - 416#64)]; simp only [sepConj_assoc]
  refine signalMessageNew_seg3_seq_wpp_inImage' htr2' hF2 hsym2
    (new_pq_clone_wpp_ext_x hAX x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) addrCap hpq_bound s2 hF2 hsym2 hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx21_2
      hx22_2 hx24_2 rfl hx26_2 hx27_2 hx28_2 hx29_2)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, hsp_align3, hx19_3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine signalMessageNew_seg3_seq_wp_inImage' hF3 hsym3
    (new_addr_into_boxed_wp_ext x sp0 serPtr
      (BitVec.ofNat 64 (x.model C.F uuidTryParse).serialized.length)
      (s2.readReg64 .x25) (s3.readReg64 .x23) addrCap haddrCap s3 hpc3 hrun3 hsp3 hsp_align3
      hx19_3 hx21_3 hx22_3 rfl hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3)
    (by sep_focus) ?_
  intro s4 hpc4 hrun4 hF4 hsym4 ⟨hsp4, hsp_align4, hx19_4, hx21_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine signalMessageNew_seg3_seq_wp_inImage' hF4 hsym4
    (new_sret_stores_wp_ext x sp0 serPtr (s2.readReg64 .x25) (s3.readReg64 .x23)
      (s4.readReg64 .x0) (s4.readReg64 .x20) verW32 hver hct_bound hpq_bound s4
      hpc4 hrun4 hsp4 hsp_align4 rfl hx19_4 rfl hx21_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 hF5 hsym5 ⟨hsp5, hsp_align5, hx19_5, hx21_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  refine SepWPp.fold (Entails.of_eq (stackAt_17424_to_16912 (sp0 - 416#64)).symm) (by sep_focus) ?_
  conv => arg 4; rw [stackAt_17424_to_4624 (sp0 - 416#64)]; simp only [sepConj_assoc]
  refine signalMessageNew_seg3_seq_wpp_inImage' htr5' hF5 hsym5
    (ExtSignalMsgNewSeg3.new_dealloc_rk_and_ct_wpp_4k hA4K x sp0 rkPtr ctCopyPtr pqCopyPtr
      hct_bound s5 hpc5 hrun5 hsp5 hsp_align5 hx19_5 hx21_5 hx29_5)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s6 hpc6 hrun6 hF6 hsym6 ⟨hsp6, hsp_align6, hx20_6, _hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  refine SepWPp.fold (Entails.of_eq (stackAt_17424_to_4624 (sp0 - 416#64)).symm) (by sep_focus) ?_
  conv => arg 4; rw [stackAt_17424_to_16912 (sp0 - 416#64)]; simp only [sepConj_assoc]
  have hfr := entails_newFrameRest sp0 rkPtr ctCopyPtr pqCopyPtr
    x.counter x.previousCounter verW32
    x.ciphertextA x.senderRatchetKeyA x.senderIkA x.receiverIkA x.macKeyA x.pqRatchetA
  refine SepWPp.fold hfr (by sep_focus) ?_
  refine signalMessageNew_seg3_seq_wpp' htr6'
    (new_dealloc_pq_and_epilogue_wpp_ext_x hAX x sp0 pqCap pqCopyPtr hpq_bound s0 s6
      hF6 hsym6 hpc6 hrun6 hsp6 hsp0 hsp0_align hsp_align6 hx20_6 htr6')
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro sf hpcf hrunf ⟨hspf, hcsf, htrf⟩
  refine SepWPp.done hpcf hrunf ⟨⟨hspf, hcsf, htrf⟩, ?_⟩
  rw [hsp0, stackAt_17840_to_17328 sp0]
  exact NewMacAndBoxesCallees.entails_of_sep_focus (by sep_focus)

/-! ## Main Theorem (`signalMessageNew_ok_ext32`) -/

set_option maxHeartbeats 3200000 in
theorem signalMessageNew_ok_ext32 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAX : AllocContractsX img A ext)
    (hA4K : AllocContracts4K img.base A ext)
    (hMac : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((Mac.VerifyMacWithAddresses.computeMacSpecWithStack C.F A Statements.computeMacStackExt32).inImage img)) :
    ExtEncryptBody.SignalMessageNewOkExt32 img C A uuidTryParse ext := by
  have hEncLen : EncodedLenOkExt img.base A ext := Glue.encodedLenOk_ext img.base A ext
  have hVarint : EncodeVarintOkExt img.base A ext := ExtSignalMsgNewSeg1.encodeVarint_ok_4k hA4K
  apply signalMessageNew_subroutine_ok_of_sepWPp
    (Ppost := fun x s0 =>
      x.inputsAt A s0.sp ∗
      (∃∗ g : SignalMessageGhost, signalMessageAt A g x.ret (x.model C.F uuidTryParse)) ∗
      A.pool ∗ stackAt s0.sp ExtEncryptBody.signalMessageNewStackExt32)
    (fun x s0 sf htr => by
      simp only [Spec.inImage, ExtEncryptBody.signalMessageNewSpecExt32]
      exact Entails.pure_right htr (Entails.refl _))
    (fun _ _ _ => rfl)
  intro x s0 hpc hrun hsp_align
  simp only [Spec.inImage, ExtEncryptBody.signalMessageNewSpecExt32,
    SignalMessageNewGhost.inputsAt, sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hF0, hsym0⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hx8,
    hct_bound, hpq_bound⟩ => ?_
  conv =>
    arg 4
    rw [stackAt_signalMessageNewStackExt32_ready s0.sp]
    simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w408 => SepWPp.exists_elim fun w400 =>
    SepWPp.exists_elim fun w392 => SepWPp.exists_elim fun w384 =>
    SepWPp.exists_elim fun w380 => SepWPp.exists_elim fun w376 =>
    SepWPp.exists_elim fun w368 => SepWPp.exists_elim fun w360 =>
    SepWPp.exists_elim fun w352 => SepWPp.exists_elim fun w344 =>
    SepWPp.exists_elim fun w332 => SepWPp.exists_elim fun w328 =>
    SepWPp.exists_elim fun w320 => SepWPp.exists_elim fun w176 =>
    SepWPp.exists_elim fun w168 => SepWPp.exists_elim fun w160 => ?_
  refine signalMessageNew_seg3_seq_wp_inImage' hF0 hsym0
    (new_prologue_wp_ext x s0.sp w368 w360 w352 w344 w328 w332 s0
      hpc hrun rfl hsp_align hx1 hx2 hx4 hx5 hx6 hx7 hx8)
    (by sep_focus) ?_
  intro s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, hsp_align1, hx3_1, hx4_1, hx19_1, hx20_1, hx22_1, hx23_1,
    hx24_1, hx25_1, hx27_1, hx29_1, htr1⟩
  conv => arg 4; rw [stackAt_17424_to_16912 (s0.sp - 416#64)]; simp only [sepConj_assoc]
  refine signalMessageNew_seg3_seq_wpp_inImage' htr1 hF1 hsym1
    (ExtSignalMsgNewSeg1.new_addr_and_rk_wpp_ext_x hAX x s0.sp s1 hF1 hsym1
      hpc1 hrun1 hsp1 hsp_align1 (hx3_1.trans hx3) hloc_ne hx4_1 hx19_1 hx20_1
      hx22_1 hx23_1 hx24_1 hx25_1 hx27_1 hx29_1)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s2 hpc2 hrun2 hF2 hsym2 ⟨hsp2, hsp_align2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2,
    hx24_2, hx25_2, hx27_2, hx29_2, htr2⟩
  have htr2' : TraceVRegsEq s2 s0 := htr2.trans htr1
  refine SepWPp.fold (Entails.of_eq (stackAt_17424_to_16912 (s0.sp - 416#64)).symm) (by sep_focus) ?_
  conv => arg 4; rw [stackAt_17424_to_4624 (s0.sp - 416#64)]; simp only [sepConj_assoc]
  refine signalMessageNew_seg3_seq_wpp_inImage' htr2' hF2 hsym2
    (ExtSignalMsgNewSeg1.new_ct_copy_wpp_4k hA4K x s0.sp (s2.readReg64 .x28) w400 hct_bound s2
      hpc2 hrun2 hsp2 hsp_align2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2
      hx24_2 hx25_2 hx27_2 rfl hx29_2)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, hsp_align3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3,
    hx24_3, hx25_3, hx27_3, hx28_3, hx29_3, htr3⟩
  have htr3' : TraceVRegsEq s3 s0 := htr3.trans htr2'
  refine SepWPp.fold (Entails.of_eq (stackAt_17424_to_4624 (s0.sp - 416#64)).symm) (by sep_focus) ?_
  conv => arg 4; rw [stackAt_17424_to_16912 (s0.sp - 416#64)]; simp only [sepConj_assoc]
  refine signalMessageNew_seg3_seq_wpp_inImage' htr3' hF3 hsym3
    (new_pq_copy_wpp_ext_x hAX x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26) hpq_bound s3
      hF3 hsym3 hpc3 hrun3 hsp3 hsp_align3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3
      hx24_3 rfl hx27_3 hx28_3 hx29_3)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s4 hpc4 hrun4 hF4 hsym4 ⟨hsp4, hsp_align4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4,
    hx24_4, hx26_4, hx27_4, hx28_4, hx29_4, htr4⟩
  have htr4' : TraceVRegsEq s4 s0 := htr4.trans htr3'
  refine SepWPp.fold (Entails.of_eq (stackAt_17424_to_16912 (s0.sp - 416#64)).symm) (by sep_focus) ?_
  conv => arg 4; rw [stackAt_17424_to_4624 (s0.sp - 416#64)]; simp only [sepConj_assoc]
  refine SepWPp.fold (optSerializeAddressesAt_unpack A (s0.sp - 312#64) x) (by sep_focus) ?_
  conv =>
    arg 4
    simp (disch := decide) only [bv_sub_add_lit, Nat.reduceSub,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun addrCap => SepWPp.exists_elim fun addrPtr =>
    SepWPp.exists_elim fun addrLen => ?_
  refine SepWPp.fold (optPqBuf_extract_pin A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet)
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hpq_pin => ?_
  refine SepWPp.fold (optAddrBuf_extract_cap A addrCap addrPtr addrLen (x.addresses uuidTryParse))
    (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun haddrCap => ?_
  have hrk_buf :
      boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize =
        signalMessageNew_vecU8Buf A 33#64 (s2.readReg64 .x28) x.senderRatchetKey.serialize := by
    have hlen : x.senderRatchetKey.serialize.length = 33 :=
      publicKey_serialize_length x.senderRatchetKey
    have h := (vecU8Buf_eq_boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize (by omega)).symm
    rw [hlen] at h
    exact h
  rw [hrk_buf]
  refine signalMessageNew_seg3_seq_wp_inImage' hF4 hsym4
    (new_store_wire_wp_ext x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr addrLen w376 w320
      hct_bound s4 hpc4 hrun4 hsp4 hsp_align4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4
      hx24_4 rfl hx26_4 hx27_4 hx28_4 hx29_4 rfl)
    (by sep_focus) ?_
  intro s5 hpc5 hrun5 hF5 hsym5 ⟨hsp5, hsp_align5, hx0_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5,
    hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hx29_5, htr5⟩
  have htr5' : TraceVRegsEq s5 s0 := htr5.trans htr4'
  have hver32 : ((s0.readReg64 .x0).setWidth 32).setWidth 8 = x.messageVersion := by
    rw [← hx0]
    bv_kernel
  refine signalMessageNew_seg3_seq_wpp_inImage' htr5' hF5 hsym5
    (ExtSignalMsgNewSeg1.new_alloc_ser_wpp_4k hA4K hEncLen x s0.sp (s2.readReg64 .x28)
      (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr w176 w168 w160
      w384 w380 ((s0.readReg64 .x0).setWidth 32) hver32 hct_bound hpq_bound s5
      hpc5 hrun5 hsp5 hsp_align5 hx0_5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5
      hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s6 hpc6 hrun6 hF6 hsym6 ⟨hsp6, hsp_align6, hx19_6, hx20_6, hx21_6, hx22_6, _hx23_6,
    hx24_6, hx25_6, hx26_6, hx27_6, hx28_6, hx29_6, htr6⟩
  have htr6' : TraceVRegsEq s6 s0 := htr6.trans htr5'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr6' hF6 hsym6
    (ExtSignalMsgNewSeg1.new_encode_tag1_wpp_4k hA4K hVarint x s0.sp (s2.readReg64 .x28)
      (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr
      (s6.readReg64 .x22) hct_bound hpq_bound hx22_6 s6 hpc6 hrun6 hsp6 hsp_align6 hx19_6 hx20_6
      hx21_6 rfl hx24_6 hx25_6 hx26_6 hx27_6 hx28_6 hx29_6)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s7 hpc7 hrun7 hF7 hsym7 ⟨hsp7, hsp_align7, hx19_7, hx20_7, hx21_7, hx22_7, hx23_7,
    hx24_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, htr7⟩
  have htr7' : TraceVRegsEq s7 s0 := htr7.trans htr6'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr7' hF7 hsym7
    (new_encode_tag2_wpp_ext hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x25) (s6.readReg64 .x22) hct_bound hpq_bound hx22_6 s7
      hpc7 hrun7 hsp7 hsp_align7 hx19_7 hx20_7 hx21_7 hx22_7 hx23_7 hx24_7
      hx25_7 hx26_7 hx27_7 hx28_7 hx29_7)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s8 hpc8 hrun8 hF8 hsym8 ⟨hsp8, hsp_align8, hx19_8, hx21_8, hx23_8, hx24_8, hx25_8,
    hx26_8, hx27_8, hx28_8, hx29_8, htr8⟩
  have htr8' : TraceVRegsEq s8 s0 := htr8.trans htr7'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr8' hF8 hsym8
    (new_encode_tag3_wpp_ext hVarint x s0.sp (s2.readReg64 .x28) (s3.readReg64 .x26)
      (s4.readReg64 .x9) (s4.readReg64 .x25) (s6.readReg64 .x22)
      hct_bound hpq_bound hx22_6 s8 hpc8 hrun8 hsp8 hsp_align8 hx19_8 hx21_8
      hx23_8 hx24_8 hx25_8 hx26_8 hx27_8 hx28_8 hx29_8)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s9 hpc9 hrun9 hF9 hsym9 ⟨hsp9, hsp_align9, hx19_9, hx20_9, hx21_9, hx23_9, hx24_9,
    hx25_9, hx26_9, hx27_9, hx28_9, hx29_9, htr9⟩
  have htr9' : TraceVRegsEq s9 s0 := htr9.trans htr8'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr9' hF9 hsym9
    (ExtSignalMsgNewSeg2.new_encode_tag4_wpp_4k hA4K hVarint x s0.sp (s2.readReg64 .x28)
      (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr
      (s6.readReg64 .x22) w392 hct_bound hpq_bound hx22_6 s9 hpc9 hrun9 hsp9 hsp_align9
      hx19_9 hx20_9 hx21_9 hx23_9 hx24_9 hx25_9 hx26_9 hx27_9 hx28_9 hx29_9)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s10 hpc10 hrun10 hF10 hsym10 ⟨hsp10, hsp_align10, hx19_10, hx20_10, hx21_10, hx23_10,
    hx24_10, hx25_10, hx26_10, hx27_10, hx28_10, hx29_10, htr10⟩
  have htr10' : TraceVRegsEq s10 s0 := htr10.trans htr9'
  refine signalMessageNew_seg3_seq_wpp_inImage' htr10' hF10 hsym10
    (ExtSignalMsgNewSeg2.new_encode_tag56_wpp_4k hA4K hVarint x s0.sp (s2.readReg64 .x28)
      (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr
      (s6.readReg64 .x22) w408 hct_bound hpq_bound hx22_6 hpq_pin haddrCap s10 hpc10 hrun10 hsp10
      hsp_align10 hx19_10 hx20_10 hx21_10 hx23_10 hx24_10 hx25_10 hx26_10 hx27_10 hx28_10 hx29_10)
    (by sep_focus)
    (fun _ _ hp => panicAllocPost_of_eq hp) ?_
  intro s11 hpc11 hrun11 hF11 hsym11 ⟨hsp11, hsp_align11, hx19_11, hx20_11, hx21_11, hx22_11,
    _hx23_11, hx24_11, hx25_11, hx27_11, hx29_11, htr11⟩
  have htr11' : TraceVRegsEq s11 s0 := htr11.trans htr10'
  refine SepWPp.fold (Entails.of_eq (stackAt_17424_to_4624 (s0.sp - 416#64)).symm) (by sep_focus) ?_
  refine SepWPp.fold
    (wireSignalMessageAt_unpack_for_phase3 A x s0.sp (s2.readReg64 .x28)
      (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap addrPtr
      hct_bound hpq_pin haddrCap)
    (by sep_focus) ?_
  rw [show (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 9 =
      1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8 by omega]
  simp only [sepConj_assoc]
  have hstep8 := new_phase3_wpp_ext32 hAX hA4K hMac x s0.sp (s6.readReg64 .x22)
    (s2.readReg64 .x28) (s3.readReg64 .x26) (s4.readReg64 .x9) (s4.readReg64 .x25) addrCap
    ((s0.readReg64 .x0).setWidth 32) hver32 haddrCap hct_bound hpq_bound
    s0 s11 hF11 hsym11 hpc11 hrun11 hsp11 rfl hsp_align hsp_align11
    hx19_11 hx20_11 hx21_11 hx22_11 hx24_11 hx25_11 hx27_11 hx29_11 htr11'
  have hfocus :
      (cells (s0.sp - 288#64) 9 ∗
        optSerializeAddressesAt A (s0.sp - 216#64) (x.addresses uuidTryParse) ∗
        (∃∗ w192 : BitVec 32, (s0.sp - 192#64) ↦₃₂ w192) ∗
        (∃∗ w188 : BitVec 32, (s0.sp - 188#64) ↦₃₂ w188) ∗
        (∃∗ w184 : BitVec 32, (s0.sp - 184#64) ↦₃₂ w184) ∗
        (∃∗ w180 : BitVec 32, (s0.sp - 180#64) ↦₃₂ w180) ∗
        boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize ∗
        boxU8Buf A (s3.readReg64 .x26) x.ciphertext ∗
        optPqBuf A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet ∗
        stackAt (s0.sp - 416#64) Statements.computeMacStackExt32 ∗
        ((s0.sp - 408#64) ↦₆₄ s2.readReg64 .x28) ∗
        ((s0.sp - 392#64) ↦₆₄ s4.readReg64 .x25) ∗
        ((s0.sp - 344#64) ↦₆₄ s3.readReg64 .x26) ∗
        vecU8At A (s0.sp - 176#64)
          (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
          (s6.readReg64 .x22) (x.serPrefix6 uuidTryParse) ∗
        A.pool ∗
        ((s0.sp - 320#64) ↦₆₄ s4.readReg64 .x9) ∗
        ((s0.sp - 384#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗
        ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
        ((s0.sp - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
        memRegion (s0.sp - 312#64) 24 ∗
        ((s0.sp - 328#64) ↦₆₄ x.pqRatchetA) ∗
        (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
        ((s0.sp - 400#64) ↦₆₄ x.ciphertextA) ∗
        (x.ciphertextA ↦ₛ x.ciphertext) ∗
        optAddrAt A x.locA x.loc ∗
        protocolAddressAt A x.rem x.remA ∗
        (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
        (s0.sp ↦₆₄ x.ciphertextA) ∗
        ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
        ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
        ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗
        ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
        ((s0.sp - 368#64) ↦₆₄ x.senderIkA) ∗
        ((s0.sp - 360#64) ↦₆₄ x.receiverIkA) ∗
        ((s0.sp - 352#64) ↦₆₄ x.macKeyA) ∗
        newSavedRegs s0.sp s0 ∗
        (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
        (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
        (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
        memRegion x.ret 120 ∗
        newUnusedPad s0.sp ∗
        memRegion (s0.sp - 152#64) 16) =
      (newUnusedPad s0.sp ∗
        ((s0.sp - 408#64) ↦₆₄ s2.readReg64 .x28) ∗
        ((s0.sp - 400#64) ↦₆₄ x.ciphertextA) ∗
        ((s0.sp - 392#64) ↦₆₄ s4.readReg64 .x25) ∗
        ((s0.sp - 384#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 380#64) ↦₃₂ x.previousCounter) ∗
        ((s0.sp - 376#64) ↦₆₄ x.senderRatchetKeyA) ∗
        ((s0.sp - 368#64) ↦₆₄ x.senderIkA) ∗
        ((s0.sp - 360#64) ↦₆₄ x.receiverIkA) ∗
        ((s0.sp - 352#64) ↦₆₄ x.macKeyA) ∗
        ((s0.sp - 344#64) ↦₆₄ s3.readReg64 .x26) ∗
        ((s0.sp - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
        ((s0.sp - 328#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp - 320#64) ↦₆₄ s4.readReg64 .x9) ∗
        memRegion (s0.sp - 312#64) 24 ∗
        cells (s0.sp - 288#64) 9 ∗
        optSerializeAddressesAt A (s0.sp - 216#64) (x.addresses uuidTryParse) ∗
        (∃∗ w192 : BitVec 32, (s0.sp - 192#64) ↦₃₂ w192) ∗
        (∃∗ w188 : BitVec 32, (s0.sp - 188#64) ↦₃₂ w188) ∗
        (∃∗ w184 : BitVec 32, (s0.sp - 184#64) ↦₃₂ w184) ∗
        (∃∗ w180 : BitVec 32, (s0.sp - 180#64) ↦₃₂ w180) ∗
        vecU8At A (s0.sp - 176#64)
          (BitVec.ofNat 64 (1 + (LibsignalProtoCodec.encode (x.protoMsg uuidTryParse)).length + 8))
          (s6.readReg64 .x22) (x.serPrefix6 uuidTryParse) ∗
        memRegion (s0.sp - 152#64) 16 ∗
        newSavedRegs s0.sp s0 ∗
        (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
        (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
        (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
        (x.macKeyA ↦ₛ keyToBytes32 x.macKey) ∗
        (x.ciphertextA ↦ₛ x.ciphertext) ∗
        (x.pqRatchetA ↦ₛ x.pqRatchet) ∗
        boxU8Buf A (s2.readReg64 .x28) x.senderRatchetKey.serialize ∗
        boxU8Buf A (s3.readReg64 .x26) x.ciphertext ∗
        optPqBuf A (s4.readReg64 .x9) (s4.readReg64 .x25) x.pqRatchet ∗
        memRegion x.ret 120 ∗
        A.pool ∗
        stackAt (s0.sp - 416#64) Statements.computeMacStackExt32) ∗
      (optAddrAt A x.locA x.loc ∗
        protocolAddressAt A x.rem x.remA ∗
        (s0.sp ↦₆₄ x.ciphertextA) ∗
        ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
        ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
        ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗
        ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
        ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length)) := by ac_rfl
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hregs, hent⟩ | ⟨hpan_s, P_f, hmf, hp⟩ | ⟨_, hoom⟩⟩ :=
    hstep8 _ hm hL
  · have hmf' : sf.mem ⊨ (P_f ∗
        (optAddrAt A x.locA x.loc ∗
          protocolAddressAt A x.rem x.remA ∗
          (s0.sp ↦₆₄ x.ciphertextA) ∗
          ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
          ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
          ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗
          ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
          ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length))) ∗ R := by
      rw [sepConj_assoc]; exact hmf
    refine ⟨sf, hsteps, Or.inl ⟨hpcf, hrunf, _, hmf', hregs,
      Entails.trans (sepConj_mono_left hent) ?_⟩⟩
    exact Entails.of_eq (by ac_rfl)
  · have hmf' : sf.mem ⊨ (P_f ∗
        (optAddrAt A x.locA x.loc ∗
          protocolAddressAt A x.rem x.remA ∗
          (s0.sp ↦₆₄ x.ciphertextA) ∗
          ((s0.sp + 8#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
          ((s0.sp + 16#64) ↦₆₄ x.senderIkA) ∗
          ((s0.sp + 24#64) ↦₆₄ x.receiverIkA) ∗
          ((s0.sp + 32#64) ↦₆₄ x.pqRatchetA) ∗
          ((s0.sp + 40#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length))) ∗ R := by
      rw [sepConj_assoc]; exact hmf
    have halloc := hp _ hmf
    rw [sepConj_assoc, satisfies_pure_sepConj] at halloc
    exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan_s, _, hmf', panicAllocPost_of_eq halloc.1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem signalMessageNew_ok_of_contracts_ext32 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAX : AllocContractsX img A ext)
    (hA4K : AllocContracts4K img.base A ext)
    (h_comp : HookSat ext compress256Name (withStack (compress256Spec C.F) extHookStack))
    (hHkdf : HkdfContractsExt img C.F ext) :
    ExtEncryptBody.SignalMessageNewOkExt32 img C A uuidTryParse ext := by
  have hNewSlice : NewFromSliceOkExt' img C ext := new_from_slice_ok_ext' img C ext himg hHkdf
  have hSpecEq : newFromSliceSpecExt C.F =
      newFromSlicePkStackSpecAt C.F Statements.computeMacPkStackExt32 := by
    simp only [newFromSliceSpecExt, newFromSlicePkStackSpecAt, newFromSliceStackExt,
      Statements.computeMacPkStackExt32]
  have hNewSlice' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName)
      ((newFromSlicePkStackSpecAt C.F Statements.computeMacPkStackExt32).inImage img) :=
    hSpecEq ▸ hNewSlice
  exact signalMessageNew_ok_ext32 hAX hA4K
    (Statements.computeMac_subroutine_ok_stacked_ext32 img C A ext hAX h_comp hNewSlice')

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtSignalMsgNew
