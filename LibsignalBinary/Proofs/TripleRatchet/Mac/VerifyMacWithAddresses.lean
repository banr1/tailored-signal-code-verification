/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyMacCompare
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Mac.Addresses
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Verification of `<SignalMessage>::verify_mac_with_addresses`

Main symbolic-execution proof of `<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses`
on both rebased images and `[LibsignalPlacement]`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession (logFilterAddr blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.InImageLift
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg calleeSavedVRegs_writeVReg128_ite calleeSavedVRegs_writeVReg64_ite
  calleeSavedVRegs_writeVReg32_ite isCalleeSavedVReg updateCalleeSavedVRegs
attribute [local simp, local arm64_norm]
  verifyMacWithAddresses_fnOff
  cset_eq_byte cset_eq_byte_alt bne_zext32_ite
  okTagVec_add_two_ne_zero okTagVec_add_two_eq_zero noneCap_add_one_eq_zero
  pack64_byte0 pack64_byte1 pack64_byte2 pack64_byte3
  pack64_byte4 pack64_byte5 pack64_byte6 pack64_byte7
  ite_one_zero_and_64 ite_one_zero_and_32 setWidth32_ite_one_zero_64
  zeroExtend64_ite_one_zero_32 ite_one_zero_and_one_64 setWidth8_ite_one_zero_64
  mac8_eq_bool
  setWidth8_zext64_32 setWidth8_setWidth32 setWidth8_and64 setWidth8_and32
  ite_one_zero_and_8 setWidth32_and_4294967297 setWidth32_and_1095216660735
  ite_one_zero_and_one_8 zeroExtend32_ite_one_zero_8

local elab "s2_ext_fetches " b:term:max ext:term:max
    hfn:term:max off:term:max len:term:max : tactic => open Lean Meta Elab Tactic in do
  let offLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat off "s2_ext_fetches "))
  let k0Lit := Syntax.mkNumLit "0"
  let lenLit := Syntax.mkNumLit (toString (← CryptoVerification.CodeLayout.evalNat len "s2_ext_fetches "))
  let hfnId : Ident ← if hfn.raw.isIdent then pure ⟨hfn.raw⟩ else do
    let g ← getMainGoal
    let c? ← g.withContext do
      tryCatchRuntimeEx (do
        let e := (← instantiateMVars (← Term.elabTermAndSynthesize hfn none)).consumeMData
        return if e.isConst then some e.constName! else none) (fun _ => pure none)
    match c? with
    | some c => pure (mkCIdentFrom hfn c)
    | none =>
      let id := mkIdent `_hfn_layout
      evalTactic (← `(tactic| have $id := $hfn))
      pure id
  evalTactic (← `(tactic| code_fetches_range CryptoVerification.libsignalSessionCode libsignalSessionBin $b (Rust.withPanics $ext) $hfnId:ident $offLit:num $k0Lit:num $lenLit:num))

/-! ## Main proof of `verify_mac_with_addresses` -/

theorem of_sepWP_inImage {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  of_sepWP_inImage_h hF hsym h

theorem computeMac_fnAddr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr verifyMacWithAddressesName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")) =
      (tripleRatchetProgAtExt b ext).fnAddr computeMacName := by
  have h1 : libsignalSessionCode.fnOff computeMacName = num% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::compute_mac")
  rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, Program.fnAddr_rebase, verifyMacWithAddresses_fnOff, h1]
  bv_omega

theorem serializeAddresses_fnAddr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr verifyMacWithAddressesName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")) =
      (tripleRatchetProgAtExt b ext).fnAddr serializeAddressesName := by
  have h1 : libsignalSessionCode.fnOff serializeAddressesName = num% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl) (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses")
  rw [tripleRatchetProgAtExt, Program.fnAddr_rebase, Program.fnAddr_rebase, verifyMacWithAddresses_fnOff, h1]
  bv_omega

theorem verifyMacWithAddresses_of_mac_false (F : ShaCompress) (m : SignalMessage)
    (exp : Option (List (BitVec 8))) (s r : IdentityKey) (k : BitVec 256)
    (h : (computeMac F s r k (m.serialized.take (m.serialized.length - 8)) ==
          m.serialized.drop (m.serialized.length - 8)) = false) :
    m.verifyMacWithAddresses F exp s r k = false := by
  simp [SignalMessage.verifyMacWithAddresses, SignalMessage.verifyMac, macLength, h]

theorem verifyMacWithAddresses_of_addrs_none (F : ShaCompress) (m : SignalMessage)
    (exp : Option (List (BitVec 8))) (s r : IdentityKey) (k : BitVec 256)
    (h : (computeMac F s r k (m.serialized.take (m.serialized.length - 8)) ==
          m.serialized.drop (m.serialized.length - 8)) = true)
    (haddr : m.addresses = none) :
    m.verifyMacWithAddresses F exp s r k = true := by
  simp [SignalMessage.verifyMacWithAddresses, SignalMessage.verifyMac, macLength, h,
    CryptoGames.LibsignalAead.addressCheckPasses, haddr]

theorem verifyMacWithAddresses_of_exp_none (F : ShaCompress) (m : SignalMessage)
    (ad : List (BitVec 8)) (s r : IdentityKey) (k : BitVec 256)
    (h : (computeMac F s r k (m.serialized.take (m.serialized.length - 8)) ==
          m.serialized.drop (m.serialized.length - 8)) = true)
    (haddr : m.addresses = some ad) :
    m.verifyMacWithAddresses F none s r k = false := by
  simp [SignalMessage.verifyMacWithAddresses, SignalMessage.verifyMac, macLength, h,
    CryptoGames.LibsignalAead.addressCheckPasses, haddr]

theorem verifyMacWithAddresses_of_exp_some (F : ShaCompress) (m : SignalMessage)
    (ad exp : List (BitVec 8)) (s r : IdentityKey) (k : BitVec 256)
    (h : (computeMac F s r k (m.serialized.take (m.serialized.length - 8)) ==
          m.serialized.drop (m.serialized.length - 8)) = true)
    (haddr : m.addresses = some ad) :
    m.verifyMacWithAddresses F (some exp) s r k = (ad == exp) := by
  simp [SignalMessage.verifyMacWithAddresses, SignalMessage.verifyMac, macLength, h,
    CryptoGames.LibsignalAead.addressCheckPasses, haddr]

theorem list_beq_false_of_length_ne {α : Type} [BEq α] [LawfulBEq α] {l1 l2 : List α}
    (hne : l1.length ≠ l2.length) : (l1 == l2) = false := by
  cases h : (l1 == l2)
  · rfl
  · exfalso; exact hne (congrArg List.length (eq_of_beq h))

theorem list_beq_comm {α : Type} [BEq α] [LawfulBEq α] (l1 l2 : List α) :
    (l1 == l2) = (l2 == l1) := by
  cases h1 : (l1 == l2) <;> cases h2 : (l2 == l1)
  · rfl
  · exfalso; rw [(eq_of_beq h2).symm, beq_self_eq_true] at h1; cases h1
  · exfalso; rw [eq_of_beq h1, beq_self_eq_true] at h2; cases h2
  · rfl

theorem optSerializeAddressesAt_none_eq (A : RustAlloc) (sp : BitVec 64) :
    optSerializeAddressesAt A (sp - 208#64) none =
      ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64,
        ((sp - 208#64) ↦₆₄ noneCap) ∗ ((sp - 200#64) ↦₆₄ w1) ∗ ((sp - 192#64) ↦₆₄ w2) := by
  simp only [optSerializeAddressesAt]
  have h200 : sp - 208#64 + 8#64 = sp - 200#64 := by bv_arith
  have h192 : sp - 200#64 + 8#64 = sp - 192#64 := by bv_arith
  rw [h200, memRegion_16_split_8_8, h192]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_16_of_sp_208 (sp w1 w2 : BitVec 64) :
    ((sp - 208#64) ↦₆₄ w1) ∗ ((sp - 200#64) ↦₆₄ w2) ⊢ memRegion (sp - 208#64) 16 := by
  have h200 : sp - 208#64 + 8#64 = sp - 200#64 := by bv_arith
  rw [← h200]
  exact memRegion_16_of_two_words (sp - 208#64) w1 w2

theorem memRegion_36_of_pointsToBytes (p : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 36) : (p ↦ₛ bs) ⊢ memRegion p 36 :=
  h ▸ pointsToBytes_entails_memRegion p bs

@[local simp, local arm64_norm]
theorem forall_some_eq_imp {α : Type} (a : α) (P : α → Prop) :
    (∀ x, some a = some x → P x) ↔ P a :=
  ⟨fun h => h a rfl, fun h _ hx => by cases hx; exact h⟩

@[local simp, local arm64_norm]
theorem forall_eq_right_imp {α : Type} (a : α) (P : α → Prop) :
    (∀ x, a = x → P x) ↔ P a :=
  ⟨fun h => h a rfl, fun h _ hx => hx ▸ h⟩

theorem stackAt_combine_ge (sp : BitVec 64) (n m : Nat) (h : m ≤ n) (hbound : n < 2 ^ 64) :
    stackAt sp m ∗ memRegion (sp - BitVec.ofNat 64 n) (n - m) ⊢ stackAt sp n := by
  rw [← stackAt_split_ge sp n m h hbound]
  exact Entails.refl _

/-- `serializeAddressesSpec` parameterized by stack budget `saStack`. -/
def serializeAddressesSpecWithStack (A : RustAlloc) (parse : UuidParser) (saStack : Nat) :
    Spec SerializeAddressesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.recipientA⌝ ∗
      protocolAddressAt A x.sender x.senderA ∗ protocolAddressAt A x.recipient x.recipientA ∗
      memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp saStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protocolAddressAt A x.sender x.senderA ∗ protocolAddressAt A x.recipient x.recipientA ∗
      optSerializeAddressesAt A x.ret (serializeAddresses (serviceIdParse parse) x.sender x.recipient) ∗
      A.pool ∗ stackAt s0.sp saStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `computeMacSpec` parameterized by stack budget `cmStack`. -/
def computeMacSpecWithStack (F : ShaCompress) (A : RustAlloc) (cmStack : Nat) :
    Spec ComputeMacGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.senderA ∧ s.readReg64 .x2 = x.receiverA ∧
      s.readReg64 .x3 = x.keyA ∧ s.readReg64 .x4 = 32#64 ∧ s.readReg64 .x5 = x.msgA ∧
      (s.readReg64 .x6).toNat = x.message.length ∧ x.message.length < 2 ^ 63⌝ ∗
      memRegion x.ret 16 ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool ∗ stackAt s.sp cmStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.ret ↦₆₄ okTagVec) ∗
      ((x.ret + 8#64) ↦ₛ computeMac F x.sender x.receiver x.macKey x.message) ∗
      (x.senderA ↦ₛ x.sender.publicKey.bytes.toList) ∗
      (x.receiverA ↦ₛ x.receiver.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey) ∗
      (x.msgA ↦ₛ x.message) ∗
      A.pool ∗ stackAt s0.sp cmStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `verifyMacWithAddressesSpec` parameterized by `compute_mac` stack budget `cmStack`
(total stack `cmStack + 288`). -/
def verifyMacWithAddressesSpecWithStack (img : Obj.Image) (F : ShaCompress) (A : RustAlloc)
    (parse : UuidParser) (cmStack : Nat) : Spec VerifyMacWithAddressesGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.senderAddrA ∧
      s.readReg64 .x2 = x.receiverAddrA ∧ s.readReg64 .x3 = x.senderIkA ∧
      s.readReg64 .x4 = x.receiverIkA ∧ s.readReg64 .x5 = x.keyA ∧
      s.readReg64 .x6 = 32#64 ∧ s.readReg64 .x8 = x.ret⌝ ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey) ∗
      memRegion x.ret 9 ∗
      logOff img ∗
      A.pool ∗ stackAt s.sp (cmStack + 288)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList) ∗
      (x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList) ∗
      (x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey) ∗
      verifyMacResultAt x.ret
        (x.msg.verifyMacWithAddresses F (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey) ∗
      logOff img ∗
      A.pool ∗ stackAt s0.sp (cmStack + 288)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def keepInImage {α : Type} (img : Obj.Image) (spec : Spec α) : Spec α where
  pre := spec.pre
  post := fun x s0 sf => ⌜img.FrozenLoaded sf ∧ sf.symtab = img.symtab⌝ ∗ spec.post x s0 sf
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_keepInImage {prog : Program} {entry : BitVec 64} {α : Type}
    {img : Obj.Image} {spec : Spec α}
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (keepInImage img (spec.inImage img)) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  simp only [keepInImage] at hpre
  have hpre_copy := hpre
  simp only [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre_copy
  rcases hpre_copy with ⟨⟨hF0, hsym0⟩, _⟩
  obtain ⟨sf, hsteps, hout, _⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre hsp hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [keepInImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hsteps.frozenLoaded hF0, hsteps.symtab_eq.trans hsym0⟩, hpost⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

local macro "wp_steps_inImage " mid:term : tactic =>
  `(tactic| (
    refine seq_inImage_h $mid ‹_› ‹_› ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_step hsym_step))

private structure VMHooks (cmStack saStack daStack : Nat)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State)) : Prop where
  hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName +
      BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")))
    ((rustDeallocExternSpecWithStack A daStack).inImage img)
  hbb_all : ∀ (sp_cur : BitVec 64) (n : Nat), daStack ≤ n → n ≤ cmStack → ∀ (v : BitVec 8),
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName +
        bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      ((session2BlackBoxSpecX sp_cur n v).inImage img)
  hser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr serializeAddressesName)
    ((serializeAddressesSpecWithStack A parse saStack).inImage img)
  hCompute : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
    ((computeMacSpecWithStack C.F A cmStack).inImage img)

section
attribute [local irreducible] _root_.Arm64.Program.fnOff

set_option maxHeartbeats 1600000 in
private theorem verifyMacWithAddresses_ok_of_hooks_gen_aux
    (cmStack saStack daStack : Nat)
    (hsa_le : saStack ≤ cmStack)
    (hda_le : daStack ≤ cmStack)
    (hcm_lt : cmStack + 288 < 2 ^ 64)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hk : VMHooks cmStack saStack daStack img C A parse ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpecWithStack img C.F A parse cmStack).inImage img) := by
  simp only [Spec.inImage, verifyMacWithAddressesSpecWithStack, signalMessageAt_expose,
    stackAt_verifyMacWithAddresses_gen cmStack (by omega), memRegion_24_split_16_8, memRegion_9_split,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  obtain ⟨hdealloc, hbb_all, hser, hCompute⟩ := hk
  have hCompute_keep := subroutine_ok_keepInImage hCompute
  clear hCompute
  have hser_keep := subroutine_ok_keepInImage hser
  clear hser
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hfn := verifyMacWithAddresses_fnOff
  have hbb0 := hbb_all (s0.sp - 288#64) daStack (Nat.le_refl _) hda_le 0#8
  have hbb1 := hbb_all (s0.sp - 288#64) daStack (Nat.le_refl _) hda_le 1#8
  s2_ext_fetches img.base ext hfn (num% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")) 888
  have hcomp_addr := computeMac_fnAddr_eq_ext img.base ext
  rw [← hcomp_addr] at hCompute_keep
  clear hcomp_addr
  have hser_addr := serializeAddresses_fnAddr_eq_ext img.base ext
  rw [← hser_addr] at hser_keep
  clear hser_addr
  have hmac_cmp := @macCompare8_full_sepWPp_gen cmStack img ext
    (fun sp_cur v => hbb_all sp_cur cmStack hda_le (Nat.le_refl _) v)
  have hct_eq := @ctEqLoop_sepWPp_gen cmStack img ext (s0.sp - 288#64)
    (fun v => hbb_all (s0.sp - 288#64) cmStack hda_le (Nat.le_refl _) v)
  clear hbb_all
  have hadrp544 := adrp_logFilter_544_ext ext hb
  have hadrp704 := adrp_logFilter_704_ext ext hb
  have hadrp704' := adrp_logFilter_704'_ext ext hb
  replace hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName := by
    rw [hpc, tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn]
  generalize_entry (tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName = entry
  examples_hide_fetches
  have hne : x.msg.serialized ≠ [] := by
    intro heq; rw [heq, List.length_nil] at h_5; unfold macLength at h_5; omega
  have hlen_ge9 : 9 ≤ x.msg.serialized.length := by unfold macLength at h_5; omega
  have hlen_ge8 : 8 ≤ x.msg.serialized.length := by omega
  have hsub8 := len_sub_8_eq hlen_ge9 h_7
  have hsub8_bv := len_sub_8_bv hlen_ge9 h_7
  have hult8 := len_ult_8_false hlen_ge9 h_7
  obtain ⟨hult_sub, hult_sub_rev, hule_sub, hneq_sub⟩ := len_sub_8_ult hlen_ge9 h_7
  have h48 : x.msgA + 40#64 + 8#64 = x.msgA + 48#64 := by bv_arith
  rw [boxU8At_expose_nonempty A (x.msgA + 40#64) x.msgG.serPtr x.msg.serialized hne, h48]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hser_ne, hser_lt⟩ => ?_
  conv => enter [4]; rw [pointsToBytes_serialized_split x.msgG.serPtr x.msg.serialized hlen_ge8]
  simp only [sepConj_assoc]
  apply of_sepWP_inImage h_2 h_1 (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF_1 hsym_1
  let cg : ComputeMacGhost :=
    { ret := s0.sp - 208#64
      senderA := x.senderIkA
      sender := x.senderIk
      receiverA := x.receiverIkA
      receiver := x.receiverIk
      keyA := x.keyA
      macKey := x.macKey
      msgA := x.msgG.serPtr
      message := x.msg.serialized.take (x.msg.serialized.length - 8) }
  have htake_len : (BitVec.ofNat 64 (x.msg.serialized.length - 8)).toNat =
      (x.msg.serialized.take (x.msg.serialized.length - 8)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), List.length_take]
    omega
  have htake_lt : (x.msg.serialized.take (x.msg.serialized.length - 8)).length < 2 ^ 63 := by
    rw [List.length_take]; omega
  refine SepWPp.call hCompute_keep (x := cg) (ret_pc := entry + bv% (100))
    (F := (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
      (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
      (x.msgG.serPtr + BitVec.ofNat 64 (x.msg.serialized.length - 8)) ↦ₛ
        List.drop (x.msg.serialized.length - 8) x.msg.serialized ∗
      A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
      optBoxU8At A (x.msgA + 88#64) x.msgG.addrPtr x.msg.addresses ∗
      signalMessageRest A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ logOff img ∗
      verifyMacFrameRest s0.sp ∗ (s0.sp - 192#64) ↦₆₄ v_stk_18 ∗
      (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗ (s0.sp - 280#64) ↦₆₄ v_stk_13 ∗
      (s0.sp - 272#64) ↦₆₄ v_stk_14 ∗ (s0.sp - 264#64) ↦₆₄ v_stk_15 ∗
      (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
      (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, *] at hsp_align ⊢)
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro _R' _hmR'
    simp only [keepInImage, Spec.inImage, computeMacSpecWithStack, cg, satisfies_pure_sepConj, sepConj_assoc, arm64_norm]
    exact ⟨⟨⟨hF_1, h_1⟩, htake_len, htake_lt⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) _hmR'⟩
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [keepInImage, Spec.inImage, computeMacSpecWithStack] at hm
    rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨ha, htr⟩ => ?_) hm
    unfold allocFailedIn at ha ⊢
    simpa only [arm64_norm, *] using ⟨ha, htr⟩
  · intro sf_1 hpc_1 hrun_1 hsp_1 hcs_1
    simp only [keepInImage, Spec.inImage, computeMacSpecWithStack, cg, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hF_1', hsym_1'⟩ => ?_
    refine SepWPp.pure_elim fun htr_1 => ?_
    have htr_1' : sf_1.trace = s0.trace := by simpa only [arm64_norm] using htr_1
    have hsp_1' : sf_1.sp = s0.sp - 288#64 := by simpa only [arm64_norm] using hsp_1
    have hsp_align_1 : sf_1.spAligned = true := by
      rw [State.spAligned, hsp_1']
      simp only [arm64_norm, *] at hsp_align ⊢
    obtain ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, _, _, _, _, hx29_1, hvregs_1⟩ := hcs_1
    simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 hvregs_1
    let ourMac := computeMac C.F x.senderIk x.receiverIk x.macKey
      (x.msg.serialized.take (x.msg.serialized.length - 8))
    have hour_len : ourMac.length = 8 := computeMac_length _ _ _ _ _
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 208#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 208#64 + 8#64) ↦ₛ ourMac) ∗
      (x.msgG.serPtr ↦ₛ x.msg.serialized.take (x.msg.serialized.length - 8)) ∗
      ((x.msgG.serPtr + BitVec.ofNat 64 (x.msg.serialized.length - 8)) ↦ₛ
        x.msg.serialized.drop (x.msg.serialized.length - 8)) ∗
      ((s0.sp - 280#64) ↦₆₄ v_stk_13) ∗ ((s0.sp - 272#64) ↦₆₄ v_stk_14) ∗
      ((s0.sp - 264#64) ↦₆₄ v_stk_15) ∗
      stackAt (s0.sp - 288#64) cmStack ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
       x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
       x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
       A.pool ∗
       (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
       (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
       A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
       optBoxU8At A (x.msgA + 88#64) x.msgG.addrPtr x.msg.addresses ∗
       signalMessageRest A x.msgG x.msgA x.msg ∗
       protocolAddressAt A x.senderAddr x.senderAddrA ∗
       protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
       x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ logOff img ∗
       verifyMacFrameRest s0.sp ∗ (s0.sp - 192#64) ↦₆₄ v_stk_18 ∗
       (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
       (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
       (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
       (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
       (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
       (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
       (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
       (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
       (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
       (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
       (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
       (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
       (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
       (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by ac_rfl))
    refine hmac_cmp ourMac x.msg.serialized s0.sp x.msgG.serPtr x.msgA x.receiverAddrA
      x.senderAddrA x.ret v_stk_13 v_stk_14 v_stk_15 _ sf_1 hour_len hlen_ge8
      hF_1' hsym_1' hpc_1 hrun_1 hsp_align_1 hsp_1' hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      fun sf_2 v8_2 v16_2 hF_2 hsym_2 hpc_2 hrun_2 hsp_align_2 htr_2 hsp_2 hx20_2 hx21_2 hx22_2 hx29_2 hvregs_2 => ?_
    have htr_2' : sf_2.trace = s0.trace := htr_2.trans htr_1'
    have hx29_2' : sf_2.readReg64 .x29 = s0.sp - 96#64 := hx29_2.trans hx29_1
    have hvregs_2' : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := hvregs_2.trans hvregs_1
    cases hmac : (ourMac == x.msg.serialized.drop (x.msg.serialized.length - 8))
    · simp only [hmac, Bool.false_eq_true, ↓reduceIte] at hpc_2
      have hres := verifyMacWithAddresses_of_mac_false C.F x.msg
        (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
        x.senderIk x.receiverIk x.macKey hmac
      simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
    · simp only [hmac, ↓reduceIte] at hpc_2
      cases haddr : x.msg.addresses with
      | none =>
        have hres := verifyMacWithAddresses_of_addrs_none C.F x.msg
          (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey hmac haddr
        simp only [optBoxU8At, verifyMacResultAt, hres, ↓reduceIte, sepConj_assoc]
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_done
      | some ad =>
        have had_lt40 : ad.length < 1099511627776 := h ad haddr
        rw [optBoxU8At_some_expose A x.msgA x.msgG.addrPtr ad]
        simp only [sepConj_assoc]
        apply SepWPp.weaken_pre (P' :=
          ⌜x.msgG.addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
          ((memRegion (s0.sp - 208#64) 16 ∗ ((s0.sp - 192#64) ↦₆₄ v_stk_18)) ∗
          ((x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
           (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
           (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
           (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
           ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
           ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
           x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
           x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
           x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
           A.pool ∗ stackAt (s0.sp - 288#64) cmStack ∗
           (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
           (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
           A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
           signalMessageRest A x.msgG x.msgA x.msg ∗
           protocolAddressAt A x.senderAddr x.senderAddrA ∗
           protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
           x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ logOff img ∗
           verifyMacFrameRest s0.sp ∗
           (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
           (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
           (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
           (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
           (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
           (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
           (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
           (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
           (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
           (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
           (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
           (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
           (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
           (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by ac_rfl))
        refine SepWPp.pure_elim fun ⟨haddr_ne, haddr_lt⟩ => ?_
        have haddr_beq : (x.msgG.addrPtr == 0#64) = false := beq_false_of_ne haddr_ne
        apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_24_of_16_8 s0.sp v_stk_18))
        conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack saStack hsa_le (by omega)]
        simp only [sepConj_assoc]
        apply of_sepWP_inImage hF_2 hsym_2 (mid := entry + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::protocol::SignalMessage>::serialize_addresses") - (ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hF_2' hsym_2'
        let sg : SerializeAddressesGhost :=
          { ret := s0.sp - 208#64
            senderA := x.senderAddrA
            sender := x.senderAddr
            recipientA := x.receiverAddrA
            recipient := x.receiverAddr }
        refine SepWPp.call hser_keep (x := sg) (ret_pc := entry + bv% (372))
          (F := (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
            (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
            (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
            (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
            ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
            ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
            x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
            x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
            x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
            memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack)
              (cmStack - saStack) ∗
            (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
            (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
            A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
            signalMessageRest A x.msgG x.msgA x.msg ∗
            x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ logOff img ∗
            verifyMacFrameRest s0.sp ∗
            (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
            (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
            (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
            (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
            (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
            (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
            (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
            (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
            (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
            (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
            (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
            (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
            (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
            (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, *] at hsp_align_2 ⊢)
          (by simp only [arm64_norm, *])
          ?_ ?_ ?_ ?_
        · intro _R' _hmR'
          simp only [keepInImage, Spec.inImage, serializeAddressesSpecWithStack, sg, sepConj_assoc, arm64_norm, *]
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) _hmR'
        · intro _ _ _ _ hm
          exact allowPanic_not_exited hm
        · intro sf _ hm
          dsimp only [keepInImage, Spec.inImage, serializeAddressesSpecWithStack] at hm
          rw [← sepConj_assoc]
          refine allowPanic_frame (fun ⟨ha, htr⟩ => ?_) hm
          unfold allocFailedIn at ha ⊢
          simp only [arm64_norm, *] at ha htr ⊢
          exact ⟨ha, htr⟩
        · intro sf_3 hpc_3 hrun_3 hsp_3 hcs_3
          simp only [keepInImage, Spec.inImage, serializeAddressesSpecWithStack, sg, sepConj_assoc, arm64_norm, *]
          refine SepWPp.pure_elim fun ⟨⟨hF_3, hsym_3⟩, htr_3⟩ => ?_
          have hsp_3' : sf_3.sp = s0.sp - 288#64 := by simp only [arm64_norm, *] at hsp_3; exact hsp_3
          have hsp_align_3 : sf_3.spAligned = true := by
            rw [State.spAligned, hsp_3']
            simp only [arm64_norm, *] at hsp_align_2 ⊢
          obtain ⟨hx19_3, hx20_3, _, _, hx23_3, _, _, _, _, _, hx29_3, hvregs_3⟩ := hcs_3
          simp only [arm64_norm, *] at hx19_3 hx20_3 hx23_3 hx29_3 hvregs_3
          apply SepWPp.weaken_pre (P' :=
            (stackAt (s0.sp - 288#64) saStack ∗
              memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack)
                (cmStack - saStack)) ∗
            (optSerializeAddressesAt A (s0.sp - 208#64)
              (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr) ∗
             protocolAddressAt A x.senderAddr x.senderAddrA ∗
             protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
             A.pool ∗
             (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
             (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
             (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
             (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
             ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
             ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
             x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
             x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
             x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
             (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
             (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
             A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
             signalMessageRest A x.msgG x.msgA x.msg ∗
             x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ logOff img ∗
             verifyMacFrameRest s0.sp ∗
             (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
             (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
             (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
             (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
             (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
             (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
             (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
             (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
             (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
             (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
             (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
             (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
             (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
             (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by ac_rfl))
          apply SepWPp.weaken_pre (sepConj_mono_left (stackAt_combine_ge (s0.sp - 288#64) cmStack saStack hsa_le (by omega)))
          rw [← sepConj_assoc, sepConj_comm (stackAt (s0.sp - 288#64) cmStack), sepConj_assoc]
          cases hexp : serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr with
          | none =>
            conv => enter [4]; rw [optSerializeAddressesAt_none_eq A s0.sp]
            simp only [sepExists_sepConj_left, sepConj_assoc]
            refine SepWPp.exists_elim fun w2_none => SepWPp.exists_elim fun w1_none => ?_
            have hres := verifyMacWithAddresses_of_exp_none C.F x.msg ad
              x.senderIk x.receiverIk x.macKey hmac haddr
            simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
            conv => enter [4]; rw [← hadrp544 ()]
            apply SepWPp.of_sepWP_ret
            wp_steps
            rw [hadrp544 (), ← sepConj_assoc]
            apply SepWP.weaken_pre (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp noneCap w1_none))
            wp_done
          | some exp =>
            have hexp_len : exp.length = 36 := serializeAddresses_some_length hexp
            conv => enter [4]; rw [optSerializeAddressesAt_some_eq A (s0.sp - 208#64) hexp_len]
            have h200 : s0.sp - 208#64 + 8#64 = s0.sp - 200#64 := by bv_arith
            have h192 : s0.sp - 208#64 + 16#64 = s0.sp - 192#64 := by bv_arith
            conv => enter [4]; rw [h200, h192]
            simp only [sepExists_sepConj_left, sepConj_assoc]
            refine SepWPp.exists_elim fun expPtr => SepWPp.pure_elim fun hexp_ne => ?_
            by_cases had_len : ad.length = 36
            · have had_ne : ad ≠ [] := by intro h; simp [h] at had_len
              have had_len_bv : BitVec.ofNat 64 ad.length = 36#64 := by rw [had_len]
              conv => enter [4]; simp only [had_ne, had_len_bv, ↓reduceIte, sepConj_assoc]
              apply of_sepWP_inImage hF_3 hsym_3 (mid := entry + bv% (412))
              wp_steps
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_3' hsym_3'
              apply SepWPp.weaken_pre (P' :=
                (expPtr ↦ₛ exp) ∗ (x.msgG.addrPtr ↦ₛ ad) ∗
                stackAt (s0.sp - 288#64) cmStack ∗
                (((s0.sp - 208#64) ↦₆₄ 36#64) ∗
                 ((s0.sp - 200#64) ↦₆₄ expPtr) ∗
                 ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                 A.live expPtr 36 1 ∗
                 protocolAddressAt A x.senderAddr x.senderAddrA ∗
                 protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                 A.pool ∗
                 (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                 (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                 A.live x.msgG.addrPtr ad.length 1 ∗
                 (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                 ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                 ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                 x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                 x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                 x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                 (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                 (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                 A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                 signalMessageRest A x.msgG x.msgA x.msg ∗
                 x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ logOff img ∗
                 verifyMacFrameRest s0.sp ∗
                 (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                 (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                 (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                 (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                 (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                 (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                 (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                 (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                 (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                 (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                 (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                 (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                 (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by ac_rfl))
              have hexp_ne_nil : exp ≠ [] := by intro h; simp [h] at hexp_len
              refine hct_eq exp ad expPtr x.msgG.addrPtr true _ _
                hexp_ne_nil (hexp_len.trans had_len.symm) (by omega)
                hF_3' hsym_3'
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [State.spAligned, arm64_norm, *] at hsp_align_3 ⊢)
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                fun sf_4 hF_4 hsym_4 hpc_4 hrun_4 hsp_align_4 htr_4 hsp_4
                  hx19_4 hx20_4 hx21_4 _ _ _ hx29_4 hvregs_4 hx22_4 => ?_
              simp only [arm64_norm, *] at htr_4 hsp_4 hx19_4 hx20_4 hx21_4 hx29_4 hvregs_4 hx22_4
              have hres := verifyMacWithAddresses_of_exp_some C.F x.msg ad exp
                x.senderIk x.receiverIk x.macKey hmac haddr
              rw [list_beq_comm ad exp] at hres
              apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_36_of_pointsToBytes expPtr hexp_len))
              obtain ⟨remDa, hrem_da⟩ : ∃ remDa,
                  memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - daStack) = remDa := ⟨_, rfl⟩
              have hcomb_da : stackAt (s0.sp - 288#64) daStack ∗ remDa ⊢ stackAt (s0.sp - 288#64) cmStack := by
                rw [← hrem_da, ← stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega)]
                exact Entails.refl _
              conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega), hrem_da]
              clear hrem_da
              cases heq_ad : (exp == ad)
              · simp only [heq_ad, Bool.false_eq_true, ↓reduceIte] at hx22_4
                simp only [verifyMacResultAt, hres, heq_ad, had_ne, had_len_bv, Bool.false_eq_true,
                  ↓reduceIte, sepConj_assoc]
                conv => enter [4]; rw [← hadrp704 ()]
                apply SepWPp.of_sepWP_ret
                wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
                refine seq_inImage_x30 ‹_› ‹_› ?_
                wp_call hbb0 ()
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_bb hsym_bb
                wp_steps_inImage (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
                refine seq_inImage_x30 ‹_› ‹_› ?_
                wp_call hdealloc (expPtr, 36, 1)
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_da hsym_da
                wp_steps
                rw [hadrp704' ()]
                conv => enter [4]; simp only [arm64_norm, *]
                apply SepWP.weaken_pre (P' :=
                  (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                  (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                   (A.pool ∗
                    (x.msgG.addrPtr ↦ₛ ad) ∗
                    ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                    protocolAddressAt A x.senderAddr x.senderAddrA ∗
                    protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                    (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                    (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                    A.live x.msgG.addrPtr 36 1 ∗
                    (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                    ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                    ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                    x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                    x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                    x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                    (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                    (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                    A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                    signalMessageRest A x.msgG x.msgA x.msg ∗
                    x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 0#8 ∗ logOff img ∗
                    verifyMacFrameRest s0.sp ∗
                    (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                    (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                    (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                    (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                    (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                    (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                    (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                    (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                    (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                    (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                    (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by ac_rfl))
                apply SepWP.weaken_pre (sepConj_mono hcomb_da
                  (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
                wp_done
              · simp only [heq_ad, ↓reduceIte] at hx22_4
                simp only [verifyMacResultAt, hres, heq_ad, had_ne, had_len_bv, ↓reduceIte,
                  sepConj_assoc]
                apply SepWPp.of_sepWP_ret
                wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
                refine seq_inImage_x30 ‹_› ‹_› ?_
                wp_call hbb1 ()
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_bb hsym_bb
                wp_steps_inImage (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
                refine seq_inImage_x30 ‹_› ‹_› ?_
                wp_call hdealloc (expPtr, 36, 1)
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_da hsym_da
                wp_steps
                conv => enter [4]; simp only [arm64_norm, *]
                apply SepWP.weaken_pre (P' :=
                  (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                  (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                   (A.pool ∗
                    (x.msgG.addrPtr ↦ₛ ad) ∗
                    ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                    protocolAddressAt A x.senderAddr x.senderAddrA ∗
                    protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                    (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                    (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                    A.live x.msgG.addrPtr 36 1 ∗
                    (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                    ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                    ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                    x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                    x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                    x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                    (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                    (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                    A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                    signalMessageRest A x.msgG x.msgA x.msg ∗
                    x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 1#8 ∗ logOff img ∗
                    verifyMacFrameRest s0.sp ∗
                    (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                    (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                    (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                    (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                    (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                    (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                    (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                    (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                    (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                    (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                    (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by ac_rfl))
                apply SepWP.weaken_pre (sepConj_mono hcomb_da
                  (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
                wp_done
            · have had_len_bv : (36#64 == BitVec.ofNat 64 ad.length) = false := by
                cases h : (36#64 == BitVec.ofNat 64 ad.length)
                · rfl
                · exfalso
                  have heq := eq_of_beq h
                  have h1 : (36#64 : BitVec 64).toNat = 36 := rfl
                  have h2 : (BitVec.ofNat 64 ad.length).toNat = ad.length := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  have h3 := congrArg BitVec.toNat heq
                  exact had_len (by omega)
              have hres := verifyMacWithAddresses_of_exp_some C.F x.msg ad exp
                x.senderIk x.receiverIk x.macKey hmac haddr
              have hbeq_false : (ad == exp) = false :=
                list_beq_false_of_length_ne (by omega)
              rw [hbeq_false] at hres
              simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
              obtain ⟨remDa, hrem_da⟩ : ∃ remDa,
                  memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - daStack) = remDa := ⟨_, rfl⟩
              have hcomb_da : stackAt (s0.sp - 288#64) daStack ∗ remDa ⊢ stackAt (s0.sp - 288#64) cmStack := by
                rw [← hrem_da, ← stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega)]
                exact Entails.refl _
              conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega), hrem_da, ← hadrp704 ()]
              clear hrem_da
              apply SepWPp.weaken_pre (P' :=
                (expPtr ↦ₛ exp) ∗
                ((s0.sp - 208#64) ↦₆₄ 36#64 ∗
                 (s0.sp - 200#64) ↦₆₄ expPtr ∗
                 (s0.sp - 192#64) ↦₆₄ 36#64 ∗
                 A.live expPtr 36 1 ∗
                 stackAt (s0.sp - 288#64) daStack ∗
                 remDa ∗
                 protocolAddressAt A x.senderAddr x.senderAddrA ∗
                 protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                 A.pool ∗
                 (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                 (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
                 (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ x.msgG.addrPtr ↦ₛ ad) ∗
                 x.msgG.serPtr ↦ₛ x.msg.serialized ∗
                 (s0.sp - 280#64) ↦₆₄ v8_2 ∗
                 (s0.sp - 272#64) ↦₆₄ v16_2 ∗
                 (s0.sp - 264#64) ↦₆₄ x.ret ∗
                 x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                 x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                 x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                 (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                 (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                 A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                 signalMessageRest A x.msgG x.msgA x.msg ∗
                 x.ret ↦₆₄ v_stk_19 ∗
                 (x.ret + 8#64) ↦₈ v_stk_20 ∗
                 (((entry + bv% (704) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::compute_mac" + 64)) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096)) ↦₆₄ 0#64) ∗
                 verifyMacFrameRest s0.sp ∗
                 (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                 (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗
                 (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                 (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                 (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                 (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                 (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                 (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                 (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                 (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                 (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                 (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                 (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                 (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by ac_rfl))
              apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_36_of_pointsToBytes expPtr hexp_len))
              apply SepWPp.of_sepWP_ret
              wp_steps_inImage (entry + bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
              refine seq_inImage_x30 ‹_› ‹_› ?_
              wp_call hbb0 ()
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_bb hsym_bb
              wp_steps_inImage (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
              refine seq_inImage_x30 ‹_› ‹_› ?_
              wp_call hdealloc (expPtr, 36, 1)
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_da hsym_da
              wp_steps
              rw [hadrp704' ()]
              conv => enter [4]; simp only [arm64_norm, *]
              apply SepWP.weaken_pre (P' :=
                (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                 (A.pool ∗
                  ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                  protocolAddressAt A x.senderAddr x.senderAddrA ∗
                  protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                  (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                  (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
                  (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ x.msgG.addrPtr ↦ₛ ad) ∗
                  (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                  ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                  ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                  x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                  x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                  x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                  (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                  (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                  A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                  signalMessageRest A x.msgG x.msgA x.msg ∗
                  x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 0#8 ∗ logOff img ∗
                  verifyMacFrameRest s0.sp ∗
                  (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                  (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                  (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                  (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                  (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                  (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                  (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                  (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                  (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                  (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                  (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                  (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                  (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                  (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by ac_rfl))
              apply SepWP.weaken_pre (sepConj_mono hcomb_da
                (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
              wp_done

end

theorem verifyMacWithAddresses_ok_of_hooks_gen
    (cmStack saStack daStack : Nat)
    (hsa_le : saStack ≤ cmStack)
    (hda_le : daStack ≤ cmStack)
    (hcm_lt : cmStack + 288 < 2 ^ 64)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")))
      ((rustDeallocExternSpecWithStack A daStack).inImage img))
    (hbb_all : ∀ (sp_cur : BitVec 64) (n : Nat), daStack ≤ n → n ≤ cmStack → ∀ (v : BitVec 8),
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName +
          bv% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
        ((session2BlackBoxSpecX sp_cur n v).inImage img))
    (hser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr serializeAddressesName)
      ((serializeAddressesSpecWithStack A parse saStack).inImage img))
    (hCompute : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpecWithStack C.F A cmStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpecWithStack img C.F A parse cmStack).inImage img) :=
  verifyMacWithAddresses_ok_of_hooks_gen_aux cmStack saStack daStack hsa_le hda_le hcm_lt
    img C A parse ext hb ⟨hdealloc, hbb_all, hser, hCompute⟩

theorem verifyMacWithAddresses_subroutine_ok_of_compute_ext
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext)
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName) blackBoxSpec)
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName) (uuidTryParseCodeSpec uuidTryParse))
    (hCompute : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_ok_of_hooks_gen
    computeMacStack serializeAddressesStack allocHookStack
    (by decide) (by decide) (by decide) img C A uuidTryParse ext hb
    (subroutine_ok_inImage_of_subroutine_ok img
      (rustDeallocExternWithStack_of_rustDealloc
        (dealloc_ok_at_norm_ext hA (name := verifyMacWithAddressesName)
          (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
          (by fnoff_eq))
        (by decide) (by decide)))
    (fun sp_cur n _ _ v => blackBox_ok_at2_ext_inImage sp_cur n hbb_raw
      (name := verifyMacWithAddressesName)
      (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      v (by fnoff_eq))
    (subroutine_ok_inImage_of_subroutine_ok img
      (serializeAddresses_subroutine_ok_of_contracts img.base A ext hA huuid))
    hCompute

theorem verifyMacWithAddresses_subroutine_ok_of_compute_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocHooks A abs)
    (hCompute : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_subroutine_ok_of_compute_ext img C A
    (trTrapExterns C abs) hb
    (AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hA)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.black_box_ok_at_trap img.base C abs blackBoxName 0 (Nat.add_zero _))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.uuid_try_parse_ok_at_trap img.base C abs uuidTryParseName 0 (Nat.add_zero _))
    hCompute

theorem verifyMacWithAddresses_subroutine_ok_of_compute
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocHooks A abs)
    (hCompute : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_subroutine_ok_of_compute_ext img C A
    (tripleRatchetExterns C ctl abs) hb
    (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.black_box_ok_at img.base C ctl abs blackBoxName 0 (Nat.add_zero _))
    (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.uuid_try_parse_ok_at img.base C ctl abs uuidTryParseName 0 (Nat.add_zero _))
    hCompute

theorem verifyMacWithAddresses_subroutine_ok_of_loads_ext
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext)
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName) blackBoxSpec)
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName) (uuidTryParseCodeSpec uuidTryParse))
    (hCompute : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_subroutine_ok_of_compute_ext img C A ext
    (base_aligned_of_loads himg) hA hbb_raw huuid hCompute

theorem verifyMacWithAddresses_subroutine_ok_of_loads_trap
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (hCompute : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img)) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_subroutine_ok_of_compute_trap img C A abs
    (base_aligned_of_loads himg) hA hCompute

theorem verifyMacWithAddresses_subroutine_ok_of_loads
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (hCompute : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr computeMacName)
      ((computeMacSpec C.F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpec img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_subroutine_ok_of_compute img C A ctl abs
    (base_aligned_of_loads himg) hA hCompute

theorem verifyMacWithAddresses_subroutine_ok_of_compute_ext_x
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContractsX img A ext)
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img))
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName)
      ((withStack (uuidTryParseSpec uuidTryParse) extHookStack).inImage img))
    (hCompute : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpecX C.F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpecX img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_ok_of_hooks_gen
    computeMacStackX serializeAddressesStackX extHookStack
    (by decide) (by decide) (by decide) img C A uuidTryParse ext hb
    (hA.dealloc_ok_at (name := verifyMacWithAddressesName)
      (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      (by fnoff_eq))
    (fun sp_cur n hn hncm v => blackBox_ok_at2_ext_x sp_cur n hbb_raw
      (name := verifyMacWithAddressesName)
      (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses"))
      v hn (Nat.lt_of_le_of_lt hncm (by decide)) (by fnoff_eq))
    (serializeAddresses_subroutine_ok_of_contracts_x img A ext hA huuid)
    hCompute

theorem verifyMacWithAddresses_subroutine_ok_of_loads_ext_x
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hbb_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr blackBoxName)
      ((withStack blackBoxU8Spec extHookStack).inImage img))
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName)
      ((withStack (uuidTryParseSpec uuidTryParse) extHookStack).inImage img))
    (hCompute : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((computeMacSpecX C.F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpecX img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_subroutine_ok_of_compute_ext_x img C A ext
    (base_aligned_of_loads himg) hA hbb_raw huuid hCompute

theorem verifyMacWithAddresses_subroutine_ok_at_ext32
    (cmStack : Nat) (hsa_le : serializeAddressesStackX ≤ cmStack) (hcm_lt : cmStack + 288 < 2 ^ 64)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hb : img.base &&& 0xfff#64 = 0#64) (hA : AllocContractsX img A ext)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName) ((withStack (uuidTryParseSpec uuidTryParse) extHookStack).inImage img))
    (hCompute : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName) ((computeMacSpecWithStack C.F A cmStack).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse cmStack).inImage img) :=
  verifyMacWithAddresses_ok_of_hooks_gen cmStack serializeAddressesStackX extHookStack
    hsa_le (Nat.le_trans (by decide) hsa_le) hcm_lt img C A uuidTryParse ext hb
    (hA.dealloc_ok_at (name := verifyMacWithAddressesName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")) (by fnoff_eq))
    (fun sp_cur n hn hncm v => blackBox_ok_at2_ext32 sp_cur n h_bb (name := verifyMacWithAddressesName) (k := num% (ls_off% "subtle::black_box::<u8>" - ls_off% "<libsignal_protocol::protocol::SignalMessage>::verify_mac_with_addresses")) v hn (Nat.lt_of_le_of_lt hncm (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hcm_lt)) (by fnoff_eq))
    (serializeAddresses_subroutine_ok_of_contracts_x img A ext hA huuid) hCompute

theorem verifyMacWithAddresses_subroutine_ok_ext32
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) (hA : AllocContractsX img A ext)
    (h_bb : HookSat ext blackBoxName CryptoVerification.SignalSession.CliExt.blackBoxSpec)
    (huuid : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr uuidTryParseName) ((withStack (uuidTryParseSpec uuidTryParse) extHookStack).inImage img))
    (hCompute : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName) ((computeMacSpecX C.F A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName) ((verifyMacWithAddressesSpecX img C.F A uuidTryParse).inImage img) :=
  verifyMacWithAddresses_subroutine_ok_of_loads_ext_x img himg C A ext hA (blackBoxU8_inImage_ok_ext32 img h_bb) huuid hCompute

/-! ## Relocatable `[LibsignalPlacement]` contract -/

class VmaInvClass (VmaInv : Memory → Prop) : Prop where
  of_keepsFrozen : ∀ {m m' : Memory}, VmaInv m → m.KeepsFrozen m' → VmaInv m'

def VmaClState [LibsignalPlacement] (m : Memory) : Prop :=
  LibsignalCodeLoaded lsmpl m

def VmaCroState [LibsignalPlacement] (m : Memory) : Prop :=
  LibsignalCodeRoLoaded lsmpl m

instance [LibsignalPlacement] : VmaInvClass VmaClState where
  of_keepsFrozen h hkf := LibsignalCodeLoaded.of_keepsFrozen h hkf

instance [LibsignalPlacement] : VmaInvClass VmaCroState where
  of_keepsFrozen h hkf := LibsignalCodeRoLoaded.of_keepsFrozen h hkf

def VmaSymState (_s : State) : Prop := True

def withVmaClState {VmaInv : Memory → Prop} {α : Type} (spec : Spec α) : Spec α where
  pre := fun x s => ⌜VmaInv s.mem ∧ VmaSymState s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

private theorem subroutine_ok_withVmaClState_of_lscl [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog addr (withVmaClState (VmaInv := VmaClState) spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withVmaClState, withLsCodeLoaded, VmaClState, VmaSymState] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hpre.1.1, hpre.2⟩

private theorem subroutine_ok_lscl_of_withVmaClState [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withVmaClState (VmaInv := VmaClState) spec)) :
    subroutine_ok prog addr (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withVmaClState, withLsCodeLoaded, VmaClState, VmaSymState] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpre.1, trivial⟩, hpre.2⟩

private theorem subroutine_ok_withVmaClState_of_lscro [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok prog addr (withVmaClState (VmaInv := VmaCroState) spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withVmaClState, withLsCodeRoLoaded, VmaCroState, VmaSymState] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hpre.1.1, hpre.2⟩

private theorem subroutine_ok_lscro_of_withVmaClState [LibsignalPlacement] {α : Type}
    {prog : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog addr (withVmaClState (VmaInv := VmaCroState) spec)) :
    subroutine_ok prog addr (withLsCodeRoLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp =>
    h.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  dsimp only [withVmaClState, withLsCodeRoLoaded, VmaCroState, VmaSymState] at hpre ⊢
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hpre.1, trivial⟩, hpre.2⟩

def keepVmaClState {VmaInv : Memory → Prop} {α : Type} (spec : Spec α) : Spec α where
  pre := spec.pre
  post := fun x s0 sf => ⌜VmaInv sf.mem ∧ VmaSymState sf⌝ ∗ spec.post x s0 sf
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_keepVmaClState {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} {entry : BitVec 64} {α : Type} {spec : Spec α}
    (h : subroutine_ok prog entry (withVmaClState (VmaInv := VmaInv) spec)) :
    subroutine_ok prog entry (keepVmaClState (VmaInv := VmaInv) (withVmaClState (VmaInv := VmaInv) spec)) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  simp only [keepVmaClState] at hpre
  have hpre_copy := hpre
  simp only [withVmaClState, sepConj_assoc, satisfies_pure_sepConj] at hpre_copy
  rcases hpre_copy with ⟨⟨hF0, _⟩, _⟩
  obtain ⟨sf, hsteps, hout, _⟩ := h.no_fault_before_outcome x R s0 hpc hrun hpre hsp hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [keepVmaClState, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨VmaInvClass.of_keepsFrozen hF0 hsteps.keepsFrozen, trivial⟩, hpost⟩
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

private theorem of_sepWP_vma {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : VmaInv s.mem) (_hsym : VmaSymState s)
    (h : SepWP prog mid s P
      (fun sm Pm => VmaInv sm.mem → VmaSymState sm →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (Φ := VmaInv)
    (fun _ _ => VmaInvClass.of_keepsFrozen) hF
    (SepWP.mono h fun _ _ _ _ hnext hcl => hnext hcl trivial)

private theorem seq_vma {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} (mid : BitVec 64) {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : VmaInv s.mem) (_hsym : VmaSymState s)
    (h : SepWP prog mid s P (fun sm Pm =>
      VmaInv sm.mem → VmaSymState sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  SepWP.seq_frozen (Φ := VmaInv)
    (fun _ _ => VmaInvClass.of_keepsFrozen) hF
    (SepWP.mono h fun _ _ _ _ hnext hcl => hnext hcl trivial)

private theorem seq_vma_x30 {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (hF : VmaInv s.mem) (hsym : VmaSymState s)
    (h : SepWP prog (s.readReg64 .x30) s P (fun sm Pm =>
      VmaInv sm.mem → VmaSymState sm → SepWP prog target_pc sm Pm post)) :
    SepWP prog target_pc s P post :=
  seq_vma (s.readReg64 .x30) hF hsym h

local macro "wp_steps_vma " mid:term : tactic =>
  `(tactic| (
    refine seq_vma $mid ‹_› ‹_› ?_
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hF_step hsym_step))

private theorem sepWPp_done_vma {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = ret) (hrun : s.status = .Running) (hq : Q s P) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.done hpc hrun hq

private theorem sepWPp_bind_vma {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    {prog : Program} (mid : BitVec 64) {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : VmaInv s.mem) (_hsym : VmaSymState s)
    (h : SepWPp prog mid s P (fun sm Pm => VmaInv sm.mem → VmaSymState sm → SepWPp prog ret sm Pm Q Qp) Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h R hm hL with ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | hpan | hoom⟩
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext (VmaInvClass.of_keepsFrozen hF hsteps.keepsFrozen) trivial R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

private structure VMHooksPlaced [LibsignalPlacement] (VmaInv : Memory → Prop) (cmStack saStack daStack : Nat)
    (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (H : String → Option (State → State)) : Prop where
  hdealloc : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
    (lsρ lsMacRustDeallocSym)
    (rustDeallocExternSpecWithStack A daStack)
  hbb_all : ∀ (sp_cur : BitVec 64) (n : Nat), daStack ≤ n → n ≤ cmStack → ∀ (v : BitVec 8),
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsBlackBoxU8Sym)
      (session2BlackBoxSpecX sp_cur n v)
  hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
    (lsmpl.base 61)
    (withVmaClState (VmaInv := VmaInv) (serializeAddressesSpecWithStack A parse saStack))
  hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
    (lsmpl.base 60)
    (withVmaClState (VmaInv := VmaInv) (computeMacSpecWithStack C.F A cmStack))

private theorem macLsLogOff_eq [LibsignalPlacement] :
    macLsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

set_option maxHeartbeats 1600000 in
private theorem verifyMacWithAddresses_placed_ok_of_hooks_gen_aux [LibsignalPlacement]
    {VmaInv : Memory → Prop} [VmaInvClass VmaInv]
    (cmStack saStack daStack : Nat)
    (hsa_le : saStack ≤ cmStack)
    (hda_le : daStack ≤ cmStack)
    (hcm_lt : cmStack + 288 < 2 ^ 64)
    (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (H : String → Option (State → State))
    (hk : VMHooksPlaced VmaInv cmStack saStack daStack C A parse H) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withVmaClState (VmaInv := VmaInv)
        (verifyMacWithAddressesPlacedSpecWithStack C.F A parse (cmStack + 288))) := by
  simp only [withVmaClState, verifyMacWithAddressesPlacedSpecWithStack, signalMessageAt_expose,
    stackAt_verifyMacWithAddresses_gen cmStack (by omega), memRegion_24_split_16_8, memRegion_9_split,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wpp_init x s0
  obtain ⟨hdealloc, hbb_all, hser, hCompute⟩ := hk
  have hCompute_keep := subroutine_ok_keepVmaClState hCompute
  clear hCompute
  have hser_keep := subroutine_ok_keepVmaClState hser
  clear hser
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hbb0 := hbb_all (s0.sp - 288#64) daStack (Nat.le_refl _) hda_le 0#8
  have hbb1 := hbb_all (s0.sp - 288#64) daStack (Nat.le_refl _) hda_le 1#8
  have hmac_cmp := @macCompare8_full_sepWPp_placed_gen _ cmStack H
    (fun sp_cur v => hbb_all sp_cur cmStack hda_le (Nat.le_refl _) v)
  have hct_eq := @ctEqLoop_sepWPp_placed_gen _ cmStack H (s0.sp - 288#64)
    (fun v => hbb_all (s0.sp - 288#64) cmStack hda_le (Nat.le_refl _) v)
  clear hbb_all
  have hne : x.msg.serialized ≠ [] := by
    intro heq; rw [heq, List.length_nil] at h_5; unfold macLength at h_5; omega
  have hlen_ge9 : 9 ≤ x.msg.serialized.length := by unfold macLength at h_5; omega
  have hlen_ge8 : 8 ≤ x.msg.serialized.length := by omega
  have hsub8 := len_sub_8_eq hlen_ge9 h_7
  have hsub8_bv := len_sub_8_bv hlen_ge9 h_7
  have hult8 := len_ult_8_false hlen_ge9 h_7
  obtain ⟨hult_sub, hult_sub_rev, hule_sub, hneq_sub⟩ := len_sub_8_ult hlen_ge9 h_7
  have h48 : x.msgA + 40#64 + 8#64 = x.msgA + 48#64 := by bv_arith
  rw [boxU8At_expose_nonempty A (x.msgA + 40#64) x.msgG.serPtr x.msg.serialized hne, h48]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hser_ne, hser_lt⟩ => ?_
  conv => enter [4]; rw [pointsToBytes_serialized_split x.msgG.serPtr x.msg.serialized hlen_ge8]
  simp only [sepConj_assoc]
  apply of_sepWP_vma h_2 h_1 (mid := lsmpl.base 60)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hF_1 hsym_1
  let cg : ComputeMacGhost :=
    { ret := s0.sp - 208#64
      senderA := x.senderIkA
      sender := x.senderIk
      receiverA := x.receiverIkA
      receiver := x.receiverIk
      keyA := x.keyA
      macKey := x.macKey
      msgA := x.msgG.serPtr
      message := x.msg.serialized.take (x.msg.serialized.length - 8) }
  have htake_len : (BitVec.ofNat 64 (x.msg.serialized.length - 8)).toNat =
      (x.msg.serialized.take (x.msg.serialized.length - 8)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), List.length_take]
    omega
  have htake_lt : (x.msg.serialized.take (x.msg.serialized.length - 8)).length < 2 ^ 63 := by
    rw [List.length_take]; omega
  refine SepWPp.call hCompute_keep (x := cg) (ret_pc := (blkPl_62).base + 100#64)
    (F := (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
      (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
      (x.msgG.serPtr + BitVec.ofNat 64 (x.msg.serialized.length - 8)) ↦ₛ
        List.drop (x.msg.serialized.length - 8) x.msg.serialized ∗
      A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
      optBoxU8At A (x.msgA + 88#64) x.msgG.addrPtr x.msg.addresses ∗
      signalMessageRest A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.senderAddr x.senderAddrA ∗
      protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
      x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
      verifyMacFrameRest s0.sp ∗ (s0.sp - 192#64) ↦₆₄ v_stk_18 ∗
      (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗ (s0.sp - 280#64) ↦₆₄ v_stk_13 ∗
      (s0.sp - 272#64) ↦₆₄ v_stk_14 ∗ (s0.sp - 264#64) ↦₆₄ v_stk_15 ∗
      (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
      (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
      (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, *] at hsp_align ⊢)
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro _R' _hmR'
    simp only [keepVmaClState, withVmaClState, computeMacSpecWithStack, cg, satisfies_pure_sepConj, sepConj_assoc, arm64_norm]
    exact ⟨⟨⟨hF_1, h_1⟩, htake_len, htake_lt⟩, Satisfies.mono (Entails.of_eq (by ac_rfl)) _hmR'⟩
  · intro _ _ _ _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [keepVmaClState, withVmaClState, computeMacSpecWithStack] at hm
    rw [← sepConj_assoc]
    refine allowPanic_frame (fun ⟨ha, htr⟩ => ?_) hm
    unfold allocFailedIn at ha ⊢
    simpa only [arm64_norm, *] using ⟨ha, htr⟩
  · intro sf_1 hpc_1 hrun_1 hsp_1 hcs_1
    simp only [keepVmaClState, withVmaClState, computeMacSpecWithStack, cg, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hF_1', hsym_1'⟩ => ?_
    refine SepWPp.pure_elim fun htr_1 => ?_
    have htr_1' : sf_1.trace = s0.trace := by simpa only [arm64_norm] using htr_1
    have hsp_1' : sf_1.sp = s0.sp - 288#64 := by simpa only [arm64_norm] using hsp_1
    have hsp_align_1 : sf_1.spAligned = true := by
      rw [State.spAligned, hsp_1']
      simp only [arm64_norm, *] at hsp_align ⊢
    obtain ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, _, _, _, _, hx29_1, hvregs_1⟩ := hcs_1
    simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx29_1 hvregs_1
    let ourMac := computeMac C.F x.senderIk x.receiverIk x.macKey
      (x.msg.serialized.take (x.msg.serialized.length - 8))
    have hour_len : ourMac.length = 8 := computeMac_length _ _ _ _ _
    apply SepWPp.weaken_pre (P' :=
      ((s0.sp - 208#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 208#64 + 8#64) ↦ₛ ourMac) ∗
      (x.msgG.serPtr ↦ₛ x.msg.serialized.take (x.msg.serialized.length - 8)) ∗
      ((x.msgG.serPtr + BitVec.ofNat 64 (x.msg.serialized.length - 8)) ↦ₛ
        x.msg.serialized.drop (x.msg.serialized.length - 8)) ∗
      ((s0.sp - 280#64) ↦₆₄ v_stk_13) ∗ ((s0.sp - 272#64) ↦₆₄ v_stk_14) ∗
      ((s0.sp - 264#64) ↦₆₄ v_stk_15) ∗
      stackAt (s0.sp - 288#64) cmStack ∗
      (x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
       x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
       x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
       A.pool ∗
       (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
       (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
       A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
       optBoxU8At A (x.msgA + 88#64) x.msgG.addrPtr x.msg.addresses ∗
       signalMessageRest A x.msgG x.msgA x.msg ∗
       protocolAddressAt A x.senderAddr x.senderAddrA ∗
       protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
       x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
       verifyMacFrameRest s0.sp ∗ (s0.sp - 192#64) ↦₆₄ v_stk_18 ∗
       (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
       (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
       (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
       (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
       (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
       (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
       (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
       (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
       (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
       (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
       (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
       (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
       (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
       (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by ac_rfl))
    refine sepWPp_bind_vma
      (if (ourMac == x.msg.serialized.drop (x.msg.serialized.length - 8)) then
         (blkPl_62).base + 344#64
       else
         (blkPl_62).base + 504#64)
      hF_1' hsym_1' ?_
    refine hmac_cmp ourMac x.msg.serialized s0.sp x.msgG.serPtr x.msgA x.receiverAddrA
      x.senderAddrA x.ret v_stk_13 v_stk_14 v_stk_15 _ sf_1 hour_len hlen_ge8
      hpc_1 hrun_1 hsp_align_1 hsp_1' hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1
      fun sf_2 v8_2 v16_2 hpc_2 hrun_2 hsp_align_2 htr_2 hsp_2 hx20_2 hx21_2 hx22_2 hx29_2 hvregs_2 =>
        sepWPp_done_vma hpc_2 hrun_2 fun hF_2 hsym_2 => ?_
    have htr_2' : sf_2.trace = s0.trace := htr_2.trans htr_1'
    have hx29_2' : sf_2.readReg64 .x29 = s0.sp - 96#64 := hx29_2.trans hx29_1
    have hvregs_2' : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := hvregs_2.trans hvregs_1
    cases hmac : (ourMac == x.msg.serialized.drop (x.msg.serialized.length - 8))
    · simp only [hmac, Bool.false_eq_true, ↓reduceIte] at hpc_2
      have hres := verifyMacWithAddresses_of_mac_false C.F x.msg
        (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
        x.senderIk x.receiverIk x.macKey hmac
      simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
      apply SepWPp.of_sepWP_ret
      wp_steps
      wp_done
    · simp only [hmac, ↓reduceIte] at hpc_2
      cases haddr : x.msg.addresses with
      | none =>
        have hres := verifyMacWithAddresses_of_addrs_none C.F x.msg
          (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr)
          x.senderIk x.receiverIk x.macKey hmac haddr
        simp only [optBoxU8At, verifyMacResultAt, hres, ↓reduceIte, sepConj_assoc]
        apply SepWPp.of_sepWP_ret
        wp_steps
        wp_done
      | some ad =>
        have had_lt40 : ad.length < 1099511627776 := h ad haddr
        rw [optBoxU8At_some_expose A x.msgA x.msgG.addrPtr ad]
        simp only [sepConj_assoc]
        apply SepWPp.weaken_pre (P' :=
          ⌜x.msgG.addrPtr ≠ 0#64 ∧ ad.length < 2 ^ 63⌝ ∗
          ((memRegion (s0.sp - 208#64) 16 ∗ ((s0.sp - 192#64) ↦₆₄ v_stk_18)) ∗
          ((x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
           (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
           (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
           (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
           ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
           ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
           x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
           x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
           x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
           A.pool ∗ stackAt (s0.sp - 288#64) cmStack ∗
           (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
           (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
           A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
           signalMessageRest A x.msgG x.msgA x.msg ∗
           protocolAddressAt A x.senderAddr x.senderAddrA ∗
           protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
           x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
           verifyMacFrameRest s0.sp ∗
           (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
           (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
           (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
           (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
           (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
           (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
           (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
           (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
           (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
           (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
           (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
           (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
           (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
           (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by ac_rfl))
        refine SepWPp.pure_elim fun ⟨haddr_ne, haddr_lt⟩ => ?_
        have haddr_beq : (x.msgG.addrPtr == 0#64) = false := beq_false_of_ne haddr_ne
        apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_24_of_16_8 s0.sp v_stk_18))
        conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack saStack hsa_le (by omega)]
        simp only [sepConj_assoc]
        apply of_sepWP_vma hF_2 hsym_2 (mid := lsmpl.base 61)
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hF_2' hsym_2'
        let sg : SerializeAddressesGhost :=
          { ret := s0.sp - 208#64
            senderA := x.senderAddrA
            sender := x.senderAddr
            recipientA := x.receiverAddrA
            recipient := x.receiverAddr }
        refine SepWPp.call hser_keep (x := sg) (ret_pc := (blkPl_62).base + 372#64)
          (F := (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
            (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
            (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
            (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
            ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
            ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
            x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
            x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
            x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
            memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack)
              (cmStack - saStack) ∗
            (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
            (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
            A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
            signalMessageRest A x.msgG x.msgA x.msg ∗
            x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
            verifyMacFrameRest s0.sp ∗
            (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
            (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
            (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
            (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
            (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
            (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
            (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
            (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
            (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
            (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
            (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
            (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
            (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
            (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
          (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by simp only [State.spAligned, arm64_norm, *] at hsp_align_2 ⊢)
          (by simp only [arm64_norm, *])
          ?_ ?_ ?_ ?_
        · intro _R' _hmR'
          simp only [keepVmaClState, withVmaClState, serializeAddressesSpecWithStack, sg, sepConj_assoc, arm64_norm, *]
          exact Satisfies.mono (Entails.of_eq (by ac_rfl)) _hmR'
        · intro _ _ _ _ hm
          exact allowPanic_not_exited hm
        · intro sf _ hm
          dsimp only [keepVmaClState, withVmaClState, serializeAddressesSpecWithStack] at hm
          rw [← sepConj_assoc]
          refine allowPanic_frame (fun ⟨ha, htr⟩ => ?_) hm
          unfold allocFailedIn at ha ⊢
          simp only [arm64_norm, *] at ha htr ⊢
          exact ⟨ha, htr⟩
        · intro sf_3 hpc_3 hrun_3 hsp_3 hcs_3
          simp only [keepVmaClState, withVmaClState, serializeAddressesSpecWithStack, sg, sepConj_assoc, arm64_norm, *]
          refine SepWPp.pure_elim fun ⟨⟨hF_3, hsym_3⟩, htr_3⟩ => ?_
          have hsp_3' : sf_3.sp = s0.sp - 288#64 := by simp only [arm64_norm, *] at hsp_3; exact hsp_3
          have hsp_align_3 : sf_3.spAligned = true := by
            rw [State.spAligned, hsp_3']
            simp only [arm64_norm, *] at hsp_align_2 ⊢
          obtain ⟨hx19_3, hx20_3, _, _, hx23_3, _, _, _, _, _, hx29_3, hvregs_3⟩ := hcs_3
          simp only [arm64_norm, *] at hx19_3 hx20_3 hx23_3 hx29_3 hvregs_3
          apply SepWPp.weaken_pre (P' :=
            (stackAt (s0.sp - 288#64) saStack ∗
              memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack)
                (cmStack - saStack)) ∗
            (optSerializeAddressesAt A (s0.sp - 208#64)
              (serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr) ∗
             protocolAddressAt A x.senderAddr x.senderAddrA ∗
             protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
             A.pool ∗
             (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
             (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
             (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ (x.msgG.addrPtr ↦ₛ ad)) ∗
             (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
             ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
             ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
             x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
             x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
             x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
             (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
             (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
             A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
             signalMessageRest A x.msgG x.msgA x.msg ∗
             x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
             verifyMacFrameRest s0.sp ∗
             (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
             (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
             (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
             (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
             (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
             (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
             (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
             (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
             (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
             (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
             (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
             (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
             (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
             (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by ac_rfl))
          apply SepWPp.weaken_pre (sepConj_mono_left (stackAt_combine_ge (s0.sp - 288#64) cmStack saStack hsa_le (by omega)))
          rw [← sepConj_assoc, sepConj_comm (stackAt (s0.sp - 288#64) cmStack), sepConj_assoc]
          cases hexp : serializeAddresses (serviceIdParse parse) x.senderAddr x.receiverAddr with
          | none =>
            conv => enter [4]; rw [optSerializeAddressesAt_none_eq A s0.sp]
            simp only [sepExists_sepConj_left, sepConj_assoc]
            refine SepWPp.exists_elim fun w2_none => SepWPp.exists_elim fun w1_none => ?_
            have hres := verifyMacWithAddresses_of_exp_none C.F x.msg ad
              x.senderIk x.receiverIk x.macKey hmac haddr
            simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
            conv => enter [4]; rw [macLsLogOff_eq]
            apply SepWPp.of_sepWP_ret
            wp_steps
            rw [← macLsLogOff_eq, ← sepConj_assoc]
            apply SepWP.weaken_pre (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp noneCap w1_none))
            wp_done
          | some exp =>
            have hexp_len : exp.length = 36 := serializeAddresses_some_length hexp
            conv => enter [4]; rw [optSerializeAddressesAt_some_eq A (s0.sp - 208#64) hexp_len]
            have h200 : s0.sp - 208#64 + 8#64 = s0.sp - 200#64 := by bv_arith
            have h192 : s0.sp - 208#64 + 16#64 = s0.sp - 192#64 := by bv_arith
            conv => enter [4]; rw [h200, h192]
            simp only [sepExists_sepConj_left, sepConj_assoc]
            refine SepWPp.exists_elim fun expPtr => SepWPp.pure_elim fun hexp_ne => ?_
            by_cases had_len : ad.length = 36
            · have had_ne : ad ≠ [] := by intro h; simp [h] at had_len
              have had_len_bv : BitVec.ofNat 64 ad.length = 36#64 := by rw [had_len]
              conv => enter [4]; simp only [had_ne, had_len_bv, ↓reduceIte, sepConj_assoc]
              apply of_sepWP_vma hF_3 hsym_3 (mid := (blkPl_62).base + 412#64)
              wp_steps
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_3' hsym_3'
              apply SepWPp.weaken_pre (P' :=
                (expPtr ↦ₛ exp) ∗ (x.msgG.addrPtr ↦ₛ ad) ∗
                stackAt (s0.sp - 288#64) cmStack ∗
                (((s0.sp - 208#64) ↦₆₄ 36#64) ∗
                 ((s0.sp - 200#64) ↦₆₄ expPtr) ∗
                 ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                 A.live expPtr 36 1 ∗
                 protocolAddressAt A x.senderAddr x.senderAddrA ∗
                 protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                 A.pool ∗
                 (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                 (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                 A.live x.msgG.addrPtr ad.length 1 ∗
                 (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                 ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                 ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                 x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                 x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                 x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                 (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                 (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                 A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                 signalMessageRest A x.msgG x.msgA x.msg ∗
                 x.ret ↦₆₄ v_stk_19 ∗ (x.ret + 8#64) ↦₈ v_stk_20 ∗ macLsLogOff ∗
                 verifyMacFrameRest s0.sp ∗
                 (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                 (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                 (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                 (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                 (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                 (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                 (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                 (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                 (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                 (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                 (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                 (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                 (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by ac_rfl))
              have hexp_ne_nil : exp ≠ [] := by intro h; simp [h] at hexp_len
              refine sepWPp_bind_vma ((blkPl_62).base + 444#64) hF_3' hsym_3' ?_
              refine hct_eq exp ad expPtr x.msgG.addrPtr true _ _
                hexp_ne_nil (hexp_len.trans had_len.symm) (by omega)
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [State.spAligned, arm64_norm, *] at hsp_align_3 ⊢)
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                (by simp only [arm64_norm, *])
                fun sf_4 hpc_4 hrun_4 hsp_align_4 htr_4 hsp_4
                  hx19_4 hx20_4 hx21_4 _ _ _ hx29_4 hvregs_4 hx22_4 =>
                  sepWPp_done_vma hpc_4 hrun_4 fun hF_4 hsym_4 => ?_
              simp only [arm64_norm, *] at htr_4 hsp_4 hx19_4 hx20_4 hx21_4 hx29_4 hvregs_4 hx22_4
              have hres := verifyMacWithAddresses_of_exp_some C.F x.msg ad exp
                x.senderIk x.receiverIk x.macKey hmac haddr
              rw [list_beq_comm ad exp] at hres
              apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_36_of_pointsToBytes expPtr hexp_len))
              obtain ⟨remDa, hrem_da⟩ : ∃ remDa,
                  memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - daStack) = remDa := ⟨_, rfl⟩
              have hcomb_da : stackAt (s0.sp - 288#64) daStack ∗ remDa ⊢ stackAt (s0.sp - 288#64) cmStack := by
                rw [← hrem_da, ← stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega)]
                exact Entails.refl _
              conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega), hrem_da]
              clear hrem_da
              cases heq_ad : (exp == ad)
              · simp only [heq_ad, Bool.false_eq_true, ↓reduceIte] at hx22_4
                simp only [verifyMacResultAt, hres, heq_ad, had_ne, had_len_bv, Bool.false_eq_true,
                  ↓reduceIte, sepConj_assoc]
                apply SepWPp.of_sepWP_ret
                wp_steps_vma (lsρ lsBlackBoxU8Sym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hbb0 ()
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_bb hsym_bb
                conv => enter [4]; rw [macLsLogOff_eq]
                wp_steps_vma (lsρ lsMacRustDeallocSym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hdealloc (expPtr, 36, 1)
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_da hsym_da
                wp_steps
                rw [← macLsLogOff_eq]
                conv => enter [4]; simp only [arm64_norm, *]
                apply SepWP.weaken_pre (P' :=
                  (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                  (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                   (A.pool ∗
                    (x.msgG.addrPtr ↦ₛ ad) ∗
                    ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                    protocolAddressAt A x.senderAddr x.senderAddrA ∗
                    protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                    (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                    (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                    A.live x.msgG.addrPtr 36 1 ∗
                    (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                    ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                    ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                    x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                    x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                    x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                    (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                    (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                    A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                    signalMessageRest A x.msgG x.msgA x.msg ∗
                    x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 0#8 ∗ macLsLogOff ∗
                    verifyMacFrameRest s0.sp ∗
                    (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                    (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                    (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                    (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                    (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                    (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                    (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                    (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                    (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                    (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                    (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by ac_rfl))
                apply SepWP.weaken_pre (sepConj_mono hcomb_da
                  (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
                wp_done
              · simp only [heq_ad, ↓reduceIte] at hx22_4
                simp only [verifyMacResultAt, hres, heq_ad, had_ne, had_len_bv, ↓reduceIte,
                  sepConj_assoc]
                apply SepWPp.of_sepWP_ret
                wp_steps_vma (lsρ lsBlackBoxU8Sym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hbb1 ()
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_bb hsym_bb
                wp_steps_vma (lsρ lsMacRustDeallocSym)
                refine seq_vma_x30 ‹_› ‹_› ?_
                wp_call hdealloc (expPtr, 36, 1)
                apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
                intro hF_da hsym_da
                wp_steps
                conv => enter [4]; simp only [arm64_norm, *]
                apply SepWP.weaken_pre (P' :=
                  (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                  (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                   (A.pool ∗
                    (x.msgG.addrPtr ↦ₛ ad) ∗
                    ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                    protocolAddressAt A x.senderAddr x.senderAddrA ∗
                    protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                    (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                    (x.msgA + 96#64) ↦₆₄ 36#64 ∗
                    A.live x.msgG.addrPtr 36 1 ∗
                    (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                    ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                    ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                    x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                    x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                    x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                    (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                    (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                    A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                    signalMessageRest A x.msgG x.msgA x.msg ∗
                    x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 1#8 ∗ macLsLogOff ∗
                    verifyMacFrameRest s0.sp ∗
                    (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                    (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                    (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                    (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                    (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                    (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                    (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                    (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                    (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                    (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                    (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                    (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by ac_rfl))
                apply SepWP.weaken_pre (sepConj_mono hcomb_da
                  (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
                wp_done
            · have had_len_bv : (36#64 == BitVec.ofNat 64 ad.length) = false := by
                cases h : (36#64 == BitVec.ofNat 64 ad.length)
                · rfl
                · exfalso
                  have heq := eq_of_beq h
                  have h1 : (36#64 : BitVec 64).toNat = 36 := rfl
                  have h2 : (BitVec.ofNat 64 ad.length).toNat = ad.length := by
                    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
                  have h3 := congrArg BitVec.toNat heq
                  exact had_len (by omega)
              have hres := verifyMacWithAddresses_of_exp_some C.F x.msg ad exp
                x.senderIk x.receiverIk x.macKey hmac haddr
              have hbeq_false : (ad == exp) = false :=
                list_beq_false_of_length_ne (by omega)
              rw [hbeq_false] at hres
              simp only [verifyMacResultAt, hres, Bool.false_eq_true, ↓reduceIte, sepConj_assoc]
              obtain ⟨remDa, hrem_da⟩ : ∃ remDa,
                  memRegion (s0.sp - 288#64 - BitVec.ofNat 64 cmStack) (cmStack - daStack) = remDa := ⟨_, rfl⟩
              have hcomb_da : stackAt (s0.sp - 288#64) daStack ∗ remDa ⊢ stackAt (s0.sp - 288#64) cmStack := by
                rw [← hrem_da, ← stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega)]
                exact Entails.refl _
              conv => enter [4]; rw [stackAt_split_ge (s0.sp - 288#64) cmStack daStack hda_le (by omega), hrem_da]
              clear hrem_da
              apply SepWPp.weaken_pre (P' :=
                (expPtr ↦ₛ exp) ∗
                ((s0.sp - 208#64) ↦₆₄ 36#64 ∗
                 (s0.sp - 200#64) ↦₆₄ expPtr ∗
                 (s0.sp - 192#64) ↦₆₄ 36#64 ∗
                 A.live expPtr 36 1 ∗
                 stackAt (s0.sp - 288#64) daStack ∗
                 remDa ∗
                 protocolAddressAt A x.senderAddr x.senderAddrA ∗
                 protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                 A.pool ∗
                 (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                 (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
                 (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ x.msgG.addrPtr ↦ₛ ad) ∗
                 x.msgG.serPtr ↦ₛ x.msg.serialized ∗
                 (s0.sp - 280#64) ↦₆₄ v8_2 ∗
                 (s0.sp - 272#64) ↦₆₄ v16_2 ∗
                 (s0.sp - 264#64) ↦₆₄ x.ret ∗
                 x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                 x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                 x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                 (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                 (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                 A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                 signalMessageRest A x.msgG x.msgA x.msg ∗
                 x.ret ↦₆₄ v_stk_19 ∗
                 (x.ret + 8#64) ↦₈ v_stk_20 ∗
                 macLsLogOff ∗
                 verifyMacFrameRest s0.sp ∗
                 (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                 (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗
                 (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                 (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                 (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                 (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                 (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                 (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                 (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                 (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                 (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                 (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                 (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                 (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                 (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))) (Entails.of_eq (by ac_rfl))
              apply SepWPp.weaken_pre (sepConj_mono_left (memRegion_36_of_pointsToBytes expPtr hexp_len))
              apply SepWPp.of_sepWP_ret
              wp_steps_vma (lsρ lsBlackBoxU8Sym)
              refine seq_vma_x30 ‹_› ‹_› ?_
              wp_call hbb0 ()
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_bb hsym_bb
              conv => enter [4]; rw [macLsLogOff_eq]
              wp_steps_vma (lsρ lsMacRustDeallocSym)
              refine seq_vma_x30 ‹_› ‹_› ?_
              wp_call hdealloc (expPtr, 36, 1)
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hF_da hsym_da
              wp_steps
              rw [← macLsLogOff_eq]
              conv => enter [4]; simp only [arm64_norm, *]
              apply SepWP.weaken_pre (P' :=
                (stackAt (s0.sp - 288#64) daStack ∗ remDa) ∗
                (((s0.sp - 208#64) ↦₆₄ 36#64 ∗ (s0.sp - 200#64) ↦₆₄ expPtr) ∗
                 (A.pool ∗
                  ((s0.sp - 192#64) ↦₆₄ 36#64) ∗
                  protocolAddressAt A x.senderAddr x.senderAddrA ∗
                  protocolAddressAt A x.receiverAddr x.receiverAddrA ∗
                  (x.msgA + 88#64) ↦₆₄ x.msgG.addrPtr ∗
                  (x.msgA + 96#64) ↦₆₄ BitVec.ofNat 64 ad.length ∗
                  (if ad = [] then emp else A.live x.msgG.addrPtr ad.length 1 ∗ x.msgG.addrPtr ↦ₛ ad) ∗
                  (x.msgG.serPtr ↦ₛ x.msg.serialized) ∗
                  ((s0.sp - 280#64) ↦₆₄ v8_2) ∗ ((s0.sp - 272#64) ↦₆₄ v16_2) ∗
                  ((s0.sp - 264#64) ↦₆₄ x.ret) ∗
                  x.senderIkA ↦ₛ x.senderIk.publicKey.bytes.toList ∗
                  x.receiverIkA ↦ₛ x.receiverIk.publicKey.bytes.toList ∗
                  x.keyA ↦ₛ HMAC.keyToBytes32 x.macKey ∗
                  (x.msgA + 40#64) ↦₆₄ x.msgG.serPtr ∗
                  (x.msgA + 48#64) ↦₆₄ BitVec.ofNat 64 x.msg.serialized.length ∗
                  A.live x.msgG.serPtr x.msg.serialized.length 1 ∗
                  signalMessageRest A x.msgG x.msgA x.msg ∗
                  x.ret ↦₆₄ (bv% (2 ^ 64 - 2)) ∗ (x.ret + 8#64) ↦₈ 0#8 ∗ macLsLogOff ∗
                  verifyMacFrameRest s0.sp ∗
                  (s0.sp - 288#64) ↦₆₄ v_stk_12 ∗
                  (s0.sp - 256#64) ↦₆₄ x.senderAddrA ∗ (s0.sp - 248#64) ↦₆₄ x.receiverAddrA ∗
                  (s0.sp - 96#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                  (s0.sp - 88#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                  (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
                  (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 27#5) ∗
                  (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 26#5) ∗
                  (s0.sp - 56#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
                  (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
                  (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
                  (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
                  (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
                  (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                  (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))) (Entails.of_eq (by ac_rfl))
              apply SepWP.weaken_pre (sepConj_mono hcomb_da
                (sepConj_mono_left (memRegion_16_of_sp_208 s0.sp 36#64 expPtr)))
              wp_done

theorem verifyMacWithAddresses_placed_ok_of_hooks_gen [LibsignalPlacement]
    (cmStack saStack daStack : Nat)
    (hsa_le : saStack ≤ cmStack)
    (hda_le : daStack ≤ cmStack)
    (hcm_lt : cmStack + 288 < 2 ^ 64)
    (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (H : String → Option (State → State))
    (hdealloc : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsρ lsMacRustDeallocSym)
      (rustDeallocExternSpecWithStack A daStack))
    (hbb_all : ∀ (sp_cur : BitVec 64) (n : Nat), daStack ≤ n → n ≤ cmStack → ∀ (v : BitVec 8),
      subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
        (lsρ lsBlackBoxU8Sym)
        (session2BlackBoxSpecX sp_cur n v))
    (hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecWithStack A parse saStack)))
    (hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecWithStack C.F A cmStack))) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpecWithStack C.F A parse (cmStack + 288))) :=
  subroutine_ok_lscl_of_withVmaClState
    (verifyMacWithAddresses_placed_ok_of_hooks_gen_aux cmStack saStack daStack hsa_le hda_le hcm_lt
      C A parse H ⟨hdealloc, hbb_all, subroutine_ok_withVmaClState_of_lscl hser,
        subroutine_ok_withVmaClState_of_lscl hCompute⟩)

theorem verifyMacWithAddresses_placed_ok_of_compute [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpec)
    (hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec A parse)))
    (hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpec C.F A))) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A parse)) :=
  verifyMacWithAddresses_placed_ok_of_hooks_gen
    computeMacStack serializeAddressesStack allocHookStack
    (by decide) (by decide) (by decide) C A parse H
    (rustDeallocExternWithStack_of_rustDealloc (mac_ls_hook_ok_of_mem hdealloc) (by decide) (by decide))
    (fun sp_cur n _ _ v => blackBox_placed_ok sp_cur n hbb_raw v)
    hser
    hCompute

theorem verifyMacWithAddresses_placed_cro_ok_of_compute [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym) blackBoxSpec)
    (hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 61)
      (withLsCodeRoLoaded lsmpl (serializeAddressesSpec A parse)))
    (hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 60)
      (withLsCodeRoLoaded lsmpl (computeMacSpec C.F A))) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeRoLoaded lsmpl (verifyMacWithAddressesPlacedSpec C.F A parse)) :=
  subroutine_ok_lscro_of_withVmaClState
    (verifyMacWithAddresses_placed_ok_of_hooks_gen_aux
      computeMacStack serializeAddressesStack allocHookStack
      (by decide) (by decide) (by decide) C A parse H
      ⟨rustDeallocExternWithStack_of_rustDealloc (mac_ls_hook_ok_of_mem hdealloc) (by decide) (by decide),
       fun sp_cur n _ _ v => blackBox_placed_ok sp_cur n hbb_raw v,
       subroutine_ok_withVmaClState_of_lscro hser,
       subroutine_ok_withVmaClState_of_lscro hCompute⟩)

theorem verifyMacWithAddresses_placed_ok_of_compute_x [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (parse : UuidParser)
    (H : String → Option (State → State))
    (hdealloc : HookSat H lsMacRustDeallocSym (rustDeallocSpec A))
    (hbb_raw : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H) (lsρ lsBlackBoxU8Sym)
      (withStack blackBoxU8Spec extHookStack))
    (hser : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecX A parse)))
    (hCompute : subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (lsmpl.base 60)
      (withLsCodeLoaded lsmpl (computeMacSpecX C.F A))) :
    subroutine_ok ((blkPC_62).rebase (blkPl_62).base H)
      (blkPl_62).base
      (withLsCodeLoaded lsmpl (verifyMacWithAddressesPlacedSpecX C.F A parse)) :=
  verifyMacWithAddresses_placed_ok_of_hooks_gen
    computeMacStackX serializeAddressesStackX extHookStack
    (by decide) (by decide) (by decide) C A parse H
    (rustDeallocExternWithStack_of_rustDealloc (mac_ls_hook_ok_of_mem hdealloc) (by decide) (by decide))
    (fun sp_cur n hn hncm v => blackBox_placed_ok_x sp_cur n hbb_raw v hn (Nat.lt_of_le_of_lt hncm (by decide)))
    hser
    hCompute

end CryptoVerification.LibsignalTripleRatchet.Mac.VerifyMacWithAddresses
