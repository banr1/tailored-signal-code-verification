/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpoch
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCallees
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesLeavesExt
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesChainExt
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtA
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage2
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignature
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignatureExt
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes

/-!
# Cryptographic, Session, and Local Callee Contracts for `initiate`

Transfers the PQXDH and SPQR callee contracts onto `initProg img W` (`InitLocalCallees`) and
`initProgExt img ext` (`InitLocalCalleesExt`), and proves the handshake-crate local instantiations
`<kem::Key<Public>>::serialize [local#2]` and `core::ptr::drop_glue::<SessionStructure> [local#5]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## Symbol names -/

abbrev cliKemPublicKeySerializeName : String :=
  "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]"

abbrev cliDropSessionStructureName : String :=
  "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"

abbrev cliVerifySignatureName : String :=
  "<libsignal_core::curve::PublicKey>::verify_signature"

abbrev cliIsSameAccountName : String :=
  "<libsignal_protocol::identity_key::IdentityKey>::is_same_account"

abbrev cliCalculateAgreementName : String :=
  "<libsignal_core::curve::PrivateKey>::calculate_agreement"

abbrev cliDerivePubKeyBytesName : String :=
  "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes"

abbrev cliHandshakeDeriveName : String :=
  "<libsignal_protocol::pqxdh::HandshakeKeys>::derive"

abbrev cliKemCtSerializeName : String :=
  "<libsignal_protocol::kem::Ciphertext>::serialize"

abbrev cliRootKeyCreateChainName : String :=
  "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"

abbrev cliSpqrChainParamsName : String :=
  "libsignal_protocol::ratchet::spqr_chain_params"

abbrev cliSpqrInitialStateName : String :=
  "spqr::initial_state"

abbrev cliSessionStateNewName : String :=
  "<libsignal_protocol::state::session::SessionState>::new"

abbrev cliWithReceiverChainName : String :=
  "<libsignal_protocol::state::session::SessionState>::with_receiver_chain"

abbrev cliWithSenderChainName : String :=
  "<libsignal_protocol::state::session::SessionState>::with_sender_chain"

abbrev cliSetKyberCiphertextName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext"

abbrev cliSetUnackPreKeyMsgName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_pre_key_message"

abbrev cliSetUnackKyberIdName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id"

abbrev cliPromoteStateName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::promote_state"

theorem cliKemPublicKeySerialize_fnOff :
    libsignalSessionCode.fnOff cliKemPublicKeySerializeName =
      num% (ls_off% "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::kem::Key<libsignal_protocol::kem::Public>>::serialize [local#1]")

theorem cliDropSessionStructure_fnOff :
    libsignalSessionCode.fnOff cliDropSessionStructureName =
      num% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")

theorem cliVerifySignature_fnOff :
    libsignalSessionCode.fnOff cliVerifySignatureName =
      num% (ls_off% "<libsignal_core::curve::PublicKey>::verify_signature") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::verify_signature")

theorem cliIsSameAccount_fnOff :
    libsignalSessionCode.fnOff cliIsSameAccountName =
      num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::is_same_account") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::is_same_account")

theorem cliCalculateAgreement_fnOff :
    libsignalSessionCode.fnOff cliCalculateAgreementName =
      num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement")

theorem cliDerivePubKeyBytes_fnOff :
    libsignalSessionCode.fnOff cliDerivePubKeyBytesName =
      num% (ls_off% "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_core::curve::curve25519::PrivateKey>::derive_public_key_bytes")

theorem cliHandshakeDerive_fnOff :
    libsignalSessionCode.fnOff cliHandshakeDeriveName =
      num% (ls_off% "<libsignal_protocol::pqxdh::HandshakeKeys>::derive") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::pqxdh::HandshakeKeys>::derive")

theorem cliKemCtSerialize_fnOff :
    libsignalSessionCode.fnOff cliKemCtSerializeName =
      num% (ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::kem::Ciphertext>::serialize")

theorem cliRootKeyCreateChain_fnOff :
    libsignalSessionCode.fnOff cliRootKeyCreateChainName =
      num% (ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")

theorem cliSpqrChainParams_fnOff :
    libsignalSessionCode.fnOff cliSpqrChainParamsName =
      num% (ls_off% "libsignal_protocol::ratchet::spqr_chain_params") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "libsignal_protocol::ratchet::spqr_chain_params")

theorem cliSpqrInitialState_fnOff :
    libsignalSessionCode.fnOff cliSpqrInitialStateName =
      num% (ls_off% "spqr::initial_state") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "spqr::initial_state")

theorem cliSessionStateNew_fnOff :
    libsignalSessionCode.fnOff cliSessionStateNewName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionState>::new") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::new")

theorem cliWithReceiverChain_fnOff :
    libsignalSessionCode.fnOff cliWithReceiverChainName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionState>::with_receiver_chain") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::with_receiver_chain")

theorem cliWithSenderChain_fnOff :
    libsignalSessionCode.fnOff cliWithSenderChainName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionState>::with_sender_chain") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::with_sender_chain")

theorem cliSetKyberCiphertext_fnOff :
    libsignalSessionCode.fnOff cliSetKyberCiphertextName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext")

theorem cliSetUnackPreKeyMsg_fnOff :
    libsignalSessionCode.fnOff cliSetUnackPreKeyMsgName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_pre_key_message") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_pre_key_message")

theorem cliSetUnackKyberId_fnOff :
    libsignalSessionCode.fnOff cliSetUnackKyberIdName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id")

theorem cliPromoteState_fnOff :
    libsignalSessionCode.fnOff cliPromoteStateName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state") :=
  Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_state")

/-! ## `<kem::Key<Public>>::serialize [local#2]` contract -/

structure KemPubSerializeGhost where
  keyRef : BitVec 64
  kpkPtr : BitVec 64
  kpk : List (BitVec 8)

/-- Specification for `<kem::Key<Public>>::serialize [local#2]`: reads `(kpkPtr, 1568)` at `keyRef`,
allocates `1569` bytes, writes `0x08 :: kpk`, and returns `(ptr, 1569)` in `(x0, x1)`. -/
def kemPubSerializeSpec (A : RustAlloc) (img : Obj.Image) (stk : Nat) :
    Spec KemPubSerializeGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.kpkPtr ∧ s.readReg64 .x1 = 1568#64 ∧ x.kpk.length = 1568⌝ ∗
          (x.keyRef ↦₆₄ x.kpkPtr) ∗ ((x.keyRef + 8#64) ↦₆₄ 1568#64) ∗
          (x.kpkPtr ↦ₛ x.kpk) ∗ A.pool ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = 1569#64 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) 1569 1 ∗
          ((sf.readReg64 .x0) ↦ₛ (0x08#8 :: x.kpk)) ∗
          (x.keyRef ↦₆₄ x.kpkPtr) ∗ ((x.keyRef + 8#64) ↦₆₄ 1568#64) ∗
          (x.kpkPtr ↦ₛ x.kpk) ∗ A.pool ∗ stackAt s0.sp stk
      onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap }
    img

theorem kemPublicKeySerialize_local2_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliKemPublicKeySerializeName)
      (kemPubSerializeSpec A img stk) := by
  let _ := himg
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _hL => ?_
  exact (KemPubSerializeLocal2.kemPubKeySerialize_local2_full_ok W hh hstk).mono_outcome
    (x.keyRef, x.kpkPtr, x.kpk) R s0 hpc hrun hpre hsp (fun _ hout => hout)

/-! ## Signature verification specification and callee transfers -/

/-- Ghost arguments for `<PublicKey>::verify_signature`. -/
structure VerifySignatureGhost where
  pkPtr : BitVec 64
  pk : Pqxdh.Shared.Bytes
  msgPtr : BitVec 64
  m : Pqxdh.Shared.Bytes
  sigPtr : BitVec 64
  sig : Pqxdh.Shared.Bytes

/-- Separation-logic specification for `<PublicKey>::verify_signature` on `img`. -/
def verifySignatureSpec (P : SignalPqxdh.Primitives) (img : Obj.Image) :
    Spec VerifySignatureGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x0 = g.pkPtr ∧
          s.readReg64 .x1 = g.msgPtr ∧
          s.readReg64 .x2 = BitVec.ofNat 64 g.m.length ∧
          s.readReg64 .x3 = g.sigPtr ∧
          s.readReg64 .x4 = 64#64 ∧
          g.pk.length = 32 ∧
          (g.m.length = 33 ∨ g.m.length = 1569) ∧
          g.sig.length = 64⌝ ∗
          (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
          (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
          (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
          stackAt s.sp (Pqxdh.Shared.pqxdhHookStack + 1280)
      post := fun g s0 sf =>
        ⌜sf.readReg64 .x0 = (if P.sigVerify g.pk g.m g.sig = true then 1#64 else 0#64) ∧
          sf.trace = s0.trace⌝ ∗
          (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
          (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
          (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
          stackAt s0.sp (Pqxdh.Shared.pqxdhHookStack + 1280) }
    img

theorem dropSessionStructure_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliDropSessionStructureName)
      (FromRecordCallees.dropSessionStructureLocal2Spec A) := by
  let _ := himg
  exact Slots.subroutine_ok_cli_of_trTrap
    (CryptoVerification.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5.drop_session_structure5_ok_trap
      hh.allocHooks)

theorem verifySignature_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliVerifySignatureName)
      (verifySignatureSpec (modelPrims X ⟨W.C, W.Q⟩) img) := by
  let _ := hh
  apply Slots.subroutine_ok_cli_of_trTrap
  refine subroutine_ok_intro fun g R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [verifySignatureSpec, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfl, _hsym⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hpk, hm, hsig⟩, hmem⟩
  have hro := Pqxdh.Shared.sha512IV_holdsBytes himg hfl
  have hfsp_align : ((s0.sp - 1280#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1280#64 hsp (by decide)
  have hfsp_add : (s0.sp - 1280#64) + 1280#64 = s0.sp := by bv_omega
  have hH : Pqxdh.Shared.PqxdhHookContracts (modelPrims X ⟨W.C, W.Q⟩) A img (cliExterns W) :=
    Slots.cliExterns_pqxdhHookContracts W X img
  have hwp := Pqxdh.Shared.verifySignature_sepWP_trap (C := W.C)
    (modelPrims X ⟨W.C, W.Q⟩) A img (cliExterns W)
    himg (Pqxdh.Initiator.structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩) hH
    s0 (s0.sp - 1280#64) g.pkPtr g.msgPtr g.sigPtr (s0.readReg64 .x30)
    g.pk g.m g.sig emp
    hro hpk hm hsig hfsp_align hrun hpc hfsp_add.symm hx0 hx1 hx2 hx3 hx4 rfl
  have hmem' : s0.mem ⊨
      ((g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
       (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
       (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
       stackAt ((s0.sp - 1280#64) + 1280#64) (Pqxdh.Shared.pqxdhHookStack + 1280) ∗ emp) ∗ R := by
    rw [hfsp_add, sepConj_emp]
    exact Arm64.Satisfies.of_eq hmem (by ac_rfl)
  obtain ⟨sf, hsteps, ⟨hpc_f, hrun_f, Pf, hmf, hPf, _, _, hsp_f, hx0_f,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs, htr⟩ | ⟨_hoom, hfalse⟩⟩ :=
    SepWP.elim hwp hmem' hL
  · rw [hfsp_add] at hsp_f hPf
    rw [sepConj_emp] at hPf
    refine ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, ?_,
      ⟨hsp_f, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩⟩⟩
    dsimp only [verifySignatureSpec, Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_f, htr⟩, ?_⟩
    exact Arm64.Satisfies.mono
      (sepConj_mono_left (Entails.trans hPf (Entails.of_eq (by ac_rfl)))) hmf
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem isSameAccount_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliIsSameAccountName)
      (Pqxdh.WireEntries.isSameAccountDistinctSpec A uuidTryParse) := by
  let _ := himg; let _ := hh
  exact Slots.subroutine_ok_cli_of_trTrap
    (Pqxdh.WireEntries.isSameAccountEqDistinct_ok_trap img.base W.C A (cliExterns W))

theorem calculateAgreement_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliCalculateAgreementName)
      (Pqxdh.Initiator.pqxdhCalculateAgreementFrozenSpec (modelPrims X ⟨W.C, W.Q⟩) A img) := by
  exact Slots.subroutine_ok_cli_of_trTrap
    (Pqxdh.Initiator.calculateAgreement_frozen_ok_trap himg
      (Pqxdh.ResponderCore.pqxdhCalculateAgreement_ok_trap
        (Pqxdh.ResponderCore.primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩)
        himg hh.allocHooks))

theorem derivePubKeyBytes_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliDerivePubKeyBytesName)
      (derivePublicKeyBytesSpec W.C.pubKey) := by
  let _ := himg; let _ := hh
  exact Slots.subroutine_ok_cli_of_trTrap derive_public_key_bytes_ok_trap

theorem handshakeDerive_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliHandshakeDeriveName)
      (Pqxdh.Initiator.handshakeKeysDeriveSpec (modelPrims X ⟨W.C, W.Q⟩) A img) := by
  let _ := hh
  exact Slots.subroutine_ok_cli_of_trTrap
    (Pqxdh.ResponderCore.handshakeKeysDerive_ok_trap himg
      (Pqxdh.Initiator.structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩)
      (Pqxdh.ResponderCore.primitivesMatchCrypto_modelPrims X ⟨W.C, W.Q⟩))

theorem kemCtSerialize_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliKemCtSerializeName)
      (Pqxdh.kemCiphertextSerializeSpec A) := by
  let _ := himg
  exact Slots.subroutine_ok_cli_of_trTrap (Pqxdh.kemCiphertextSerialize_ok_trap hh.allocHooks)

theorem rootKeyCreateChain_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliRootKeyCreateChainName)
      ((createChainSpec W.C A).inImage img) := by
  exact Slots.subroutine_ok_cli_of_trTrap
    (Pqxdh.Initiator.pqxdh_createChain_ok_trap himg hh.allocHooks)

theorem spqrChainParams_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliSpqrChainParamsName)
      Pqxdh.spqrChainParamsSpec := by
  let _ := himg; let _ := hh
  exact Slots.subroutine_ok_cli_of_trTrap Pqxdh.spqrChainParams_ok_trap

theorem spqrInitialState_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliSpqrInitialStateName)
      (CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX A W.C.F img) := by
  exact CryptoVerification.SpqrV1.Top.InitialState.initial_state_ok_x himg hh.allocContracts
    (Slots.authNewOkX_cli_of_hooks W himg hh.allocContracts hh.allocZeroed)

theorem sessionStateNew_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliSessionStateNewName)
      (Pqxdh.Initiator.sessionStateNewSpec A img) := by
  let _ := himg
  exact Slots.subroutine_ok_cli_of_trTrap (Pqxdh.Initiator.sessionStateNew_base_ok_trap hh.allocHooks)

theorem withReceiverChain_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliWithReceiverChainName)
      (Pqxdh.Initiator.withReceiverChainEmptySpec A img) := by
  let _ := himg
  exact Slots.subroutine_ok_cli_of_trTrap
    (Pqxdh.Initiator.withReceiverChain_empty_base_ok_trap hh.allocHooks)

theorem withSenderChain_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliWithSenderChainName)
      (Pqxdh.Initiator.withSenderChainNoneSpec A img) := by
  let _ := himg
  exact Slots.subroutine_ok_cli_of_trTrap
    (Pqxdh.Initiator.withSenderChain_none_base_ok_trap hh.allocHooks)

theorem setKyberCiphertext_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliSetKyberCiphertextName)
      Pqxdh.setKyberCiphertextNoneSpec := by
  let _ := himg; let _ := hh
  exact Slots.subroutine_ok_cli_of_trTrap Pqxdh.setKyberCiphertext_none_ok_trap

/-- Specification for `<SessionState>::set_unacknowledged_pre_key_message` at `now = UNIX_EPOCH`
(`x5 = 0`, `w6 = 0`), refining `setUnackPreKeyMsgExactStackSpec`. -/
def setUnackPreKeyMsgEpochSpec (A : RustAlloc) (img : Obj.Image) :
    Spec Pqxdh.TopLevel.SetUnackExactGhost :=
  { Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec A img with
    pre := fun g s =>
      ⌜s.readReg64 .x5 = 0#64 ∧ (s.readReg64 .x6).setWidth 32 = 0#32⌝ ∗
        (Pqxdh.TopLevel.setUnackPreKeyMsgExactStackSpec A img).pre g s }

theorem setUnackPreKeyMsg_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliSetUnackPreKeyMsgName)
      (setUnackPreKeyMsgEpochSpec A img) := by
  let _ := himg
  exact Slots.setUnackPreKeyMsg_exact_stack_epoch_ok_cli W hh.allocHooks

theorem setUnackKyberId_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliSetUnackKyberIdName)
      Pqxdh.setUnackKyberPreKeyIdSpec := by
  let _ := himg; let _ := hh
  exact Slots.subroutine_ok_cli_of_trTrap Pqxdh.setUnackKyberPreKeyId_ok_trap

theorem promoteState_cli_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W)) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr cliPromoteStateName)
      Pqxdh.ResponderStore.promoteStateEmptySpec := by
  let _ := himg; let _ := hh
  exact Slots.subroutine_ok_cli_of_trTrap Pqxdh.ResponderStore.promote_state_empty_ok_trap

/-! ## Bundled local and PQXDH/SPQR callees (`InitLocalCallees`) -/

structure InitLocalCallees (img : Obj.Image) (A : RustAlloc) (W : CliHooks)
    (stk : Nat) : Prop where
  kemPubSerialize : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliKemPublicKeySerializeName)
    (kemPubSerializeSpec A img (stk - cliInitiateFrame))
  dropSessionStructure : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliDropSessionStructureName)
    (FromRecordCallees.dropSessionStructureLocal2Spec A)
  verifySignature : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliVerifySignatureName)
    (verifySignatureSpec (modelPrims X ⟨W.C, W.Q⟩) img)
  isSameAccount : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliIsSameAccountName)
    (Pqxdh.WireEntries.isSameAccountDistinctSpec A uuidTryParse)
  calculateAgreement : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliCalculateAgreementName)
    (Pqxdh.Initiator.pqxdhCalculateAgreementFrozenSpec (modelPrims X ⟨W.C, W.Q⟩) A img)
  derivePubKeyBytes : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliDerivePubKeyBytesName)
    (derivePublicKeyBytesSpec W.C.pubKey)
  handshakeDerive : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliHandshakeDeriveName)
    (Pqxdh.Initiator.handshakeKeysDeriveSpec (modelPrims X ⟨W.C, W.Q⟩) A img)
  kemCtSerialize : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliKemCtSerializeName)
    (Pqxdh.kemCiphertextSerializeSpec A)
  rootKeyCreateChain : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliRootKeyCreateChainName)
    ((createChainSpec W.C A).inImage img)
  spqrChainParams : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliSpqrChainParamsName)
    Pqxdh.spqrChainParamsSpec
  spqrInitialState : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliSpqrInitialStateName)
    (CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX A W.C.F img)
  sessionStateNew : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliSessionStateNewName)
    (Pqxdh.Initiator.sessionStateNewSpec A img)
  withReceiverChain : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliWithReceiverChainName)
    (Pqxdh.Initiator.withReceiverChainEmptySpec A img)
  withSenderChain : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliWithSenderChainName)
    (Pqxdh.Initiator.withSenderChainNoneSpec A img)
  setKyberCiphertext : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliSetKyberCiphertextName)
    Pqxdh.setKyberCiphertextNoneSpec
  setUnackPreKeyMsg : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliSetUnackPreKeyMsgName)
    (setUnackPreKeyMsgEpochSpec A img)
  setUnackKyberId : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliSetUnackKyberIdName)
    Pqxdh.setUnackKyberPreKeyIdSpec
  promoteState : subroutine_ok (initProg img W)
    ((initProg img W).fnAddr cliPromoteStateName)
    Pqxdh.ResponderStore.promoteStateEmptySpec

/-- Discharges all `InitLocalCallees` fields on `initProg img W` at residual stack `stk - cliInitiateFrame`. -/
theorem initLocalCallees_ok {img : Obj.Image} {A : RustAlloc} (W : CliHooks) (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitLocalCallees img A W stk := by
  exact
    { kemPubSerialize := kemPublicKeySerialize_local2_ok W himg hh (by
        have h1 := stk_sub_ge_base hstk
        have hext : extHookStack ≤ 65536 := by decide
        omega)
      dropSessionStructure := dropSessionStructure_cli_ok W himg hh
      verifySignature := fun X => verifySignature_cli_ok W X himg hh
      isSameAccount := isSameAccount_cli_ok W himg hh
      calculateAgreement := fun X => calculateAgreement_cli_ok W X himg hh
      derivePubKeyBytes := derivePubKeyBytes_cli_ok W himg hh
      handshakeDerive := fun X => handshakeDerive_cli_ok W X himg hh
      kemCtSerialize := kemCtSerialize_cli_ok W himg hh
      rootKeyCreateChain := rootKeyCreateChain_cli_ok W himg hh
      spqrChainParams := spqrChainParams_cli_ok W himg hh
      spqrInitialState := spqrInitialState_cli_ok W himg hh
      sessionStateNew := sessionStateNew_cli_ok W himg hh
      withReceiverChain := withReceiverChain_cli_ok W himg hh
      withSenderChain := withSenderChain_cli_ok W himg hh
      setKyberCiphertext := setKyberCiphertext_cli_ok W himg hh
      setUnackPreKeyMsg := setUnackPreKeyMsg_cli_ok W himg hh
      setUnackKyberId := setUnackKyberId_cli_ok W himg hh
      promoteState := promoteState_cli_ok W himg hh }

/-! ## Extern-parameterized callees (`InitLocalCalleesExt`) -/

theorem kemPublicKeySerialize_local2_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliKemPublicKeySerializeName)
      (kemPubSerializeSpec A img stk) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _hL => ?_
  exact (KemPubSerializeLocal2.kemPubKeySerialize_local2_full_ext_ok
    (Slots.ext_allocContractsX hOk img) hstk).mono_outcome
    (x.keyRef, x.kpkPtr, x.kpk) R s0 hpc hrun hpre hsp (fun _ hout => hout)

theorem dropSessionStructure_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliDropSessionStructureName)
      (FromRecordCallees.dropSessionStructureLocal2Spec A) :=
  CryptoVerification.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5.drop_session_structure5_ok_ext
    (Slots.ext_allocHooks hOk)

/-- Extern-parameterized specification for `<PublicKey>::verify_signature` at `verifySigStackExt`. -/
def verifySignatureExtSpec (P : SignalPqxdh.Primitives) (img : Obj.Image) :
    Spec VerifySignatureGhost :=
  Spec.inImage
    { pre := fun g s =>
        ⌜s.readReg64 .x0 = g.pkPtr ∧
          s.readReg64 .x1 = g.msgPtr ∧
          s.readReg64 .x2 = BitVec.ofNat 64 g.m.length ∧
          s.readReg64 .x3 = g.sigPtr ∧
          s.readReg64 .x4 = 64#64 ∧
          g.pk.length = 32 ∧
          (g.m.length = 33 ∨ g.m.length = 1569) ∧
          g.sig.length = 64⌝ ∗
          (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
          (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
          (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
          stackAt s.sp Pqxdh.Shared.verifySigStackExt
      post := fun g s0 sf =>
        ⌜sf.readReg64 .x0 = (if P.sigVerify g.pk g.m g.sig = true then 1#64 else 0#64) ∧
          sf.trace = s0.trace⌝ ∗
          (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
          (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
          (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
          stackAt s0.sp Pqxdh.Shared.verifySigStackExt }
    img

theorem verifySignature_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (X : UnreachedPqxdhPrimitives)
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliVerifySignatureName)
      (verifySignatureExtSpec (modelPrims X P) img) := by
  refine subroutine_ok_intro fun g R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [verifySignatureExtSpec, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfl, _hsym⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hpk, hm, hsig⟩, hmem⟩
  have hro := Pqxdh.Shared.sha512IV_holdsBytes himg hfl
  have hfsp_align : ((s0.sp - 1280#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1280#64 hsp (by decide)
  have hfsp_add : (s0.sp - 1280#64) + 1280#64 = s0.sp := by bv_omega
  have hH : Pqxdh.Shared.PqxdhHookContractsExt (modelPrims X P) A img (cliExternsWith ext) :=
    Pqxdh.Shared.PqxdhHookContractsExt.of_cliExternsOk X img hOk
  have hwp := Pqxdh.Shared.verifySignature_sepWP_ext
    (modelPrims X P) A img (cliExternsWith ext)
    himg (Pqxdh.Initiator.structuralPrims_initiatorModelPrims X P) hH
    s0 (s0.sp - 1280#64) g.pkPtr g.msgPtr g.sigPtr (s0.readReg64 .x30)
    g.pk g.m g.sig emp
    hro hpk hm hsig hfsp_align hrun hpc hfsp_add.symm hx0 hx1 hx2 hx3 hx4 rfl
  have hmem' : s0.mem ⊨
      ((g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
       (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
       (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
       stackAt ((s0.sp - 1280#64) + 1280#64) Pqxdh.Shared.verifySigStackExt ∗ emp) ∗ R := by
    rw [hfsp_add, sepConj_emp]
    exact Arm64.Satisfies.of_eq hmem (by ac_rfl)
  obtain ⟨sf, hsteps, ⟨hpc_f, hrun_f, Pf, hmf, hPf, _, _, hsp_f, hx0_f,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs, htr⟩ | ⟨_hoom, hfalse⟩⟩ :=
    SepWP.elim hwp hmem' hL
  · rw [hfsp_add] at hsp_f hPf
    rw [sepConj_emp] at hPf
    refine ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, ?_,
      ⟨hsp_f, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩⟩⟩
    dsimp only [verifySignatureExtSpec, Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_f, htr⟩, ?_⟩
    exact Arm64.Satisfies.mono
      (sepConj_mono_left (Entails.trans hPf (Entails.of_eq (by ac_rfl)))) hmf
  · exact (not_satisfies_false_sepConj hfalse).elim

theorem isSameAccount_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliIsSameAccountName)
      ((isSameAccountDistinctAtSpec A uuidTryParse isSameAccountExtStack).inImage img) :=
  isSameAccount_inImage_ext_ok hOk

theorem isSameAccount_raw_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliIsSameAccountName)
      (isSameAccountDistinctAtSpec A uuidTryParse isSameAccountExtStack) :=
  isSameAccount_ext_ok hOk

theorem calculateAgreement_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (X : UnreachedPqxdhPrimitives)
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliCalculateAgreementName)
      (Pqxdh.Initiator.pqxdhCalculateAgreementFrozenSpecExt (modelPrims X P) A img) :=
  Pqxdh.Initiator.calculateAgreement_frozen_ok_of_cliExternsOk X himg hOk

theorem derivePubKeyBytes_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliDerivePubKeyBytesName)
      (derivePublicKeyBytesStackSpec P.C.pubKey extHookStack) :=
  derivePubKeyBytes_ext_ok hOk

theorem derivePubKeyBytes_inImage_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliDerivePubKeyBytesName)
      ((derivePublicKeyBytesStackSpec P.C.pubKey extHookStack).inImage img) :=
  derivePubKeyBytes_inImage_ext_ok hOk

theorem handshakeDerive_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (X : UnreachedPqxdhPrimitives)
    (himg : Obj.Loads libsignalSessionImage img)
    (hext : Pqxdh.Initiator.PqxdhHkdfExtractOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hexp : Pqxdh.Initiator.PqxdhHkdfExpandMultiInfoOk_ext
      (modelPrims X P) img (cliExternsWith ext)) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliHandshakeDeriveName)
      (Pqxdh.Initiator.handshakeKeysDeriveSpecExt (modelPrims X P) A img) :=
  Pqxdh.ResponderCore.handshakeKeysDerive_ok_ext himg
    (Pqxdh.Initiator.structuralPrims_initiatorModelPrims X P) hext hexp

theorem kemCtSerialize_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliKemCtSerializeName)
      (kemCiphertextSerializeExtSpec A) :=
  kemCtSerialize_ext_ok hOk

theorem rootKeyCreateChain_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliRootKeyCreateChainName)
      ((Keys.createChainSpecAt P.C A extractStackExt).inImage img) :=
  rootKeyCreateChain_at_extractStackExt_ok himg hOk

theorem spqrChainParams_cli_ext_ok {img : Obj.Image}
    {ext : String → Option (State → State)} :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSpqrChainParamsName)
      Pqxdh.spqrChainParamsSpec :=
  spqrChainParams_ext_ok

theorem spqrInitialState_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hSpqrInit : CryptoVerification.SpqrV1.Top.InitialState.InitialStateOkXExt
      img A P.C.F (cliExternsWith ext)) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSpqrInitialStateName)
      (CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt A P.C.F img) :=
  hSpqrInit

theorem sessionStateNew_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSessionStateNewName)
      (Pqxdh.Initiator.sessionStateNewSpec A img) :=
  sessionStateNew_ext_ok hOk

theorem withReceiverChain_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliWithReceiverChainName)
      (Pqxdh.Initiator.withReceiverChainEmptySpec A img) :=
  withReceiverChain_ext_ok hOk

theorem withSenderChain_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliWithSenderChainName)
      (Pqxdh.Initiator.withSenderChainNoneSpec A img) :=
  withSenderChain_ext_ok hOk

theorem setKyberCiphertext_cli_ext_ok {img : Obj.Image}
    {ext : String → Option (State → State)} :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSetKyberCiphertextName)
      Pqxdh.setKyberCiphertextNoneSpec :=
  setKyberCiphertext_ext_ok

theorem setUnackPreKeyMsg_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSetUnackPreKeyMsgName)
      (Slots.setUnackPreKeyMsgExtStackEpochSpec A img) :=
  Slots.setUnackPreKeyMsg_ext_stack_epoch_ok hOk

theorem setUnackKyberId_cli_ext_ok {img : Obj.Image}
    {ext : String → Option (State → State)} :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSetUnackKyberIdName)
      Pqxdh.setUnackKyberPreKeyIdSpec :=
  setUnackKyberId_ext_ok

theorem promoteState_cli_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliPromoteStateName)
      (promoteStateEmptyExtSpec img (extHookStack + 32)) :=
  promoteState_ext_ok hOk

/-- Bundled extern-parameterized local and PQXDH/SPQR callees on `initProgExt img ext`. -/
structure InitLocalCalleesExt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) (stk : Nat) : Prop where
  kemPubSerialize : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliKemPublicKeySerializeName)
    (kemPubSerializeSpec A img (stk - cliInitiateFrame))
  dropSessionStructure : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliDropSessionStructureName)
    (FromRecordCallees.dropSessionStructureLocal2Spec A)
  verifySignature : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliVerifySignatureName)
    (verifySignatureExtSpec (modelPrims X P) img)
  isSameAccount : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliIsSameAccountName)
    ((isSameAccountDistinctAtSpec A uuidTryParse isSameAccountExtStack).inImage img)
  calculateAgreement : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliCalculateAgreementName)
    (Pqxdh.Initiator.pqxdhCalculateAgreementFrozenSpecExt (modelPrims X P) A img)
  derivePubKeyBytes : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliDerivePubKeyBytesName)
    (derivePublicKeyBytesStackSpec P.C.pubKey extHookStack)
  handshakeDerive : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliHandshakeDeriveName)
    (Pqxdh.Initiator.handshakeKeysDeriveSpecExt (modelPrims X P) A img)
  kemCtSerialize : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliKemCtSerializeName)
    (kemCiphertextSerializeExtSpec A)
  rootKeyCreateChain : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliRootKeyCreateChainName)
    ((Keys.createChainSpecAt P.C A extractStackExt).inImage img)
  spqrChainParams : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliSpqrChainParamsName)
    Pqxdh.spqrChainParamsSpec
  spqrInitialState : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliSpqrInitialStateName)
    (CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecXExt A P.C.F img)
  sessionStateNew : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliSessionStateNewName)
    (Pqxdh.Initiator.sessionStateNewSpec A img)
  withReceiverChain : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliWithReceiverChainName)
    (Pqxdh.Initiator.withReceiverChainEmptySpec A img)
  withSenderChain : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliWithSenderChainName)
    (Pqxdh.Initiator.withSenderChainNoneSpec A img)
  setKyberCiphertext : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliSetKyberCiphertextName)
    Pqxdh.setKyberCiphertextNoneSpec
  setUnackPreKeyMsg : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliSetUnackPreKeyMsgName)
    (Slots.setUnackPreKeyMsgExtStackEpochSpec A img)
  setUnackKyberId : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliSetUnackKyberIdName)
    Pqxdh.setUnackKyberPreKeyIdSpec
  promoteState : subroutine_ok (initProgExt img ext)
    ((initProgExt img ext).fnAddr cliPromoteStateName)
    (promoteStateEmptyExtSpec img (extHookStack + 32))

/-- Discharges all `InitLocalCalleesExt` fields on `initProgExt img ext` from `CliExternsOk P A ext`. -/
theorem initLocalCallees_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (B : RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hHkdfExt : ∀ (X : UnreachedPqxdhPrimitives),
      Pqxdh.Initiator.PqxdhHkdfExtractOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hHkdfExp : ∀ (X : UnreachedPqxdhPrimitives),
      Pqxdh.Initiator.PqxdhHkdfExpandMultiInfoOk_ext (modelPrims X P) img (cliExternsWith ext))
    (hSpqrInit : CryptoVerification.SpqrV1.Top.InitialState.InitialStateOkXExt
      img A P.C.F (cliExternsWith ext))
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitLocalCalleesExt img P A ext stk := by
  exact
    { kemPubSerialize := kemPublicKeySerialize_local2_ext_ok hOk (by
        have h1 := stk_sub_ge_base hstk
        have hext : extHookStack ≤ 65536 := by decide
        omega)
      dropSessionStructure := dropSessionStructure_cli_ext_ok hOk
      verifySignature := fun X => verifySignature_cli_ext_ok X himg hOk
      isSameAccount := isSameAccount_cli_ext_ok hOk
      calculateAgreement := fun X => calculateAgreement_cli_ext_ok X himg hOk
      derivePubKeyBytes := derivePubKeyBytes_cli_ext_ok hOk
      handshakeDerive := fun X => handshakeDerive_cli_ext_ok X himg (hHkdfExt X) (hHkdfExp X)
      kemCtSerialize := kemCtSerialize_cli_ext_ok hOk
      rootKeyCreateChain := rootKeyCreateChain_cli_ext_ok himg hOk
      spqrChainParams := spqrChainParams_cli_ext_ok
      spqrInitialState := spqrInitialState_cli_ext_ok hSpqrInit
      sessionStateNew := sessionStateNew_cli_ext_ok hOk
      withReceiverChain := withReceiverChain_cli_ext_ok hOk
      withSenderChain := withSenderChain_cli_ext_ok hOk
      setKyberCiphertext := setKyberCiphertext_cli_ext_ok
      setUnackPreKeyMsg := setUnackPreKeyMsg_cli_ext_ok hOk
      setUnackKyberId := setUnackKyberId_cli_ext_ok
      promoteState := promoteState_cli_ext_ok hOk }

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
