/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Apply
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Decode, `.rodata`, and Key-Partition Helpers for `OutgoingTripleRatchet::from_session_state`

Instruction decode facts, `.rodata` string literal lemmas, callee bridges, and 32-byte key
partition lemmas for `<OutgoingTripleRatchet>::from_session_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.Ratchet CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem zeroExtend64_setWidth32 (v : BitVec 32) : (v.zeroExtend 64).setWidth 32 = v := by bv_kernel
theorem zeroExtend64_setWidth16 (v : BitVec 16) : (v.zeroExtend 64).setWidth 16 = v := by bv_kernel
theorem zeroExtend32_setWidth16 (v : BitVec 16) : (v.zeroExtend 32).setWidth 16 = v := by bv_kernel
theorem zeroExtend64_setWidth8 (v : BitVec 8) : (v.zeroExtend 64).setWidth 8 = v := by bv_kernel
theorem zeroExtend32_setWidth8 (v : BitVec 8) : (v.zeroExtend 32).setWidth 8 = v := by bv_kernel

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_setWidth32 zeroExtend64_setWidth16 zeroExtend32_setWidth16
  zeroExtend64_setWidth8 zeroExtend32_setWidth8

/-! ## Instruction decode lemmas for `OTR::from_session_state` -/

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") → (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 1304)]

/-! ## `.rodata` string literal lemmas for `OTR::from_session_state` -/

theorem rodata_0x40400_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 104) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 108)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 20 = invalidSessionStructureStr .missingSenderChain := by
  rfl_kernel

namespace FromSessionStateFacts

theorem img_dataOff : libsignalSessionImage.dataOff = num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)) := rfl

theorem img_data_len_ge {n : Nat} (h : n ≤ 0x3b78) : n ≤ libsignalSessionImage.data.length :=
  Nat.le_trans h (Nat.le_of_ble_eq_true (by rfl_kernel))

theorem of_rodata_loads_eq {li : Arm64.Obj.LinkedImage} {img : Arm64.Obj.Image}
    {m : Memory} {P : SepProp} (himg : Arm64.Obj.Loads li img)
    {dataOff : Nat} (hdo : li.dataOff = dataOff)
    {secOff secLen : Nat} {bs : List (BitVec 8)}
    (hsec : (secOff, secLen) ∈ li.roData)
    (hoff : dataOff ≤ secOff) (hlen : secLen < 2 ^ 32)
    (hdlen : secOff - dataOff + secLen ≤ li.data.length)
    (hrel : li.relocs.all
      (fun r => decide (r.off + r.width ≤ secOff - dataOff ∨ secOff - dataOff + secLen ≤ r.off)) = true)
    (heq : (li.data.drop (secOff - dataOff)).take secLen = bs)
    (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + BitVec.ofNat 64 secOff) ↦ᵣ bs) ∗ P := by
  subst heq
  exact ProofLib.Satisfies.of_rodata_loads himg hdo hsec hoff hlen hdlen hrel hro hP

end FromSessionStateFacts

theorem rodata_missingSenderChain_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 104) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 108))) ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗ P :=
  FromSessionStateFacts.of_rodata_loads_eq himg FromSessionStateFacts.img_dataOff
    (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (FromSessionStateFacts.img_data_len_ge (by decide)) (by rfl_kernel) rodata_0x40400_eq hro hP

theorem rodata_0x4176c_eq :
    (libsignalSessionImage.data.drop (num% (ls_str% "version does not fit in u8") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 26 = invalidSessionStructureStr .versionTooLarge := by
  rfl_kernel

theorem rodata_versionTooLarge_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "version does not fit in u8")) ↦ᵣ invalidSessionStructureStr .versionTooLarge) ∗ P :=
  FromSessionStateFacts.of_rodata_loads_eq himg FromSessionStateFacts.img_dataOff
    (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (FromSessionStateFacts.img_data_len_ge (by decide)) (by rfl_kernel) rodata_0x4176c_eq hro hP

theorem rodata_0x40ce0_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 27 = invalidSessionStructureStr .missingRemoteIdentity := by
  rfl_kernel

theorem rodata_missingRemoteIdentity_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗ P :=
  FromSessionStateFacts.of_rodata_loads_eq himg FromSessionStateFacts.img_dataOff
    (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (FromSessionStateFacts.img_data_len_ge (by decide)) (by rfl_kernel) rodata_0x40ce0_eq hro hP

/-! ## `adrp` page alignment lemmas for `OTR::from_session_state` -/

theorem fnAddr_adrp_b7fc {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr otrFromName + 104#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::sealed_sender::ServerCertificate>::deserialize" + 156)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), BitVec.add_assoc,
    adrp_page_of_aligned hb]
  rfl

theorem fnAddr_adrp_b8f4 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr otrFromName + 352#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::sealed_sender::ServerCertificate>::deserialize" + 156)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), BitVec.add_assoc,
    adrp_page_of_aligned hb]
  rfl

theorem fnAddr_adrp_ba80 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr otrFromName + 748#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "<libsignal_protocol::sealed_sender::ServerCertificate>::deserialize" + 156)) := by
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), BitVec.add_assoc,
    adrp_page_of_aligned hb]
  rfl

/-! ## `pkTryFromCodeSpec` on valid DJB public keys -/

/-- Specialized `pkTryFromSpec` when `PublicKey.deserialize bs = .ok pk`. -/
def pkTryFromOkSpec (img : Obj.Image) : Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out ∧
      PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 40 ∗ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)
  post := fun (p, bs, pk, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion (out + 33#64) 7 ∗ ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64)

theorem pkTryFromOk_ok_at_ext {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff pkTryFromName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (pkTryFromOkSpec img) := by
  refine subroutine_ok_map (pk_try_from_ok_at_ext img ext himg name k hk) ?_
  rintro ⟨p, bs, pk, out⟩ R s0 hpre
  simp only [pkTryFromOkSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, logOff, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, logOff, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    simp only [pkTryFromOkSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact hpost

theorem pkTryFromOk_ok_at_tripleRatchet {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff pkTryFromName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr name + BitVec.ofNat 64 k)
      (pkTryFromOkSpec img) :=
  pkTryFromOk_ok_at_ext himg hk

/-! ## Callee address bridges for `OTR::from_session_state` -/

theorem deserialize_ok_at_otrFrom_ext {b : BitVec 64} {ext : String → Option (State → State)}
    (h : DeserializeExtOk b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr otrFromName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"))
      (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec b) := by
  have heq : (tripleRatchetProgAtExt b ext).fnAddr otrFromName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") =
      (tripleRatchetProgAtExt b ext).fnAddr deserializeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize")]
    bv_lin
  rw [heq]; exact h

theorem deserialize_ok_at_otrFrom {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : DeserializeOk b C ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr otrFromName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"))
      (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec b) :=
  deserialize_ok_at_otrFrom_ext h

def remoteIdentityKeyOtrSpec (A : RustAlloc) (img : Obj.Image) : Spec RemoteIdentityKeyGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.ret ∧
      (match x.rem with
       | none => x.g.bytes = []
       | some ik => PublicKey.deserialize x.g.bytes = .ok ik.publicKey)⌝ ∗
      vecGhostAt A x.g (x.ss + 0x18#64) ∗ memRegion x.ret 34 ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s.sp remoteIdentityKeyStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecGhostAt A x.g (x.ss + 0x18#64) ∗ remoteIdentityOkAt x.ret x.rem ∗
      ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ stackAt s0.sp remoteIdentityKeyStack

theorem remoteIdentityKey_ok_at_otrFrom_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : RemoteIdentityKeyExtOk img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"))
      (remoteIdentityKeyOtrSpec A img) := by
  have heq : (tripleRatchetProgAtExt img.base ext).fnAddr otrFromName + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state") =
      (tripleRatchetProgAtExt img.base ext).fnAddr remoteIdentityKeyName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::remote_identity_key")]
    bv_lin
  rw [heq]; exact h

theorem remoteIdentityKey_ok_at_otrFrom {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : RemoteIdentityKeyOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrFromName + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" - ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"))
      (remoteIdentityKeyOtrSpec A img) :=
  remoteIdentityKey_ok_at_otrFrom_ext h

theorem dropSpe_ok_at_otrFrom_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropSpeExtOk img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr otrFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")))
      ((dropSpeSpec A).inImage img) := by
  have heq : (tripleRatchetProgAtExt img.base ext).fnAddr otrFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state"), (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")]
    bv_lin
  rw [heq]; exact h

theorem dropSpe_ok_at_otrFrom {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (h : DropSpeOk img C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state")))
      ((dropSpeSpec A).inImage img) :=
  dropSpe_ok_at_otrFrom_ext h

/-! ## Pure model and ghost relation lemmas for `OTR::from_session_state` -/

theorem agreeExceptPq_afterOtrFrom (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    G.AgreeExceptPq (afterOtrFrom G st) := by
  unfold afterOtrFrom SessionGhost.AgreeExceptPq
  cases st.senderChain <;> rfl

theorem otrFrom_model_none (x : OtrFromGhost) (h : x.st.senderChain = none) :
    x.model = (.error (.invalidSessionStructure .missingSenderChain), x.st) := by
  unfold OtrFromGhost.model OutgoingTripleRatchet.fromSessionState Mut.exec
  dsimp only [bind, ExceptT.bind, ExceptT.mk, StateT.run, ExceptT.run, StateT.bind,
    ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, Pure.pure, ExceptT.pure,
    StateT.pure, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map,
    throw, throwThe, MonadExceptOf.throw]
  rw [h]
  rfl

theorem otrFrom_model_verTooLarge (x : OtrFromGhost) {sc : SenderChain}
    (hsc : x.st.senderChain = some sc) (hver : 256 ≤ x.st.version.toNat) :
    x.model = (.error (.invalidSessionStructure .versionTooLarge),
      { x.st with pqRatchetState := [] }) := by
  unfold OtrFromGhost.model OutgoingTripleRatchet.fromSessionState Mut.exec
    SessionState.takePqRatchetState
  dsimp only [bind, ExceptT.bind, ExceptT.mk, StateT.run, ExceptT.run, StateT.bind,
    ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, Pure.pure, ExceptT.pure,
    StateT.pure, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw]
  have hv : ({ x.st with pqRatchetState := ([] : List (BitVec 8)) } :
      SessionState (List (BitVec 8))).version = x.st.version := rfl
  rw [hsc]
  dsimp only [bind, StateT.bind, StateT.map, StateT.modifyGet, StateT.get, StateT.pure,
    Pure.pure, ExceptT.bindCont, default]
  rw [hv, ite_eq_left_iff.mpr (fun h => absurd hver h), hsc]
  rfl

theorem otrFrom_model_noRemote (x : OtrFromGhost) {sc : SenderChain}
    (hsc : x.st.senderChain = some sc) (hver : ¬ 256 ≤ x.st.version.toNat)
    (hrem : x.st.remoteIdentity = none) :
    x.model = (.error (.invalidSessionStructure .missingRemoteIdentity),
      { x.st with pqRatchetState := [] }) := by
  unfold OtrFromGhost.model OutgoingTripleRatchet.fromSessionState Mut.exec
    SessionState.takePqRatchetState
  dsimp only [bind, ExceptT.bind, ExceptT.mk, StateT.run, ExceptT.run, StateT.bind,
    ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, Pure.pure, ExceptT.pure,
    StateT.pure, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw]
  have hv : ({ x.st with pqRatchetState := ([] : List (BitVec 8)) } :
      SessionState (List (BitVec 8))).version = x.st.version := rfl
  have hr : ({ x.st with pqRatchetState := ([] : List (BitVec 8)) } :
      SessionState (List (BitVec 8))).remoteIdentity = none := hrem
  rw [hsc]
  dsimp only [bind, StateT.bind, StateT.map, StateT.modifyGet, StateT.get, StateT.pure,
    Pure.pure, ExceptT.bindCont, default]
  rw [hv, ite_eq_right_iff.mpr (fun h => absurd h hver), hr, hsc]
  rfl

theorem otrFrom_model_ok (x : OtrFromGhost) {sc : SenderChain} {rem : IdentityKey}
    (hsc : x.st.senderChain = some sc) (hver : ¬ 256 ≤ x.st.version.toNat)
    (hrem : x.st.remoteIdentity = some rem) :
    x.model = (.ok ⟨sc.ratchetKey, sc.chainKey, x.st.previousCounter, x.st.pqRatchetState,
        BitVec.ofNat 8 x.st.version.toNat, x.st.localIdentity, rem⟩,
      { x.st with pqRatchetState := [] }) := by
  unfold OtrFromGhost.model OutgoingTripleRatchet.fromSessionState Mut.exec
    SessionState.takePqRatchetState
  dsimp only [bind, ExceptT.bind, ExceptT.mk, StateT.run, ExceptT.run, StateT.bind,
    ExceptT.bindCont, get, getThe, MonadStateOf.get, StateT.get, Pure.pure, ExceptT.pure,
    StateT.pure, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, Functor.map, StateT.map,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw]
  have hv : ({ x.st with pqRatchetState := ([] : List (BitVec 8)) } :
      SessionState (List (BitVec 8))).version = x.st.version := rfl
  have hr : ({ x.st with pqRatchetState := ([] : List (BitVec 8)) } :
      SessionState (List (BitVec 8))).remoteIdentity = some rem := hrem
  rw [hsc]
  dsimp only [bind, StateT.bind, StateT.map, StateT.modifyGet, StateT.get, StateT.pure,
    Pure.pure, ExceptT.bindCont, default]
  rw [hv, ite_eq_right_iff.mpr (fun h => absurd h hver), hr, hsc]
  rfl

theorem otrFrom_model_no_panic (x : OtrFromGhost) :
    x.model.1 ≠ .error .panic := by
  cases hsc : x.st.senderChain with
  | none => rw [otrFrom_model_none x hsc]; nofun
  | some sc =>
    by_cases hver : 256 ≤ x.st.version.toNat
    · rw [otrFrom_model_verTooLarge x hsc hver]; nofun
    · cases hrem : x.st.remoteIdentity with
      | none => rw [otrFrom_model_noRemote x hsc hver hrem]; nofun
      | some rem => rw [otrFrom_model_ok x hsc hver hrem]; nofun

/-! ## Packed word helpers (`pack8`, `pack16`, `pack32`, `pack64`) -/

def pack8 (bs : List (BitVec 8)) : BitVec 8 := packBV 8 bs
def pack16 (bs : List (BitVec 8)) : BitVec 16 := packBV 16 bs
def pack32 (bs : List (BitVec 8)) : BitVec 32 := packBV 32 bs

theorem pointsToBytes_1_eq_pointsTo8 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 1) :
    (a ↦ₛ bs) = (a ↦₈ pack8 bs) := by
  rcases bs with _ | ⟨b0, _ | _⟩ <;> try cases h
  simp only [pack8, packBV, List.foldr, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  congr 1; bv_kernel

theorem unpack16_pack16 (bs : List (BitVec 8)) (h : bs.length = 2) :
    unpack16 (pack16 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | _⟩⟩ <;> try cases h
  simp only [unpack16, pack16, packBV, List.foldr, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel⟩

theorem pointsToBytes_2_eq_pointsTo16 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 2) :
    (a ↦ₛ bs) = (a ↦₁₆ pack16 bs) := by
  rw [pointsTo16_eq_pointsToBytes, unpack16_pack16 bs h]

theorem unpack32_pack32 (bs : List (BitVec 8)) (h : bs.length = 4) :
    unpack32 (pack32 bs) = bs := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try cases h
  simp only [unpack32, pack32, packBV, List.foldr, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem pointsToBytes_4_eq_pointsTo32 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 4) :
    (a ↦ₛ bs) = (a ↦₃₂ pack32 bs) := by
  rw [pointsTo32_eq_pointsToBytes, unpack32_pack32 bs h]

theorem pointsToBytes_cut (a a' : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (hn : n ≤ bs.length) (ha' : a + BitVec.ofNat 64 n = a') :
    (a ↦ₛ bs) = (a ↦ₛ bs.take n) ∗ (a' ↦ₛ bs.drop n) := by
  subst ha'
  conv_lhs => rw [← List.take_append_drop n bs]
  rw [pointsToBytes_append, List.length_take_of_le hn]

/-! ## `errResultAt` and Branch 2/3 byte reassembly helpers -/

theorem otrResultAt_iss_intro (A : RustAlloc) (ret p len : BitVec 64) (pq : VecPin)
    (r : InvalidSessionReason) (hlen : len = BitVec.ofNat 64 (invalidSessionStructureStr r).length := by rfl_kernel) :
    (ret ↦₆₄ (bv% (2 ^ 64 - 1))) ∗ ((ret + 8#64) ↦₆₄ 9223372036854775828#64) ∗
      ((ret + 16#64) ↦₆₄ p) ∗ ((ret + 24#64) ↦₆₄ len) ∗
      (p ↦ᵣ invalidSessionStructureStr r) ∗ memRegion (ret + 32#64) 24 ∗ memRegion (ret + 56#64) 144 ⊢
    otrResultAt A ret pq (.error (.invalidSessionStructure r)) := by
  subst hlen
  unfold otrResultAt errResultAt speAt strRefAt
  have h16 : ret + 8#64 + 8#64 = ret + 16#64 := by bv_lin
  have h24 : ret + 16#64 + 8#64 = ret + 24#64 := by bv_lin
  have h32 : ret + 8#64 + 24#64 = ret + 32#64 := by bv_lin
  rw [h16, h24, h32]
  change (ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ speWord 20) ∗
      ((ret + 16#64) ↦₆₄ p) ∗ ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr r).length) ∗
      (p ↦ᵣ invalidSessionStructureStr r) ∗ memRegion (ret + 32#64) 24 ∗ memRegion (ret + 56#64) 144 ⊢ _
  have hgrp :
      (ret ↦₆₄ errTag) ∗ ((ret + 8#64) ↦₆₄ speWord 20) ∗
        ((ret + 16#64) ↦₆₄ p) ∗ ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr r).length) ∗
        (p ↦ᵣ invalidSessionStructureStr r) ∗ memRegion (ret + 32#64) 24 ∗ memRegion (ret + 56#64) 144 =
      (ret ↦₆₄ errTag) ∗ (((ret + 8#64) ↦₆₄ speWord 20) ∗
        (((ret + 16#64) ↦₆₄ p) ∗ ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr r).length) ∗
         (p ↦ᵣ invalidSessionStructureStr r)) ∗ memRegion (ret + 32#64) 24) ∗ memRegion (ret + 56#64) 144 := by
    simp only [sepConj_assoc]
  rw [hgrp]
  exact sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      (Entails.sepExists_intro p (P := fun q =>
        ((ret + 16#64) ↦₆₄ q) ∗ ((ret + 24#64) ↦₆₄ BitVec.ofNat 64 (invalidSessionStructureStr r).length) ∗
          (q ↦ᵣ invalidSessionStructureStr r))))))

/-- Branch 2 (`versionTooLarge`): `1 + 4 + 2 + 1` byte stores at `a` reassemble `a ↦₆₄ p`. -/
theorem pointsTo64_of_1_4_2_1 (a p : BitVec 64) :
    ((a ↦₈ ((p.setWidth 32).zeroExtend 64).setWidth 8) ∗
     ((a + 1#64) ↦₃₂ (((p >>> 8).setWidth 32).zeroExtend 64).setWidth 32) ∗
     ((a + 5#64) ↦₁₆ (((p >>> 40).setWidth 32).zeroExtend 64).setWidth 16) ∗
     ((a + 7#64) ↦₈ (((p >>> 56).setWidth 32).zeroExtend 64).setWidth 8)) =
    (a ↦₆₄ p) := by
  rw [pointsTo64_eq_pointsToBytes a p,
      pointsTo32_eq_pointsToBytes (a + 1#64),
      pointsTo16_eq_pointsToBytes (a + 5#64)]
  simp only [unpack64, unpack32, unpack16, pointsToBytes_cons, pointsToBytes_nil,
    sepConj_emp, sepConj_assoc]
  have h1 : a + 1#64 + 1#64 = a + 2#64 := by bv_lin
  have h2 : a + 2#64 + 1#64 = a + 3#64 := by bv_lin
  have h3 : a + 3#64 + 1#64 = a + 4#64 := by bv_lin
  have h4 : a + 4#64 + 1#64 = a + 5#64 := by bv_lin
  have h5 : a + 5#64 + 1#64 = a + 6#64 := by bv_lin
  have h6 : a + 6#64 + 1#64 = a + 7#64 := by bv_lin
  rw [h1, h2, h3, h4, h5, h6]
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  exact congrArg₂ sepConj (congrArg _ (by bv_kernel)) (congrArg _ (by bv_kernel))

/-- Branch 3 (`missingRemoteIdentity`): 22 bytes `(8 + 8 + 6)` at `a` decomposed as `4 + 2 + 8 + 8`. -/
def bs22 (w0 w1 : BitVec 64) (bs6 : List (BitVec 8)) : List (BitVec 8) :=
  unpack64 w0 ++ (unpack64 w1 ++ bs6)

theorem twentyTwoBytes_eq_4_2_8_8 (a w0 w1 : BitVec 64) (bs6 : List (BitVec 8))
    (h6 : bs6.length = 6) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦ₛ bs6)) =
      ((a ↦₃₂ pack32 ((bs22 w0 w1 bs6).take 4)) ∗
       ((a + 4#64) ↦₁₆ pack16 (((bs22 w0 w1 bs6).drop 4).take 2)) ∗
       ((a + 6#64) ↦₆₄ pack64 (((bs22 w0 w1 bs6).drop 6).take 8)) ∗
       ((a + 14#64) ↦₆₄ pack64 ((bs22 w0 w1 bs6).drop 14))) := by
  have hcomb : ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦ₛ bs6)) =
      (a ↦ₛ bs22 w0 w1 bs6) := by
    unfold bs22
    rw [pointsToBytes_append, pointsToBytes_append, unpack64_length, unpack64_length,
        ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
    have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_lin
    rw [ha16]
  rw [hcomb]
  have hlen : (bs22 w0 w1 bs6).length = 22 := by simp [bs22, h6]
  rw [pointsToBytes_cut a (a + 4#64) _ 4 (by omega) rfl,
      pointsToBytes_cut (a + 4#64) (a + 6#64) _ 2 (by simp [hlen]) (by bv_lin),
      pointsToBytes_cut (a + 6#64) (a + 14#64) _ 8 (by simp [hlen]) (by bv_lin)]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [pointsToBytes_4_eq_pointsTo32 a _ (by simp [hlen]),
      pointsToBytes_2_eq_pointsTo16 (a + 4#64) _ (by simp [hlen]),
      pointsToBytes_8_eq_pointsTo64 (a + 6#64) _ (by simp [hlen]),
      pointsToBytes_8_eq_pointsTo64 (a + 14#64) _ (by simp [hlen])]

/-! ## `SepWP.of_sepWP_inv` and 32-byte key partition lemmas -/

theorem frozenLoaded_setPC {img : Obj.Image} {s : State} (pc : BitVec 64)
    (h : img.FrozenLoaded s) : img.FrozenLoaded (s.setPC pc) :=
  (Obj.Image.frozenLoaded_iff (s := s.setPC pc)).2 ((Obj.Image.frozenLoaded_iff (s := s)).1 h)

/-- `remoteIk` 32-byte partition: `4 + 2 + 8 + 8 + 8 + 2` at `+0, +4, +6, +14, +22, +30`. -/
theorem bytes32_eq_4_2_8_8_8_2 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₃₂ pack32 (bs.take 4)) ∗
       ((a + 4#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
       ((a + 6#64) ↦₆₄ pack64 ((bs.drop 6).take 8)) ∗
       ((a + 14#64) ↦₆₄ pack64 ((bs.drop 14).take 8)) ∗
       ((a + 22#64) ↦₆₄ pack64 ((bs.drop 22).take 8)) ∗
       ((a + 30#64) ↦₁₆ pack16 (bs.drop 30))) := by
  rw [pointsToBytes_cut a (a + 4#64) _ 4 (by omega) rfl,
      pointsToBytes_cut (a + 4#64) (a + 6#64) _ 2 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 6#64) (a + 14#64) _ 8 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 14#64) (a + 22#64) _ 8 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 22#64) (a + 30#64) _ 8 (by simp [h]) (by bv_lin)]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [pointsToBytes_4_eq_pointsTo32 a _ (by simp [h]),
      pointsToBytes_2_eq_pointsTo16 (a + 4#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 6#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 14#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 22#64) _ (by simp [h]),
      pointsToBytes_2_eq_pointsTo16 (a + 30#64) _ (by simp [h])]

/-- `priv` 32-byte partition: `1 + 4 + 2 + 8 + 8 + 8 + 1` at `+0, +1, +5, +7, +15, +23, +31`. -/
theorem bytes32_eq_1_4_2_8_8_8_1 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₈ pack8 (bs.take 1)) ∗
       ((a + 1#64) ↦₃₂ pack32 ((bs.drop 1).take 4)) ∗
       ((a + 5#64) ↦₁₆ pack16 ((bs.drop 5).take 2)) ∗
       ((a + 7#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
       ((a + 15#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
       ((a + 23#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
       ((a + 31#64) ↦₈ pack8 (bs.drop 31))) := by
  rw [pointsToBytes_cut a (a + 1#64) _ 1 (by omega) rfl,
      pointsToBytes_cut (a + 1#64) (a + 5#64) _ 4 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 5#64) (a + 7#64) _ 2 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 7#64) (a + 15#64) _ 8 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 15#64) (a + 23#64) _ 8 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 23#64) (a + 31#64) _ 8 (by simp [h]) (by bv_lin)]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [pointsToBytes_1_eq_pointsTo8 a _ (by simp [h]),
      pointsToBytes_4_eq_pointsTo32 (a + 1#64) _ (by simp [h]),
      pointsToBytes_2_eq_pointsTo16 (a + 5#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 7#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 15#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 23#64) _ (by simp [h]),
      pointsToBytes_1_eq_pointsTo8 (a + 31#64) _ (by simp [h])]

/-- `srk`, `localIk`, `ck` 32-byte partition: `4 + 2 + 1 + 8 + 8 + 8 + 1` at `+0, +4, +6, +7, +15, +23, +31`. -/
theorem bytes32_eq_4_2_1_8_8_8_1 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₃₂ pack32 (bs.take 4)) ∗
       ((a + 4#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
       ((a + 6#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
       ((a + 7#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) ∗
       ((a + 15#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
       ((a + 23#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
       ((a + 31#64) ↦₈ pack8 (bs.drop 31))) := by
  rw [pointsToBytes_cut a (a + 4#64) _ 4 (by omega) rfl,
      pointsToBytes_cut (a + 4#64) (a + 6#64) _ 2 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 6#64) (a + 7#64) _ 1 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 7#64) (a + 15#64) _ 8 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 15#64) (a + 23#64) _ 8 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 23#64) (a + 31#64) _ 8 (by simp [h]) (by bv_lin)]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [pointsToBytes_4_eq_pointsTo32 a _ (by simp [h]),
      pointsToBytes_2_eq_pointsTo16 (a + 4#64) _ (by simp [h]),
      pointsToBytes_1_eq_pointsTo8 (a + 6#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 7#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 15#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 23#64) _ (by simp [h]),
      pointsToBytes_1_eq_pointsTo8 (a + 31#64) _ (by simp [h])]

/-- Switch 7 bytes `bs.take 7` from `4 + 2 + 1` to `1 + 2 + 4`. -/
theorem sevenBytes_4_2_1_eq_1_2_4 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((a ↦₃₂ pack32 (bs.take 4)) ∗
     ((a + 4#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
     ((a + 6#64) ↦₈ pack8 ((bs.drop 6).take 1))) =
    ((a ↦₈ pack8 (bs.take 1)) ∗
     ((a + 1#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
     ((a + 3#64) ↦₃₂ pack32 ((bs.drop 3).take 4))) := by
  have h7 : (bs.take 7).length = 7 := by simp [h]
  have lhs_eq :
      ((a ↦₃₂ pack32 (bs.take 4)) ∗
       ((a + 4#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
       ((a + 6#64) ↦₈ pack8 ((bs.drop 6).take 1))) = (a ↦ₛ bs.take 7) := by
    symm
    rw [pointsToBytes_cut a (a + 4#64) (bs.take 7) 4 (by omega) rfl,
        pointsToBytes_cut (a + 4#64) (a + 6#64) _ 2 (by simp [h7]) (by bv_lin)]
    simp only [List.take_take, List.drop_take, List.drop_drop, Nat.reduceAdd, Nat.reduceSub]
    rw [pointsToBytes_4_eq_pointsTo32 a _ (by simp [h]),
        pointsToBytes_2_eq_pointsTo16 (a + 4#64) _ (by simp [h]),
        pointsToBytes_1_eq_pointsTo8 (a + 6#64) _ (by simp [h])]
    rfl
  have rhs_eq :
      ((a ↦₈ pack8 (bs.take 1)) ∗
       ((a + 1#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
       ((a + 3#64) ↦₃₂ pack32 ((bs.drop 3).take 4))) = (a ↦ₛ bs.take 7) := by
    symm
    rw [pointsToBytes_cut a (a + 1#64) (bs.take 7) 1 (by omega) rfl,
        pointsToBytes_cut (a + 1#64) (a + 3#64) _ 2 (by simp [h7]) (by bv_lin)]
    simp only [List.take_take, List.drop_take, List.drop_drop, Nat.reduceAdd, Nat.reduceSub]
    rw [pointsToBytes_1_eq_pointsTo8 a _ (by simp [h]),
        pointsToBytes_2_eq_pointsTo16 (a + 1#64) _ (by simp [h]),
        pointsToBytes_4_eq_pointsTo32 (a + 3#64) _ (by simp [h])]
    rfl
  rw [lhs_eq, rhs_eq]

/-- Switch `1 + 2 + 4` (with `pack32 ((bs.drop 3).take 4)` at `+3`) into `4 + 2 + 1` ready for the store at `+0`. -/
theorem sevenBytes_after_store_at_3 (a : BitVec 64) (u0 : BitVec 8) (u12 : BitVec 16)
    (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((a ↦₈ u0) ∗ ((a + 1#64) ↦₁₆ u12) ∗ ((a + 3#64) ↦₃₂ pack32 ((bs.drop 3).take 4))) =
      ((a ↦₃₂ pack32 ([u0] ++ unpack16 u12 ++ (bs.drop 3).take 1)) ∗
       ((a + 4#64) ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
       ((a + 6#64) ↦₈ pack8 ((bs.drop 6).take 1))) := by
  let L := [u0] ++ (unpack16 u12 ++ (bs.drop 3).take 4)
  have hL : L.length = 7 := by simp [L, h]
  have lhs_eq :
      ((a ↦₈ u0) ∗ ((a + 1#64) ↦₁₆ u12) ∗ ((a + 3#64) ↦₃₂ pack32 ((bs.drop 3).take 4))) =
      (a ↦ₛ L) := by
    unfold L
    rw [pointsToBytes_append, pointsToBytes_append, List.length_singleton, unpack16_length,
        ← pointsTo16_eq_pointsToBytes, ← pointsToBytes_4_eq_pointsTo32 _ _ (by simp [h]),
        pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    have ha3 : a + 1#64 + 2#64 = a + 3#64 := by bv_lin
    rw [ha3]
  rw [lhs_eq]
  rw [pointsToBytes_cut a (a + 4#64) L 4 (by omega) rfl,
      pointsToBytes_cut (a + 4#64) (a + 6#64) _ 2 (by simp [hL]) (by bv_lin)]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [pointsToBytes_4_eq_pointsTo32 a _ (by simp [hL]),
      pointsToBytes_2_eq_pointsTo16 (a + 4#64) _ (by simp [hL]),
      pointsToBytes_1_eq_pointsTo8 (a + 6#64) _ (by simp [hL])]
  have h1 : L.take 4 = [u0] ++ unpack16 u12 ++ (bs.drop 3).take 1 := by
    simp only [L, unpack16, List.cons_append, List.nil_append, List.take_succ_cons,
      List.take_take]
    rfl
  have h2 : (L.drop 4).take 2 = (bs.drop 4).take 2 := by
    simp only [L, unpack16, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_take, List.drop_drop, List.take_take, Nat.reduceAdd, Nat.reduceSub]
    rfl
  have h3 : L.drop 6 = (bs.drop 6).take 1 := by
    simp only [L, unpack16, List.cons_append, List.nil_append, List.drop_succ_cons,
      List.drop_take, List.drop_drop, Nat.reduceAdd, Nat.reduceSub]
  rw [h1, h2, h3]

/-- Split `8B` at `a + 7` into `1 + 1 + 4 + 2` at `a + 7, a + 8, a + 9, a + 13` (`localIk` read). -/
theorem eightBytes_at_7_eq_1_1_4_2 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((a + 7#64) ↦₆₄ pack64 ((bs.drop 7).take 8)) =
      (((a + 7#64) ↦₈ pack8 ((bs.drop 7).take 1)) ∗
       ((a + 8#64) ↦₈ pack8 ((bs.drop 8).take 1)) ∗
       ((a + 9#64) ↦₃₂ pack32 ((bs.drop 9).take 4)) ∗
       ((a + 13#64) ↦₁₆ pack16 ((bs.drop 13).take 2))) := by
  have h8 : ((bs.drop 7).take 8).length = 8 := by simp [h]
  rw [← pointsToBytes_8_eq_pointsTo64 (a + 7#64) _ h8]
  rw [pointsToBytes_cut (a + 7#64) (a + 8#64) _ 1 (by omega) (by bv_lin),
      pointsToBytes_cut (a + 8#64) (a + 9#64) _ 1 (by simp [h8]) (by bv_lin),
      pointsToBytes_cut (a + 9#64) (a + 13#64) _ 4 (by simp [h8]) (by bv_lin)]
  simp only [List.take_take, List.drop_take, List.drop_drop, Nat.reduceAdd, Nat.reduceSub]
  rw [pointsToBytes_1_eq_pointsTo8 (a + 7#64) _ (by simp [h]),
      pointsToBytes_1_eq_pointsTo8 (a + 8#64) _ (by simp [h]),
      pointsToBytes_4_eq_pointsTo32 (a + 9#64) _ (by simp [h]),
      pointsToBytes_2_eq_pointsTo16 (a + 13#64) _ (by simp [h])]
  rfl

/-- `ck` 11-byte stack buffer: `2 + 1 + 8` at `a, a + 2, a + 3` equals `8 + 2 + 1` at `a, a + 8, a + 10`. -/
theorem elevenBytes_2_1_8_eq_8_2_1 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((a ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
     ((a + 2#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
     ((a + 3#64) ↦₆₄ pack64 ((bs.drop 7).take 8))) =
    ((a ↦₆₄ pack64 ((bs.drop 4).take 8)) ∗
     ((a + 8#64) ↦₁₆ pack16 ((bs.drop 12).take 2)) ∗
     ((a + 10#64) ↦₈ pack8 ((bs.drop 14).take 1))) := by
  have h11 : ((bs.drop 4).take 11).length = 11 := by simp [h]
  have lhs_eq :
      ((a ↦₁₆ pack16 ((bs.drop 4).take 2)) ∗
       ((a + 2#64) ↦₈ pack8 ((bs.drop 6).take 1)) ∗
       ((a + 3#64) ↦₆₄ pack64 ((bs.drop 7).take 8))) = (a ↦ₛ (bs.drop 4).take 11) := by
    symm
    rw [pointsToBytes_cut a (a + 2#64) ((bs.drop 4).take 11) 2 (by omega) rfl,
        pointsToBytes_cut (a + 2#64) (a + 3#64) _ 1 (by simp [h11]) (by bv_lin)]
    simp only [List.take_take, List.drop_take, List.drop_drop, Nat.reduceAdd, Nat.reduceSub]
    rw [pointsToBytes_2_eq_pointsTo16 a _ (by simp [h]),
        pointsToBytes_1_eq_pointsTo8 (a + 2#64) _ (by simp [h]),
        pointsToBytes_8_eq_pointsTo64 (a + 3#64) _ (by simp [h])]
    rfl
  have rhs_eq :
      ((a ↦₆₄ pack64 ((bs.drop 4).take 8)) ∗
       ((a + 8#64) ↦₁₆ pack16 ((bs.drop 12).take 2)) ∗
       ((a + 10#64) ↦₈ pack8 ((bs.drop 14).take 1))) = (a ↦ₛ (bs.drop 4).take 11) := by
    symm
    rw [pointsToBytes_cut a (a + 8#64) ((bs.drop 4).take 11) 8 (by omega) rfl,
        pointsToBytes_cut (a + 8#64) (a + 10#64) _ 2 (by simp [h11]) (by bv_lin)]
    simp only [List.take_take, List.drop_take, List.drop_drop, Nat.reduceAdd, Nat.reduceSub]
    rw [pointsToBytes_8_eq_pointsTo64 a _ (by simp [h]),
        pointsToBytes_2_eq_pointsTo16 (a + 8#64) _ (by simp [h]),
        pointsToBytes_1_eq_pointsTo8 (a + 10#64) _ (by simp [h])]
    rfl
  rw [lhs_eq, rhs_eq]

/-- `ck` 8-byte write at `+15`: `4 + 1 + 2 + 1` byte stores at `a` reassemble `a ↦₆₄ w`. -/
theorem pointsTo64_of_4_1_2_1 (a w : BitVec 64) :
    ((a ↦₃₂ ((w.setWidth 32).zeroExtend 64).setWidth 32) ∗
     ((a + 4#64) ↦₈ (((w >>> 32).setWidth 32).zeroExtend 64).setWidth 8) ∗
     ((a + 5#64) ↦₁₆ (((w >>> 40).setWidth 32).zeroExtend 64).setWidth 16) ∗
     ((a + 7#64) ↦₈ (((w >>> 56).setWidth 32).zeroExtend 64).setWidth 8)) =
    (a ↦₆₄ w) := by
  rw [pointsTo64_eq_pointsToBytes a w,
      pointsTo32_eq_pointsToBytes a,
      pointsTo16_eq_pointsToBytes (a + 5#64)]
  simp only [unpack64, unpack32, unpack16, pointsToBytes_cons, pointsToBytes_nil,
    sepConj_emp, sepConj_assoc]
  have h1 : a + 1#64 + 1#64 = a + 2#64 := by bv_lin
  have h2 : a + 2#64 + 1#64 = a + 3#64 := by bv_lin
  have h3 : a + 3#64 + 1#64 = a + 4#64 := by bv_lin
  have h4 : a + 4#64 + 1#64 = a + 5#64 := by bv_lin
  have h5 : a + 5#64 + 1#64 = a + 6#64 := by bv_lin
  have h6 : a + 6#64 + 1#64 = a + 7#64 := by bv_lin
  rw [h1, h2, h3, h4, h5, h6]
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  exact congrArg₂ sepConj (congrArg _ (by bv_kernel)) (congrArg _ (by bv_kernel))

/-- `ck` 32-byte write partition: `4 + 8 + 2 + 1 + 8 + 8 + 1` at `+0, +4, +12, +14, +15, +23, +31`. -/
theorem bytes32_eq_4_8_2_1_8_8_1 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₃₂ pack32 (bs.take 4)) ∗
       ((a + 4#64) ↦₆₄ pack64 ((bs.drop 4).take 8)) ∗
       ((a + 12#64) ↦₁₆ pack16 ((bs.drop 12).take 2)) ∗
       ((a + 14#64) ↦₈ pack8 ((bs.drop 14).take 1)) ∗
       ((a + 15#64) ↦₆₄ pack64 ((bs.drop 15).take 8)) ∗
       ((a + 23#64) ↦₆₄ pack64 ((bs.drop 23).take 8)) ∗
       ((a + 31#64) ↦₈ pack8 (bs.drop 31))) := by
  rw [pointsToBytes_cut a (a + 4#64) _ 4 (by omega) rfl,
      pointsToBytes_cut (a + 4#64) (a + 12#64) _ 8 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 12#64) (a + 14#64) _ 2 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 14#64) (a + 15#64) _ 1 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 15#64) (a + 23#64) _ 8 (by simp [h]) (by bv_lin),
      pointsToBytes_cut (a + 23#64) (a + 31#64) _ 8 (by simp [h]) (by bv_lin)]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [pointsToBytes_4_eq_pointsTo32 a _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 4#64) _ (by simp [h]),
      pointsToBytes_2_eq_pointsTo16 (a + 12#64) _ (by simp [h]),
      pointsToBytes_1_eq_pointsTo8 (a + 14#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 15#64) _ (by simp [h]),
      pointsToBytes_8_eq_pointsTo64 (a + 23#64) _ (by simp [h]),
      pointsToBytes_1_eq_pointsTo8 (a + 31#64) _ (by simp [h])]

theorem pack64_shift40_setWidth16 (bs : List (BitVec 8)) (h : bs.length = 32) :
    (((pack64 ((bs.drop 7).take 8) >>> 40).setWidth 32).zeroExtend 64).setWidth 16 =
      pack16 ((bs.drop 12).take 2) := by
  have h8 : ((bs.drop 7).take 8).length = 8 := by simp [h]
  have hd5 : ((bs.drop 12).take 2) = (((bs.drop 7).take 8).drop 5).take 2 := by
    simp only [List.drop_take, List.drop_drop, List.take_take, Nat.reduceAdd, Nat.reduceSub]
    rfl
  rw [hd5]
  generalize (bs.drop 7).take 8 = l at h8 ⊢
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases h8
  simp only [pack64, pack16, packBV, List.drop, List.take, List.foldr]
  bv_kernel

theorem pack64_shift56_setWidth8 (bs : List (BitVec 8)) (h : bs.length = 32) :
    (((pack64 ((bs.drop 7).take 8) >>> 56).setWidth 32).zeroExtend 64).setWidth 8 =
      pack8 ((bs.drop 14).take 1) := by
  have h8 : ((bs.drop 7).take 8).length = 8 := by simp [h]
  have hd7 : ((bs.drop 14).take 1) = (((bs.drop 7).take 8).drop 7).take 1 := by
    simp only [List.drop_take, List.drop_drop, List.take_take, Nat.reduceAdd, Nat.reduceSub]
    rfl
  rw [hd7]
  generalize (bs.drop 7).take 8 = l at h8 ⊢
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases h8
  simp only [pack64, pack8, packBV, List.drop, List.take, List.foldr]
  bv_kernel

/-- Switch `4 + 2 + 1` (with `pack32 (bs.take 4)` at `+0`) into `1 + 2 + 4` ready for the store at `+3`. -/
theorem sevenBytes_after_store_at_0 (a : BitVec 64) (u4 : BitVec 16) (u6 : BitVec 8)
    (bs : List (BitVec 8)) (h : bs.length = 32) :
    ((a ↦₃₂ pack32 (bs.take 4)) ∗ ((a + 4#64) ↦₁₆ u4) ∗ ((a + 6#64) ↦₈ u6)) =
      ((a ↦₈ pack8 (bs.take 1)) ∗
       ((a + 1#64) ↦₁₆ pack16 ((bs.drop 1).take 2)) ∗
       ((a + 3#64) ↦₃₂ pack32 ((bs.drop 3).take 1 ++ unpack16 u4 ++ [u6]))) := by
  let L := bs.take 4 ++ (unpack16 u4 ++ [u6])
  have hL : L.length = 7 := by simp [L, h]
  have lhs_eq :
      ((a ↦₃₂ pack32 (bs.take 4)) ∗ ((a + 4#64) ↦₁₆ u4) ∗ ((a + 6#64) ↦₈ u6)) =
      (a ↦ₛ L) := by
    unfold L
    have ht4 : (bs.take 4).length = 4 := by simp [h]
    rw [pointsToBytes_append, pointsToBytes_append, ht4, unpack16_length,
        ← pointsToBytes_4_eq_pointsTo32 _ _ ht4, ← pointsTo16_eq_pointsToBytes,
        pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    have ha6 : a + 4#64 + 2#64 = a + 6#64 := by bv_lin
    rw [ha6]
  rw [lhs_eq]
  rw [pointsToBytes_cut a (a + 1#64) L 1 (by omega) rfl,
      pointsToBytes_cut (a + 1#64) (a + 3#64) _ 2 (by simp [hL]) (by bv_lin)]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [pointsToBytes_1_eq_pointsTo8 a _ (by simp [hL]),
      pointsToBytes_2_eq_pointsTo16 (a + 1#64) _ (by simp [hL]),
      pointsToBytes_4_eq_pointsTo32 (a + 3#64) _ (by simp [hL])]
  unfold L
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, bs'⟩⟩⟩⟩ <;> try cases h
  rfl

theorem pointsTo32_pair_eq_pointsTo64 (a : BitVec 64) (v0 v1 : BitVec 32) :
    ((a ↦₃₂ v0) ∗ ((a + 4#64) ↦₃₂ v1)) =
      (a ↦₆₄ (v0.zeroExtend 64 ||| (v1.zeroExtend 64 <<< 32))) := by
  rw [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes a,
      pointsTo32_eq_pointsToBytes (a + 4#64)]
  simp only [unpack64, unpack32, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, sepConj_assoc]
  have h1 : a + 1#64 + 1#64 = a + 2#64 := by bv_lin
  have h2 : a + 2#64 + 1#64 = a + 3#64 := by bv_lin
  have h25 : a + 3#64 + 1#64 = a + 4#64 := by bv_lin
  have h3 : a + 4#64 + 1#64 = a + 5#64 := by bv_lin
  have h4 : a + 5#64 + 1#64 = a + 6#64 := by bv_lin
  have h5 : a + 6#64 + 1#64 = a + 7#64 := by bv_lin
  rw [h1, h2, h25, h3, h4, h5]
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  refine congrArg₂ sepConj (congrArg _ (by bv_kernel)) ?_
  exact congrArg₂ sepConj (congrArg _ (by bv_kernel)) (congrArg _ (by bv_kernel))

theorem pointsTo8_pair_eq_pointsTo16 (a : BitVec 64) (b0 b1 : BitVec 8) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1)) =
      (a ↦₁₆ (b0.zeroExtend 16 ||| (b1.zeroExtend 16 <<< 8))) := by
  rw [pointsTo16_eq_pointsToBytes]
  simp only [unpack16, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  exact congrArg₂ sepConj (congrArg _ (by bv_kernel)) (congrArg _ (by bv_kernel))

theorem localIk_bytes0_7_low32 (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8) :
    ((((v0.zeroExtend 64 |||
        ((((v4.zeroExtend 32 ||| ((v6.zeroExtend 32) <<< 16)).zeroExtend 64)) <<< 32)).setWidth 32).zeroExtend 64).setWidth 32) = v0 := by
  bv_kernel

theorem localIk_bytes0_7_mid16 (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8) :
    (((((v0.zeroExtend 64 |||
        ((((v4.zeroExtend 32 ||| ((v6.zeroExtend 32) <<< 16)).zeroExtend 64)) <<< 32)) >>> 32).setWidth 32).zeroExtend 64).setWidth 16) = v4 := by
  bv_kernel

theorem localIk_bytes0_7_hi8 (v0 : BitVec 32) (v4 : BitVec 16) (v6 : BitVec 8) :
    (((((v0.zeroExtend 64 |||
        ((((v4.zeroExtend 32 ||| ((v6.zeroExtend 32) <<< 16)).zeroExtend 64)) <<< 32)) >>> 48).setWidth 32).zeroExtend 64).setWidth 8) = v6 := by
  bv_kernel

theorem localIk_bytes7_15_reassemble (bs : List (BitVec 8)) (h : bs.length = 32) :
    (((pack8 ((bs.drop 7).take 1)).zeroExtend 64 |||
      (((pack8 ((bs.drop 8).take 1)).zeroExtend 64) <<< 8)) |||
     ((((pack32 ((bs.drop 9).take 4)).zeroExtend 64) <<< 16) |||
      (((pack16 ((bs.drop 13).take 2)).zeroExtend 64) <<< 48))) =
    pack64 ((bs.drop 7).take 8) := by
  have h8 : ((bs.drop 7).take 8).length = 8 := by simp [h]
  have hd0 : ((bs.drop 7).take 1) = ((bs.drop 7).take 8).take 1 := by simp [List.take_take]
  have hd1 : ((bs.drop 8).take 1) = (((bs.drop 7).take 8).drop 1).take 1 := by
    simp only [List.drop_take, List.drop_drop, List.take_take, Nat.reduceAdd, Nat.reduceSub]; rfl
  have hd2 : ((bs.drop 9).take 4) = (((bs.drop 7).take 8).drop 2).take 4 := by
    simp only [List.drop_take, List.drop_drop, List.take_take, Nat.reduceAdd, Nat.reduceSub]; rfl
  have hd6 : ((bs.drop 13).take 2) = (((bs.drop 7).take 8).drop 6).take 2 := by
    simp only [List.drop_take, List.drop_drop, List.take_take, Nat.reduceAdd, Nat.reduceSub]; rfl
  rw [hd0, hd1, hd2, hd6]
  generalize (bs.drop 7).take 8 = l at h8 ⊢
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try cases h8
  dsimp only [List.drop, List.take]
  have h8 (x : BitVec 8) : pack8 [x] = x := by
    dsimp [pack8, packBV]; bv_kernel
  have h45 : (((0 : BitVec 32) <<< 8 ||| b5.zeroExtend 32) <<< 8 ||| b4.zeroExtend 32) =
      (pack16 [b4, b5]).zeroExtend 32 := by
    dsimp [pack16, packBV]; bv_kernel
  have h23 (v : BitVec 16) :
      ((((v.zeroExtend 32 <<< 8 ||| b3.zeroExtend 32) <<< 8) ||| b2.zeroExtend 32).zeroExtend 64) =
        ((v.zeroExtend 64 <<< 8 ||| b3.zeroExtend 64) <<< 8) ||| b2.zeroExtend 64 := by
    bv_kernel
  have h67 : (pack16 [b6, b7]).zeroExtend 64 =
      (((0 : BitVec 64) <<< 8 ||| b7.zeroExtend 64) <<< 8) ||| b6.zeroExtend 64 := by
    dsimp [pack16, packBV]; bv_kernel
  have h47 (hi : BitVec 64) (x y : BitVec 8) :
      (hi <<< 16) ||| (pack16 [x, y]).zeroExtend 64 =
        ((hi <<< 8 ||| y.zeroExtend 64) <<< 8) ||| x.zeroExtend 64 := by
    have hp : (pack16 [x, y]).zeroExtend 64 = (y.zeroExtend 64 <<< 8) ||| x.zeroExtend 64 := by
      dsimp [pack16, packBV]; bv_kernel
    rw [hp, ← BitVec.or_assoc]
    bv_kernel
  have hw16 (w32 : BitVec 32) (acc : BitVec 16) :
      (w32.zeroExtend 64 <<< 16) ||| (acc.zeroExtend 64 <<< 48) =
        ((acc.zeroExtend 64 <<< 32) ||| w32.zeroExtend 64) <<< 16 := by
    bv_kernel
  have h16_shift (a b : BitVec 16) :
      (a.zeroExtend 64 <<< 32) ||| (b.zeroExtend 64 <<< 16) =
        ((a.zeroExtend 64 <<< 16) ||| b.zeroExtend 64) <<< 16 := by
    bv_kernel
  have hb1 (hi : BitVec 64) :
      (b1.zeroExtend 64 <<< 8) ||| (hi <<< 16) =
        (hi <<< 8 ||| b1.zeroExtend 64) <<< 8 := by
    bv_kernel
  rw [h8 b0, h8 b1, hw16 (pack32 [b2, b3, b4, b5]) (pack16 [b6, b7])]
  dsimp only [pack32, packBV, List.foldr]
  rw [h45, h23 (pack16 [b4, b5]), ← h47 (BitVec.zeroExtend 64 (pack16 [b4, b5])) b2 b3,
      ← BitVec.or_assoc ((pack16 [b6, b7]).zeroExtend 64 <<< 32),
      h16_shift (pack16 [b6, b7]) (pack16 [b4, b5]),
      h47 _ b2 b3, h47 _ b4 b5, h67,
      BitVec.or_assoc (b0.zeroExtend 64), hb1, BitVec.or_comm (b0.zeroExtend 64)]
  rfl

theorem shift40_shift16_eq_shift56 (w : BitVec 64) :
    (((((w >>> 40).setWidth 32) >>> 16).zeroExtend 64).setWidth 8) =
      ((((w >>> 56).setWidth 32).zeroExtend 64).setWidth 8) := by
  bv_kernel

attribute [local arm64_norm]
  localIk_bytes0_7_low32 localIk_bytes0_7_mid16 localIk_bytes0_7_hi8
  shift40_shift16_eq_shift56


namespace FromSessionStateFacts

theorem vec32_pack8_take1_eq_get0 (v : List.Vector (BitVec 8) 32) :
    pack8 (v.toList.take 1) = v.get 0 := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨x0, l'⟩
  · cases hl
  · change pack8 [x0] = x0
    dsimp [pack8, packBV, List.foldr]
    bv_kernel

theorem vec32_pack8_drop31_eq_get31 (v : List.Vector (BitVec 8) 32) :
    pack8 (v.toList.drop 31) = v.get 31 := by
  have hd : v.toList.drop 31 = [v.toList[31]'(by simp)] := by
    rw [List.drop_eq_getElem_cons (by simp), List.drop_eq_nil_of_le (by simp)]
  have hget : v.get 31 = v.toList[31]'(by simp) := rfl
  rw [hd, hget]
  dsimp [pack8, packBV, List.foldr]
  bv_kernel

end FromSessionStateFacts

theorem clampScalar_byte0 {v : List.Vector (BitVec 8) 32} (hcl : Ratchet.clampScalar v = v) :
    ((((pack8 (v.toList.take 1)).zeroExtend 32 &&& 0xfffffff8#32).zeroExtend 64).setWidth 8) =
      pack8 (v.toList.take 1) := by
  have h0 : (Ratchet.clampScalar v).get 0 = v.get 0 := congrArg (fun u => u.get 0) hcl
  have hne : (0 : Fin 32) ≠ 31 := by decide
  simp only [Ratchet.clampScalar, List.Vector.get_set_of_ne hne.symm, List.Vector.get_set_same] at h0
  rw [FromSessionStateFacts.vec32_pack8_take1_eq_get0 v]
  revert h0; bv_kernel

theorem clampScalar_byte31 {v : List.Vector (BitVec 8) 32} (hcl : Ratchet.clampScalar v = v) :
    ((BitVec.ofNat 32 64 &&& 4294967232#32 |||
      ((pack8 (v.toList.drop 31)).zeroExtend 32 &&& 63#32)).zeroExtend 64).setWidth 8 =
      pack8 (v.toList.drop 31) := by
  have h31 : (Ratchet.clampScalar v).get 31 = v.get 31 := congrArg (fun u => u.get 31) hcl
  simp only [Ratchet.clampScalar, List.Vector.get_set_same] at h31
  rw [FromSessionStateFacts.vec32_pack8_drop31_eq_get31 v]
  revert h31; bv_kernel

/-! ## Stack and `sessionStateAt` decomposition for `OTR::from_session_state` -/

theorem stackAt_prologue (sp : BitVec 64) :
    stackAt sp smallRootStack =
      stackAt (sp - 384#64) 65152 ∗
      memRegion (sp - 384#64) 288 ∗
      (∃∗ r0 : BitVec 64, (sp - 96#64) ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (sp - 88#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (sp - 80#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (sp - 72#64) ↦₆₄ r3) ∗
      (∃∗ r4 : BitVec 64, (sp - 64#64) ↦₆₄ r4) ∗
      (∃∗ r5 : BitVec 64, (sp - 56#64) ↦₆₄ r5) ∗
      (∃∗ r6 : BitVec 64, (sp - 48#64) ↦₆₄ r6) ∗
      (∃∗ r7 : BitVec 64, (sp - 40#64) ↦₆₄ r7) ∗
      (∃∗ r8 : BitVec 64, (sp - 32#64) ↦₆₄ r8) ∗
      (∃∗ r9 : BitVec 64, (sp - 24#64) ↦₆₄ r9) ∗
      (∃∗ r10 : BitVec 64, (sp - 16#64) ↦₆₄ r10) ∗
      (∃∗ r11 : BitVec 64, (sp - 8#64) ↦₆₄ r11) := by
  show memRegion (sp - BitVec.ofNat 64 65536) 65536 = _
  rw [mr_cut' sp 65536 384 65152 384 65536 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 384 96 288 96 384 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 96 88 8 88 96 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 88 80 8 80 88 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 80 72 8 72 80 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 72 64 8 64 72 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 64 56 8 56 64 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 56 48 8 48 56 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 48 40 8 40 48 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 40 32 8 32 40 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 32 24 8 24 32 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 24 16 8 16 24 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 16 8 8 8 16 rfl rfl (by decide) (by decide) (by decide)]
  have hstk : memRegion (sp - BitVec.ofNat 64 65536) 65152 = stackAt (sp - 384#64) 65152 := by
    simp only [stackAt]; congr 1; bv_lin
  rw [hstk]
  simp only [memRegion_eight]

theorem stackAt_prologue_fold (sp r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : BitVec 64) :
    stackAt (sp - 384#64) 65152 ∗
      memRegion (sp - 384#64) 288 ∗
      ((sp - 96#64) ↦₆₄ r0) ∗ ((sp - 88#64) ↦₆₄ r1) ∗
      ((sp - 80#64) ↦₆₄ r2) ∗ ((sp - 72#64) ↦₆₄ r3) ∗
      ((sp - 64#64) ↦₆₄ r4) ∗ ((sp - 56#64) ↦₆₄ r5) ∗
      ((sp - 48#64) ↦₆₄ r6) ∗ ((sp - 40#64) ↦₆₄ r7) ∗
      ((sp - 32#64) ↦₆₄ r8) ∗ ((sp - 24#64) ↦₆₄ r9) ∗
      ((sp - 16#64) ↦₆₄ r10) ∗ ((sp - 8#64) ↦₆₄ r11) ⊢
    stackAt sp smallRootStack := by
  rw [stackAt_prologue sp]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (Entails.sepExists_intro r0) (sepConj_mono (Entails.sepExists_intro r1) ?_)
  refine sepConj_mono (Entails.sepExists_intro r2) (sepConj_mono (Entails.sepExists_intro r3) ?_)
  refine sepConj_mono (Entails.sepExists_intro r4) (sepConj_mono (Entails.sepExists_intro r5) ?_)
  refine sepConj_mono (Entails.sepExists_intro r6) (sepConj_mono (Entails.sepExists_intro r7) ?_)
  refine sepConj_mono (Entails.sepExists_intro r8) (sepConj_mono (Entails.sepExists_intro r9) ?_)
  exact sepConj_mono (Entails.sepExists_intro r10) (Entails.sepExists_intro r11)

theorem stackAt_dealloc (sp : BitVec 64) :
    stackAt (sp - 384#64) 65152 =
      stackAt (sp - 4480#64) 61056 ∗ stackAt (sp - 384#64) allocHookStack := by
  change memRegion (sp - 384#64 - 65152#64) (61056 + 4096) =
    memRegion (sp - 4480#64 - 61056#64) 61056 ∗ memRegion (sp - 384#64 - 4096#64) 4096
  rw [memRegion_split (sp - 384#64 - 65152#64) 61056 4096 (by decide)]
  have h1 : sp - 384#64 - 65152#64 = sp - 4480#64 - 61056#64 := by bv_lin
  have h2 : sp - 4480#64 - 61056#64 + BitVec.ofNat 64 61056 = sp - 384#64 - 4096#64 := by bv_lin
  rw [h1, h2]

theorem stackAt_remoteIk (sp : BitVec 64) :
    stackAt (sp - 384#64) 65152 =
      stackAt (sp - 528#64) 65008 ∗ stackAt (sp - 384#64) remoteIdentityKeyStack := by
  change memRegion (sp - 384#64 - 65152#64) (65008 + 144) =
    memRegion (sp - 528#64 - 65008#64) 65008 ∗ memRegion (sp - 384#64 - 144#64) 144
  rw [memRegion_split (sp - 384#64 - 65152#64) 65008 144 (by decide)]
  have h1 : sp - 384#64 - 65152#64 = sp - 528#64 - 65008#64 := by bv_lin
  have h2 : sp - 528#64 - 65008#64 + BitVec.ofNat 64 65008 = sp - 384#64 - 144#64 := by bv_lin
  rw [h1, h2]

theorem stackAt_dropSpe (sp : BitVec 64) :
    stackAt (sp - 384#64) 65152 =
      stackAt (sp - 4512#64) 61024 ∗ stackAt (sp - 384#64) dropSpeStack := by
  change memRegion (sp - 384#64 - 65152#64) (61024 + 4128) =
    memRegion (sp - 4512#64 - 61024#64) 61024 ∗ memRegion (sp - 384#64 - 4128#64) 4128
  rw [memRegion_split (sp - 384#64 - 65152#64) 61024 4128 (by decide)]
  have h1 : sp - 384#64 - 65152#64 = sp - 4512#64 - 61024#64 := by bv_lin
  have h2 : sp - 4512#64 - 61024#64 + BitVec.ofNat 64 61024 = sp - 384#64 - 4128#64 := by bv_lin
  rw [h1, h2]

/-! ## Relocatable `[LibsignalPlacement]` `.rodata` and callee helpers -/

abbrev missingSenderChainSym : String :=
  "libsignal_protocol:.rodata..Lanon.4"

abbrev versionTooLargeSym : String :=
  "libsignal_protocol:.rodata..Lanon.238"

abbrev missingRemoteIdentitySym : String :=
  "libsignal_protocol:.rodata..Lanon.139"

theorem rodata_missingSenderChain_placed_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsρ missingSenderChainSym) ↦ᵣ invalidSessionStructureStr .missingSenderChain) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

theorem rodata_versionTooLarge_placed_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsρ versionTooLargeSym) ↦ᵣ invalidSessionStructureStr .versionTooLarge) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

theorem rodata_missingRemoteIdentity_placed_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsρ missingRemoteIdentitySym) ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗ P :=
  lsro_intro_chk hro (by rfl_kernel) hP

/-- Relocatable `pkTryFromPlacedSpec` specialized when `PublicKey.deserialize bs = .ok pk`. -/
def pkTryFromOkPlacedSpec [LibsignalPlacement] :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out ∧
      PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 40 ∗ (lsLogFilterAddr ↦₆₄ 0#64)
  post := fun (p, bs, pk, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion (out + 33#64) 7 ∗ (lsLogFilterAddr ↦₆₄ 0#64)

theorem pkTryFromOk_placed_ok_at [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : String → Option (State → State)} [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base 211) (withLsCodeLoaded lsmpl pkTryFromOkPlacedSpec) := by
  refine subroutine_ok_map (pk_try_from_placed_ok_at (prog := prog) hi hunmut) ?_
  rintro ⟨p, bs, pk, out⟩ R s0 hpre
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  simp only [pkTryFromOkPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl, ?_⟩
    simp only [pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  · simp only [pkTryFromPlacedSpec, pkTryFromSpec, lsLogOff, hdes,
      pkTryFromResultAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    simp only [pkTryFromOkPlacedSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact hpost

/-- Add `⌜LibsignalRoLoaded pl s0.mem⌝` to `spec`'s precondition. -/
abbrev withLsRoLoaded {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalRoLoaded pl s0.mem⌝ }

/-- Sequence two `SepWP` segments while threading both `LibsignalCodeLoaded pl ·.mem` and
    `LibsignalRoLoaded pl ·.mem` across the cut. -/
theorem sepWP_seq_lscl_ro {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem) (hro : LibsignalRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → LibsignalRoLoaded pl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen
    (Φ := fun m => LibsignalCodeLoaded pl m ∧ LibsignalRoLoaded pl m)
    (fun _ _ ⟨h1, h2⟩ hkf => ⟨h1.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen h2 hkf⟩)
    ⟨hcl, hro⟩
    (SepWP.mono h fun _ _ _ _ hnext ⟨h1, h2⟩ => hnext h1 h2)

/-- Transfer a cross-block `subroutine_ok` (whose spec takes `withLsRoLoaded`) from block `j` to
    block `i`'s program `callerProg` using `hcl` and `hro` at the call site. -/
theorem lscall_blk_ro [LibsignalPlacement] {α : Type} {callerProg calleeProg : Program}
    {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {spec : Spec α} {m : Memory}
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsRoLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl m) (hro : LibsignalRoLoaded lsmpl m)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base j) (withMemEq m spec) := by
  have h1 := ls_subroutine_ok_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain hcallee) hi hj hj_unmut
  exact subroutine_ok_mono h1
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hm ▸ hcl
      have hro0 : LibsignalRoLoaded lsmpl s0.mem := hm ▸ hro
      dsimp only [withLsCodeLoaded, withLsRoLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcl0, ?_⟩
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hro0, hpre⟩)
    (fun _ _ _ _ hq => hq)

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
