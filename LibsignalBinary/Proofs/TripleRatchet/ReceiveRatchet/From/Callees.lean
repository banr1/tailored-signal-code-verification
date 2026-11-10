/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.Apply
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import ProofLib.SepLogic.WPp

/-!
# Callee Lemmas and Byte-Packing Helpers for `TripleRatchet::from_session_state`

Callee and `.rodata` lemmas, byte-granular `SepLoad`/`SepStore` normalizers, and key-clamping /
layout helpers for `<TripleRatchet>::from_session_state` (`0x1c60c`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open ProofLib.ProgramReflection

/-! ## Drop-glue callee hypotheses for `TR::from_session_state` -/

/-- `SessionState::remote_identity_key` (`0x11b04`) meets `remoteIdentityKeySpec A img` on `tripleRatchetProgAtExt`. -/
def RemoteIdentityKeyOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr remoteIdentityKeyName)
    (remoteIdentityKeySpec A img)

/-- `SessionState::remote_identity_key` (`0x11b04`) meets `remoteIdentityKeySpec A img` on `tripleRatchetProgAt`. -/
def RemoteIdentityKeyOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  RemoteIdentityKeyOkExt img A (tripleRatchetExterns C ctl abs)

/-- `drop_glue<SignalProtocolError>` (`0x2374`) meets `(dropSpeSpec A).inImage img` on `tripleRatchetProgAtExt`. -/
def DropSpeOkExt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName) ((dropSpeSpec A).inImage img)

/-- `drop_glue<SignalProtocolError>` (`0x2374`) meets `(dropSpeSpec A).inImage img` on `tripleRatchetProgAt`. -/
def DropSpeOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  DropSpeOkExt img A (tripleRatchetExterns C ctl abs)

/-- `drop_glue<SignalProtocolError>` (`0x2374`) meets `(dropSpeSpecX A).inImage img` on `tripleRatchetProgAtExt`. -/
def DropSpeOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName) ((dropSpeSpecX A).inImage img)


namespace ReceiveRatchetFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

-- Instruction decode lemmas for `TR::from_session_state` (`0x1c60c`).
gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") → (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 180), (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 232) → (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 596),
    (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 624) → (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 868), (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 888) → (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 964), (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 1004) → (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 1296), (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 1420) → (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state" + 1508)]

namespace FromFetches

open Lean Meta Elab Tactic in
elab "tr_from_fetches_raw " b:term:max H:term:max hfn:term:max relStart:num count:num : tactic => do
  let r0 := relStart.getNat
  let n := count.getNat
  let fnOff := num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")
  let fetchEntry := mkIdent ``CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent ``CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [0:n] do
    let k := r0 + 4 * i
    let off := fnOff + k
    let hexStr := String.ofList (Nat.toDigits 16 off)
    let dec := mkIdent (Name.str `CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
      ("libsignalSessionBin_decode_0x" ++ hexStr))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| (
        have _h := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec)))
    else
      evalTactic (← `(tactic| (
        have _h := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec)))

end FromFetches

open Lean Meta Elab Tactic in
/-- Fetch `count` instructions of `TR::from_session_state` (`0x1c60c`) starting at relative
byte offset `relStart`, rewriting the entry address with `hentry`. -/
elab "tr_from_fetches " b:term:max H:term:max hfn:term:max hentry:term:max relStart:num count:num : tactic => do
  let r0 := relStart.getNat
  let n := count.getNat
  let fnOff := num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")
  let fetchEntry := mkIdent ``CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent ``CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [0:n] do
    let k := r0 + 4 * i
    let off := fnOff + k
    let hexStr := String.ofList (Nat.toDigits 16 off)
    let dec := mkIdent (Name.str `CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
      ("libsignalSessionBin_decode_0x" ++ hexStr))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic| (
        have h := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec
        rw [$hentry:term] at h)))
    else
      evalTactic (← `(tactic| (
        have h := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec
        rw [$hentry:term] at h)))

/-! ## Callee, hook, and `.rodata` lemmas -/

theorem deserialize_ok_at_from {b : BitVec 64}
    {ext : String → Option (State → State)}
    (h : DeserializeOkExt b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr trFromName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))
      (CryptoVerification.LibsignalSession.FindReceiverChainIndex.deserializeSpec b) := by
  have hk : libsignalSessionCode.fnOff trFromName + num% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") =
      libsignalSessionCode.fnOff deserializeName := by simp only [arm64_norm]
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr trFromName + bv% (ls_off% "<libsignal_core::curve::PublicKey>::deserialize" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") =
      (tripleRatchetProgAtExt b ext).fnAddr deserializeName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hk]
  rwa [haddr]

theorem remoteIdentityKey_ok_at_from {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : RemoteIdentityKeyOkExt img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr trFromName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")))
      (remoteIdentityKeySpec A img) := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff trFromName) + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff remoteIdentityKeyName) := by
    simp only [arm64_norm]
  have haddr : (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + bv% (2 ^ 64 + (ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr remoteIdentityKeyName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, hk]
  rwa [haddr]

theorem dropSpe_ok_at_from {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropSpeOkExt img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr trFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")))
      ((dropSpeSpec A).inImage img) := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff trFromName) + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff dropSpeName) := by
    simp only [arm64_norm]
  have haddr : (tripleRatchetProgAtExt img.base ext).fnAddr trFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropSpeName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, hk]
  rwa [haddr]

theorem dropVecChain_ok_at_from {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropVecChainOkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr trFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")))
      (dropVecChainSpec A) := by
  have hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff trFromName) + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      BitVec.ofNat 64 (libsignalSessionCode.fnOff dropVecChainName) := by
    simp only [arm64_norm]
  have haddr : (tripleRatchetProgAtExt b ext).fnAddr trFromName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<alloc::vec::Vec<libsignal_protocol::proto::storage::session_structure::Chain>>") - (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) =
      (tripleRatchetProgAtExt b ext).fnAddr dropVecChainName := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
    rw [BitVec.add_assoc, hk]
  rwa [haddr]

theorem dealloc_ok_at_from {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr trFromName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))
      (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext hA (name := trFromName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))

theorem fnAddr_adrp_40000 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((tripleRatchetProgAtExt b ext).fnAddr trFromName + 1048#64) &&& 0xfffffffffffff000#64) + bv% (page% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)) - page% (ls_off% "<libsignal_protocol::sealed_sender::SenderCertificate>::deserialize" + 3404)) =
      b + bv% (page% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) := by
  have hfn : libsignalSessionCode.fnOff trFromName = num% (ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") := by simp only [arm64_norm]
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn]
  bv_arith

theorem rodata_0x40ce0_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752)) - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 27 =
      invalidSessionStructureStr .missingRemoteIdentity := by
  rfl_kernel

theorem rodata_missingRemoteIdentity_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img) {m : Memory} {P : SepProp}
    (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) ↦ᵣ invalidSessionStructureStr .missingRemoteIdentity) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 748) (ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::from_session_state" + 752))) (secLen := 27) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x40ce0_eq] at h

theorem SepWP.call_dropSpe {prog : Program} {img : Obj.Image}
    {entry target_pc sp_val : BitVec 64} {A : RustAlloc}
    (hsub : subroutine_ok prog entry ((dropSpeSpec A).inImage img)) (x : DropSpeGhost)
    {s : State} {P F_frame : SepProp} {post : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hsp_eq : s.sp = sp_val) (hx0 : s.readReg64 .x0 = x.a)
    (hpre : P = (speAt A x.fnName x.a x.e ∗ A.pool ∗ stackAt sp_val dropSpeStack) ∗ F_frame)
    (hcont : ∀ sf, sf.pc = s.readReg64 .lr → sf.sp = s.sp → sf.status = .Running →
      sf.spAligned = true → CalleeSavedPreserved s sf → sf.trace = s.trace →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWP prog target_pc sf (memRegion x.a 48 ∗ A.pool ∗ stackAt sp_val dropSpeStack ∗ F_frame) post) :
    SepWP prog target_pc s P post := by
  apply SepWP.of_sepWP_inv (mid := s.readReg64 .lr) hfl hsym
  refine SepWP.call_subroutine_frame hsub (x := x) (F := F_frame) hpc hrun hsp rfl ?_ ?_ ?_ ?_ ?_
  · intro R hm
    rw [hpre, ← hsp_eq] at hm
    dsimp only [Spec.inImage, dropSpeSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfl, hsym⟩, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, by simpa only [sepConj_assoc] using hm⟩
  · intro R' sf _ hpan_mem
    unfold Spec.inImage dropSpeSpec at hpan_mem
    dsimp only at hpan_mem
    rw [satisfies_pure_sepConj] at hpan_mem
    exact hpan_mem.1
  · intro R' code sf _ hundef_mem
    unfold Spec.inImage dropSpeSpec at hundef_mem
    dsimp only at hundef_mem
    rw [satisfies_pure_sepConj] at hundef_mem
    exact hundef_mem.1
  · intro sm hpcm hrunm hspm hcsm
    dsimp only [Spec.inImage, dropSpeSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun htrm => ?_
    rw [hsp_eq]
    simp only [sepConj_assoc]
    apply SepWP.done hpcm hrunm
    intro hflm hsymm
    exact hcont sm hpcm hspm hrunm (by simpa [State.spAligned, hspm] using hsp) hcsm htrm hflm hsymm
  · intro R' sf _ hoom_mem
    unfold Spec.inImage dropSpeSpec at hoom_mem
    dsimp only at hoom_mem
    rw [satisfies_pure_sepConj] at hoom_mem
    exact hoom_mem.1.elim

def pkTryFromOkSpec (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (p, bs, pk, out, out33, out34) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out ∧
      PublicKey.deserialize bs = .ok pk ∧ out + 33#64 = out33 ∧ out + 34#64 = out34⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 33 ∗ memRegion out33 1 ∗ memRegion out34 14 ∗ logOff img
  post := fun (p, bs, pk, out, out33, out34) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion out33 1 ∗ memRegion out34 14 ∗ logOff img

theorem pkTryFrom_ok_at_from {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr trFromName + bv% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state"))
      (pkTryFromOkSpec img) := by
  have hk : libsignalSessionCode.fnOff trFromName + num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state") =
      libsignalSessionCode.fnOff pkTryFromName := by simp only [arm64_norm]
  refine subroutine_ok_map (pk_try_from_ok_at_ext img ext himg trFromName (num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from" - ls_off% "<libsignal_protocol::triple_ratchet::TripleRatchet>::from_session_state")) hk) ?_
  rintro ⟨p, bs, pk, out, out33, out34⟩ R s0 hpre
  simp only [pkTryFromOkSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes, hout33, hout34⟩, hmem⟩
  subst hout33 hout34
  refine ⟨(p, bs, out), memRegion (out + 40#64) 8 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8⟩, ?_⟩
    rw [ProofLib.memRegion_split' (b := out) (n := 33) (k := 7) (b' := out + 33#64)
          rfl (by bv_omega) (by decide)]
    rw [ProofLib.memRegion_split' (b := out + 33#64) (n := 1) (k := 6) (b' := out + 34#64)
          rfl (by bv_omega) (by decide)]
    rw [ProofLib.memRegion_split' (b := out + 34#64) (n := 6) (k := 8) (b' := out + 40#64)
          rfl (by bv_omega) (by decide)] at hmem
    convert hmem using 1; ac_rfl
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [pkTryFromOkSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [ProofLib.memRegion_split' (b := out + 34#64) (n := 6) (k := 8) (b' := out + 40#64)
          rfl (by bv_omega) (by decide)]
    rw [ProofLib.memRegion_split' (b := out + 33#64) (n := 1) (k := 6) (b' := out + 34#64)
          rfl (by bv_omega) (by decide)] at hpost
    convert hpost using 1; ac_rfl

theorem afterTrFrom_decRel (G : SessionGhost) :
    G.AfterTryDecrypt false G.afterTrFrom := by
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

/-! ## Byte-granular `SepLoad`/`SepStore` and byte-concatenation normalization -/

theorem pointsTo16_eq_bytes2 (a : BitVec 64) (b0 b1 : BitVec 8) :
    (a ↦₁₆ (b1 ++ b0)) = (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) := by
  rw [← pointsToBytes2_eq_pointsTo16, pointsToBytes_cons, pointsToBytes_cons,
    pointsToBytes_nil, sepConj_emp]

theorem pointsTo32_eq_bytes4 (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) := by
  rw [← pointsToBytes4_eq_pointsTo32, pointsToBytes_cons, pointsToBytes_cons,
    pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_arith
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_arith
  rw [h2, h3]

theorem pointsTo64_eq_bytes8 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (a ↦₆₄ (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
      ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) := by
  rw [← pointsToBytes8_eq_pointsTo64]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_arith
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_arith
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by bv_arith
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by bv_arith
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by bv_arith
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by bv_arith
  rw [h2, h3, h4, h5, h6, h7]

theorem SepLoad16.of_bytes2 {a a0 a1 : BitVec 64} {b0 b1 : BitVec 8}
    {P F : SepProp}
    (h : P = ((a0 ↦₈ b0) ∗ (a1 ↦₈ b1)) ∗ F)
    (ha0 : a0 = a) (ha1 : a1 = a + 1#64) :
    SepLoad16 a P (b1 ++ b0) := by
  subst ha0 ha1
  exact SepLoad16.of_eq (by rw [h, ← pointsTo16_eq_bytes2])

theorem SepStore16.of_bytes2 {a a0 a1 : BitVec 64} {b0 b1 b0' b1' : BitVec 8}
    {val : BitVec 16} {P P' F : SepProp}
    (h : P = ((a0 ↦₈ b0) ∗ (a1 ↦₈ b1)) ∗ F)
    (h' : P' = ((a0 ↦₈ b0') ∗ (a1 ↦₈ b1')) ∗ F)
    (ha0 : a0 = a) (ha1 : a1 = a + 1#64)
    (hb0 : val.extractLsb' 0 8 = b0') (hb1 : val.extractLsb' 8 8 = b1') :
    SepStore16 a val P P' := by
  subst ha0 ha1 hb0 hb1
  have hval : (val.extractLsb' 8 8 ++ val.extractLsb' 0 8) = val := by bv_kernel
  exact SepStore16.of_eq (by rw [h, ← pointsTo16_eq_bytes2])
    (by rw [h', ← pointsTo16_eq_bytes2, hval])

theorem SepLoad32.of_bytes4 {a a0 a1 a2 a3 : BitVec 64} {b0 b1 b2 b3 : BitVec 8}
    {P F : SepProp}
    (h : P = ((a0 ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₈ b3)) ∗ F)
    (ha0 : a0 = a) (ha1 : a1 = a + 1#64) (ha2 : a2 = a + 2#64) (ha3 : a3 = a + 3#64) :
    SepLoad32 a P (b3 ++ b2 ++ b1 ++ b0) := by
  subst ha0 ha1 ha2 ha3
  exact SepLoad32.of_eq (by rw [h, ← pointsTo32_eq_bytes4])

theorem SepStore32.of_bytes4 {a a0 a1 a2 a3 : BitVec 64}
    {b0 b1 b2 b3 b0' b1' b2' b3' : BitVec 8}
    {val : BitVec 32} {P P' F : SepProp}
    (h : P = ((a0 ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₈ b3)) ∗ F)
    (h' : P' = ((a0 ↦₈ b0') ∗ (a1 ↦₈ b1') ∗ (a2 ↦₈ b2') ∗ (a3 ↦₈ b3')) ∗ F)
    (ha0 : a0 = a) (ha1 : a1 = a + 1#64) (ha2 : a2 = a + 2#64) (ha3 : a3 = a + 3#64)
    (hb0 : val.extractLsb' 0 8 = b0') (hb1 : val.extractLsb' 8 8 = b1')
    (hb2 : val.extractLsb' 16 8 = b2') (hb3 : val.extractLsb' 24 8 = b3') :
    SepStore32 a val P P' := by
  subst ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  have hval : (val.extractLsb' 24 8 ++ val.extractLsb' 16 8 ++
      val.extractLsb' 8 8 ++ val.extractLsb' 0 8) = val := by bv_kernel
  exact SepStore32.of_eq (by rw [h, ← pointsTo32_eq_bytes4])
    (by rw [h', ← pointsTo32_eq_bytes4, hval])

theorem SepLoad64.of_bytes8 {a a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8} {P F : SepProp}
    (h : P = ((a0 ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₈ b3) ∗
      (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ (a7 ↦₈ b7)) ∗ F)
    (ha0 : a0 = a) (ha1 : a1 = a + 1#64) (ha2 : a2 = a + 2#64) (ha3 : a3 = a + 3#64)
    (ha4 : a4 = a + 4#64) (ha5 : a5 = a + 5#64) (ha6 : a6 = a + 6#64) (ha7 : a7 = a + 7#64) :
    SepLoad64 a P (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) := by
  subst ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7
  exact SepLoad64.of_eq (by rw [h, ← pointsTo64_eq_bytes8])

theorem SepStore64.of_bytes8 {a a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 64}
    {b0 b1 b2 b3 b4 b5 b6 b7 b0' b1' b2' b3' b4' b5' b6' b7' : BitVec 8}
    {val : BitVec 64} {P P' F : SepProp}
    (h : P = ((a0 ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₈ b3) ∗
      (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ (a7 ↦₈ b7)) ∗ F)
    (h' : P' = ((a0 ↦₈ b0') ∗ (a1 ↦₈ b1') ∗ (a2 ↦₈ b2') ∗ (a3 ↦₈ b3') ∗
      (a4 ↦₈ b4') ∗ (a5 ↦₈ b5') ∗ (a6 ↦₈ b6') ∗ (a7 ↦₈ b7')) ∗ F)
    (ha0 : a0 = a) (ha1 : a1 = a + 1#64) (ha2 : a2 = a + 2#64) (ha3 : a3 = a + 3#64)
    (ha4 : a4 = a + 4#64) (ha5 : a5 = a + 5#64) (ha6 : a6 = a + 6#64) (ha7 : a7 = a + 7#64)
    (hb0 : val.extractLsb' 0 8 = b0') (hb1 : val.extractLsb' 8 8 = b1')
    (hb2 : val.extractLsb' 16 8 = b2') (hb3 : val.extractLsb' 24 8 = b3')
    (hb4 : val.extractLsb' 32 8 = b4') (hb5 : val.extractLsb' 40 8 = b5')
    (hb6 : val.extractLsb' 48 8 = b6') (hb7 : val.extractLsb' 56 8 = b7') :
    SepStore64 a val P P' := by
  subst ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have hval : (val.extractLsb' 56 8 ++ val.extractLsb' 48 8 ++ val.extractLsb' 40 8 ++
      val.extractLsb' 32 8 ++ val.extractLsb' 24 8 ++ val.extractLsb' 16 8 ++
      val.extractLsb' 8 8 ++ val.extractLsb' 0 8) = val := by bv_kernel
  exact SepStore64.of_eq (by rw [h, ← pointsTo64_eq_bytes8])
    (by rw [h', ← pointsTo64_eq_bytes8, hval])

open Lean Meta Elab Tactic in
meta def proveSepLoadBytes (n : Nat) (a P vTarget : Expr) : TacticM Expr := do
  let P := (← instantiateMVars P).consumeMData
  let atoms := SepSolver.atoms P
  let mut idxs : Array Nat := #[]
  let mut atomExprs : Array Expr := #[]
  let mut haPrfs : Array Expr := #[]
  for k in [0:n] do
    let akTarget ← if k == 0 then Pure.pure a else
      mkAppM ``HAdd.hAdd #[a, mkCanonBitVecLit 64 k]
    let some (i, haOpt) ← findPointsToAtom ``Arm64.pointsTo8 atoms akTarget
      | throwError "proveSepLoadBytes: no byte cell at offset {k} from {a}"
    if idxs.contains i then
      throwError "proveSepLoadBytes: duplicate byte cell at offset {k}"
    let atom := atoms[i]!
    let ak := atom.getArg! 0
    let hak ← match haOpt with
      | some p => Pure.pure p
      | none => proveSepAddrEq ak akTarget
    idxs := idxs.push i
    atomExprs := atomExprs.push atom
    haPrfs := haPrfs.push hak
  let mut restAtoms : Array Expr := #[]
  for h : j in [:atoms.size] do
    if !idxs.contains j then
      restAtoms := restAtoms.push atoms[j]
  let grouped := SepSolver.mkSepList atomExprs
  let rest := SepSolver.mkSepList restAtoms
  let e₁ ← SepSolver.eqAC P (SepSolver.mkSep grouped rest)
  let thmName := match n with
    | 2 => ``SepLoad16.of_bytes2
    | 4 => ``SepLoad32.of_bytes4
    | _ => ``SepLoad64.of_bytes8
  let prf ← mkAppM thmName (#[e₁] ++ haPrfs)
  let prfTy ← instantiateMVars (← inferType prf)
  let loadedVal := prfTy.getArg! 2
  unless ← isDefEq vTarget loadedVal do
    throwError "proveSepLoadBytes: cannot assign loaded value {loadedVal}"
  return prf

open Lean Meta in
meta partial def replaceSepAtom (e : Expr) (idx : Nat) (newExpr : Expr) : Expr :=
  let rec go (cur : Expr) (k : Nat) : Expr × Nat :=
    let curBeta := cur.consumeMData.headBeta
    if curBeta.isAppOfArity ``SepProp.sepConj 2 then
      let l := curBeta.getArg! 0
      let r := curBeta.getArg! 1
      let (l', k1) := go l k
      if k1 > idx && k ≤ idx then
        (SepSolver.mkSep l' r, k1)
      else
        let (r', k2) := go r k1
        (SepSolver.mkSep l r', k2)
    else
      let leaf := (SepSolver.stripMData curBeta).headBeta
      if leaf.isConstOf ``SepProp.emp then
        (cur, k)
      else if k == idx then
        (newExpr, k + 1)
      else
        (cur, k + 1)
  (go e 0).1

open Lean Meta Elab Tactic in
meta def proveSepStoreBytes (n : Nat) (a val P pOutTarget : Expr) : TacticM Expr := do
  let P := (← instantiateMVars P).consumeMData
  let atoms := SepSolver.atoms P
  let mut idxs : Array Nat := #[]
  let mut oldAtomExprs : Array Expr := #[]
  let mut newAtomExprs : Array Expr := #[]
  let mut haPrfs : Array Expr := #[]
  let mut hbPrfs : Array Expr := #[]
  let mut P' := P
  for k in [0:n] do
    let akTarget ← if k == 0 then Pure.pure a else
      mkAppM ``HAdd.hAdd #[a, mkCanonBitVecLit 64 k]
    let some (i, haOpt) ← findPointsToAtom ``Arm64.pointsTo8 atoms akTarget
      | throwError "proveSepStoreBytes: no byte cell at offset {k} from {a}"
    if idxs.contains i then
      throwError "proveSepStoreBytes: duplicate byte cell at offset {k}"
    let atom := atoms[i]!
    let ak := atom.getArg! 0
    let hak ← match haOpt with
      | some p => Pure.pure p
      | none => proveSepAddrEq ak akTarget
    let rawByte ← mkAppM ``BitVec.extractLsb' #[toExpr (8 * k), toExpr (8 : Nat), val]
    let (bk', hbk) ← wpNormSimpLhsExpr rawByte
    let newAtom := mkApp2 (mkConst ``Arm64.pointsTo8) ak bk'
    P' := replaceSepAtom P' i newAtom
    idxs := idxs.push i
    oldAtomExprs := oldAtomExprs.push atom
    newAtomExprs := newAtomExprs.push newAtom
    haPrfs := haPrfs.push hak
    hbPrfs := hbPrfs.push hbk
  unless ← isDefEq pOutTarget P' do
    throwError "proveSepStoreBytes: cannot assign {P'}"
  let mut restAtoms : Array Expr := #[]
  for h : j in [:atoms.size] do
    if !idxs.contains j then
      restAtoms := restAtoms.push atoms[j]
  let groupedOld := SepSolver.mkSepList oldAtomExprs
  let groupedNew := SepSolver.mkSepList newAtomExprs
  let rest := SepSolver.mkSepList restAtoms
  let e₁ ← SepSolver.eqAC P (SepSolver.mkSep groupedOld rest)
  let e₂ ← SepSolver.eqAC P' (SepSolver.mkSep groupedNew rest)
  let thmName := match n with
    | 2 => ``SepStore16.of_bytes2
    | 4 => ``SepStore32.of_bytes4
    | _ => ``SepStore64.of_bytes8
  mkAppM thmName (#[e₁, e₂] ++ haPrfs ++ hbPrfs)

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_sep_access) => do
    let g ← getMainGoal
    g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let tyClean := ty.consumeMData
      let args := tyClean.getAppArgs
      let prf ←
        if tyClean.isAppOf ``SepLoad16 then
          try sepAccess16Proof ty
          catch _ => proveSepLoadBytes 2 args[0]! args[1]! args[2]!
        else if tyClean.isAppOf ``SepStore16 then
          try sepAccess16Proof ty
          catch _ => proveSepStoreBytes 2 args[0]! args[1]! args[2]! args[3]!
        else if tyClean.isAppOf ``SepLoad32 then
          try sepAccess32Proof ty
          catch _ => proveSepLoadBytes 4 args[0]! args[1]! args[2]!
        else if tyClean.isAppOf ``SepStore32 then
          try sepAccess32Proof ty
          catch _ => proveSepStoreBytes 4 args[0]! args[1]! args[2]! args[3]!
        else if tyClean.isAppOf ``SepLoad64 then
          try sepAccessProof ty
          catch _ => proveSepLoadBytes 8 args[0]! args[1]! args[2]!
        else if tyClean.isAppOf ``SepStore64 then
          try sepAccessProof ty
          catch _ => proveSepStoreBytes 8 args[0]! args[1]! args[2]! args[3]!
        else if tyClean.isAppOf ``SepLoad8 then
          try sepAccessProof ty
          catch _ => sepLoad8From32Proof ty
        else
          sepAccessProof ty
      unless ← isDefEq (← inferType prf) ty do throwError "wp_sep_access: type mismatch"
      g.assign prf
    replaceMainGoal []

/-! ### Byte-concatenation simplification rules for `arm64_norm` / `wp_norm` -/

@[arm64_norm, wp_norm]
theorem bv16_extract_0 (b0 b1 : BitVec 8) : (b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv16_extract_8 (b0 b1 : BitVec 8) : (b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv32_extract_0 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv32_extract_8 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv32_extract_16 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv32_extract_24 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_extract_0 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_extract_8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_extract_16 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_extract_24 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_extract_32 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 32 8 = b4 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_extract_40 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 40 8 = b5 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_extract_48 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 48 8 = b6 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_extract_56 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 56 8 = b7 := by bv_kernel

@[arm64_norm, wp_norm]
theorem zext64_bv32_extract_0 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 0 8 = w.extractLsb' 0 8 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_extract_8 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 8 8 = w.extractLsb' 8 8 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_extract_16 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 16 8 = w.extractLsb' 16 8 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_extract_24 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 24 8 = w.extractLsb' 24 8 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_extract_32 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 32 8 = 0#8 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_extract_40 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 40 8 = 0#8 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_extract_48 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 48 8 = 0#8 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_extract_56 (w : BitVec 32) :
    (w.zeroExtend 64).extractLsb' 56 8 = 0#8 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv16_setWidth_8 (b0 b1 : BitVec 8) : (b1 ++ b0).setWidth 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv32_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0).setWidth 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv32_setWidth_16 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0).setWidth 16 = b1 ++ b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_setWidth_8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_setWidth_16 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 16 = b1 ++ b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem bv64_setWidth_32 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).setWidth 32 = b3 ++ b2 ++ b1 ++ b0 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_lsr_40 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) >>> 40 =
      (0#8 ++ b7 ++ b6 ++ b5 : BitVec 32).zeroExtend 64 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_lsr_32 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) >>> 32 =
      (b7 ++ b6 ++ b5 ++ b4 : BitVec 32).zeroExtend 64 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_lsr_48 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) >>> 48 =
      (b7 ++ b6 : BitVec 16).zeroExtend 64 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv32_lsr_16 (b0 b1 b2 b3 : BitVec 8) :
    (b3 ++ b2 ++ b1 ++ b0) >>> 16 = (b3 ++ b2 : BitVec 16).zeroExtend 32 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv32_orr_lsl32_bv8 (b0 b1 b2 b3 b4 : BitVec 8) :
    ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64) ||| ((b4.zeroExtend 64) <<< 32) =
      0#8 ++ 0#8 ++ 0#8 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  have h1 : 0#8 ++ 0#8 ++ 0#8 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 =
      0#8 ++ 0#8 ++ 0#8 ++ b4 ++ (b3 ++ b2 ++ b1 ++ b0) := by bv_kernel
  rw [h1]
  generalize b3 ++ b2 ++ b1 ++ b0 = x
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_extr_40_append (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) ++
      (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)) >>> 40).setWidth 64 =
      a4 ++ a3 ++ a2 ++ a1 ++ a0 ++ b7 ++ b6 ++ b5 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_extr_40_extract (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) ++
      (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0)).extractLsb' 40 64 =
      a4 ++ a3 ++ a2 ++ a1 ++ a0 ++ b7 ++ b6 ++ b5 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_extr_40_orr (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) <<< 24) |||
      ((b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) >>> 40) =
      a4 ++ a3 ++ a2 ++ a1 ++ a0 ++ b7 ++ b6 ++ b5 := by
  have h1 : (a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0) <<< 24 =
      (a4 ++ a3 ++ a2 ++ a1 ++ a0) ++ 0#24 := by bv_kernel
  have h2 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) >>> 40 =
      0#40 ++ (b7 ++ b6 ++ b5) := by bv_kernel
  have h3 : a4 ++ a3 ++ a2 ++ a1 ++ a0 ++ b7 ++ b6 ++ b5 =
      (a4 ++ a3 ++ a2 ++ a1 ++ a0) ++ (b7 ++ b6 ++ b5) := by bv_kernel
  rw [h1, h2, h3]
  clear h1 h2 h3
  generalize a4 ++ a3 ++ a2 ++ a1 ++ a0 = x
  generalize b7 ++ b6 ++ b5 = y
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_one_orr_lsl32 (b0 b1 b2 b3 : BitVec 8) :
    1#64 ||| ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64 <<< 32) =
      b3 ++ b2 ++ b1 ++ b0 ++ 0#8 ++ 0#8 ++ 0#8 ++ 1#8 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv32_orr_lsl16_bv8 (b0 b1 b2 : BitVec 8) :
    ((b1 ++ b0).zeroExtend 32) ||| ((b2.zeroExtend 32) <<< 16) =
      0#8 ++ b2 ++ b1 ++ b0 := by
  have h1 : 0#8 ++ b2 ++ b1 ++ b0 = 0#8 ++ b2 ++ (b1 ++ b0) := by bv_kernel
  rw [h1]
  generalize b1 ++ b0 = x
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_orr_lsl32_bv32 (b0 b1 b2 b3 a0 a1 a2 a3 : BitVec 8) :
    ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64) ||| (((a3 ++ a2 ++ a1 ++ a0).zeroExtend 64) <<< 32) =
      a3 ++ a2 ++ a1 ++ a0 ++ b3 ++ b2 ++ b1 ++ b0 := by
  have h1 : a3 ++ a2 ++ a1 ++ a0 ++ b3 ++ b2 ++ b1 ++ b0 =
      (a3 ++ a2 ++ a1 ++ a0) ++ (b3 ++ b2 ++ b1 ++ b0) := by bv_kernel
  rw [h1]
  generalize b3 ++ b2 ++ b1 ++ b0 = x
  generalize a3 ++ a2 ++ a1 ++ a0 = y
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_orr_lsl8_bv8 (b0 b1 : BitVec 8) :
    (b0.zeroExtend 64) ||| ((b1.zeroExtend 64) <<< 8) =
      0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ b1 ++ b0 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_lsl16_bv32 (b0 b1 b2 b3 : BitVec 8) :
    ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64) <<< 16 =
      0#8 ++ 0#8 ++ b3 ++ b2 ++ b1 ++ b0 ++ 0#8 ++ 0#8 := by bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_orr_lsl48_bv16 (b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (0#8 ++ 0#8 ++ b5 ++ b4 ++ b3 ++ b2 ++ 0#8 ++ 0#8 : BitVec 64) |||
      (((b7 ++ b6).zeroExtend 64) <<< 48) =
      b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ 0#8 ++ 0#8 := by
  have h1 : (0#8 ++ 0#8 ++ b5 ++ b4 ++ b3 ++ b2 ++ 0#8 ++ 0#8 : BitVec 64) =
      0#16 ++ (b5 ++ b4 ++ b3 ++ b2) ++ 0#16 := by bv_kernel
  have h2 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ 0#8 ++ 0#8 : BitVec 64) =
      (b7 ++ b6) ++ (b5 ++ b4 ++ b3 ++ b2) ++ 0#16 := by bv_kernel
  rw [h1, h2]
  generalize b5 ++ b4 ++ b3 ++ b2 = x
  generalize b7 ++ b6 = y
  bv_kernel

@[arm64_norm, wp_norm]
theorem bv64_orr_low16_high48 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ b1 ++ b0 : BitVec 64) |||
      (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ 0#8 ++ 0#8 : BitVec 64) =
      b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by
  have h1 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ b1 ++ b0 : BitVec 64) =
      0#48 ++ (b1 ++ b0) := by bv_kernel
  have h2 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ 0#8 ++ 0#8 : BitVec 64) =
      (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2) ++ 0#16 := by bv_kernel
  have h3 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 : BitVec 64) =
      (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2) ++ (b1 ++ b0) := by bv_kernel
  rw [h1, h2, h3]
  generalize b1 ++ b0 = x
  generalize b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 = y
  bv_kernel

@[arm64_norm, wp_norm]
theorem zext64_bv16_setWidth_8 (b0 b1 : BitVec 8) :
    ((b1 ++ b0).zeroExtend 64).setWidth 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv16_setWidth_16 (w : BitVec 16) :
    (w.zeroExtend 64).setWidth 16 = w := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv16_setWidth_32 (w : BitVec 16) :
    (w.zeroExtend 64).setWidth 32 = w.zeroExtend 32 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext32_bv16_setWidth_8 (b0 b1 : BitVec 8) :
    ((b1 ++ b0).zeroExtend 32).setWidth 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext32_bv16_setWidth_16 (w : BitVec 16) :
    (w.zeroExtend 32).setWidth 16 = w := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_setWidth_8 (b0 b1 b2 b3 : BitVec 8) :
    ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64).setWidth 8 = b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_setWidth_16 (b0 b1 b2 b3 : BitVec 8) :
    ((b3 ++ b2 ++ b1 ++ b0).zeroExtend 64).setWidth 16 = b1 ++ b0 := by bv_kernel
@[arm64_norm, wp_norm]
theorem zext64_bv32_setWidth_32 (w : BitVec 32) :
    (w.zeroExtend 64).setWidth 32 = w := by bv_kernel

/-! ## Byte/word packing, clamping, and layout helpers -/

theorem exists_bytes_of_bv64 (w : BitVec 64) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      w = b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 :=
  ⟨w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
   w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8,
   by bv_kernel⟩

theorem exists_bytes_of_bv32 (w : BitVec 32) :
    ∃ b0 b1 b2 b3 : BitVec 8,
      w = b3 ++ b2 ++ b1 ++ b0 :=
  ⟨w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
   by bv_kernel⟩

theorem pointsTo64_eq_pointsTo32 (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₆₄ (hi ++ lo)) : SepProp) = ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) := by
  rcases exists_bytes_of_bv32 lo with ⟨b0, b1, b2, b3, rfl⟩
  rcases exists_bytes_of_bv32 hi with ⟨b4, b5, b6, b7, rfl⟩
  have hassoc : (b7 ++ b6 ++ b5 ++ b4) ++ (b3 ++ b2 ++ b1 ++ b0) =
      b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0 := by bv_kernel
  rw [hassoc, pointsTo64_eq_bytes8, pointsTo32_eq_bytes4 a, pointsTo32_eq_bytes4 (a + 4#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem bytes8_entails_memRegion_8 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
     ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7)) ⊢
      memRegion a 8 := by
  rw [← pointsTo64_eq_bytes8]
  exact pointsTo64_entails_memRegion a _

theorem unpack64_append_eq_list8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  simp only [unpack64, List.cons.injEq, and_true]
  exact ⟨by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel,
         by bv_kernel, by bv_kernel, by bv_kernel, by bv_kernel⟩

theorem clampScalar_bytes_eq (v : List.Vector (BitVec 8) 32)
    (hclamp : Ratchet.clampScalar v = v)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8)
    (hv : v.toList =
      unpack64 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) ++
      unpack64 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8) ++
      unpack64 (b23 ++ b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16) ++
      unpack64 (b31 ++ b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24)) :
    b0 &&& 0xf8#8 = b0 ∧
    (b31 &&& 0x7f#8) ||| 0x40#8 = b31 ∧
    (b0.zeroExtend 32 &&& 0xfffffff8#32).zeroExtend 64 = b0.zeroExtend 64 ∧
    (((0x40#32 &&& 0xffffffc0#32) ||| (b31.zeroExtend 32 &&& 0x3f#32)).zeroExtend 64) =
      b31.zeroExtend 64 := by
  rw [unpack64_append_eq_list8, unpack64_append_eq_list8,
      unpack64_append_eq_list8, unpack64_append_eq_list8] at hv
  have hv' : v = ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], rfl⟩ :=
    Subtype.ext hv
  rw [hv'] at hclamp
  have h0 : b0 &&& 0xf8#8 = b0 :=
    Option.some.inj (congrArg (fun x => x.toList[0]?) hclamp)
  have h31 : (b31 &&& 0x7f#8) ||| 0x40#8 = b31 :=
    Option.some.inj (congrArg (fun x => x.toList[31]?) hclamp)
  refine ⟨h0, h31, ?_, ?_⟩
  · revert h0; bv_kernel
  · revert h31; bv_kernel

theorem optSenderChainBytes_length (o : Option SenderChain) {pad : List (BitVec 8)}
    (hpad : pad.length = 100) :
    (optSenderChainBytes o pad).length = 104 := by
  cases o with
  | none =>
    simp [optSenderChainBytes, leBytes, hpad]
  | some sc =>
    simp [optSenderChainBytes, senderChainBytes, chainKeyBytes, CryptoGames.HMAC.keyToBytes32,
      leBytes, sc.ratchetKey.publicKey.bytes.toList_length,
      sc.ratchetKey.privateKey.bytes.toList_length]

theorem leBytes_4_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  change [BitVec.ofNat 8 (w.toNat / 1), BitVec.ofNat 8 (w.toNat / 256),
          BitVec.ofNat 8 (w.toNat / 65536), BitVec.ofNat 8 (w.toNat / 16777216)] =
    [BitVec.extractLsb' 0 8 w, BitVec.extractLsb' 8 8 w,
     BitVec.extractLsb' 16 8 w, BitVec.extractLsb' 24 8 w]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb']
  · congr 1
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
    · congr 1
      · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
      · congr 1
        · apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem optSenderChainBytes_none_eq (a : BitVec 64) (pad : List (BitVec 8)) :
    (a ↦ₛ optSenderChainBytes none pad) =
      (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 0#8) ∗ ((a + 2#64) ↦₈ 0#8) ∗ ((a + 3#64) ↦₈ 0#8) ∗
      ((a + 4#64) ↦ₛ pad) := by
  unfold optSenderChainBytes
  have h0 : leBytes 4 0 = [0#8, 0#8, 0#8, 0#8] := rfl
  rw [h0]
  simp only [List.cons_append, List.nil_append, pointsToBytes_cons, BitVec.add_assoc, BitVec.reduceAdd]

theorem optSenderChainBytes_some_eq (a : BitVec 64) (sc : SenderChain) (pad : List (BitVec 8)) :
    (a ↦ₛ optSenderChainBytes (some sc) pad) =
      (a ↦₈ 1#8) ∗ ((a + 1#64) ↦₈ 0#8) ∗ ((a + 2#64) ↦₈ 0#8) ∗ ((a + 3#64) ↦₈ 0#8) ∗
        ((a + 4#64) ↦ₛ sc.ratchetKey.publicKey.bytes.toList) ∗
        ((a + 36#64) ↦ₛ sc.ratchetKey.privateKey.bytes.toList) ∗
        ((a + 68#64) ↦ₛ CryptoGames.HMAC.keyToBytes32 sc.chainKey.key) ∗
        ((a + 100#64) ↦₃₂ sc.chainKey.index) := by
  dsimp only [optSenderChainBytes, senderChainBytes, chainKeyBytes]
  have h1 : leBytes 4 1 = [1#8, 0#8, 0#8, 0#8] := rfl
  have hpk : sc.ratchetKey.publicKey.bytes.toList.length = 32 := sc.ratchetKey.publicKey.bytes.toList_length
  have hsk : sc.ratchetKey.privateKey.bytes.toList.length = 32 := sc.ratchetKey.privateKey.bytes.toList_length
  have hck : (CryptoGames.HMAC.keyToBytes32 sc.chainKey.key).length = 32 := by
    simp [CryptoGames.HMAC.keyToBytes32]
  rw [h1, leBytes_4_eq_unpack32]
  simp only [List.append_assoc, List.cons_append, List.nil_append, pointsToBytes_cons,
    pointsToBytes_append, hpk, hsk, hck, ← pointsTo32_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem exists_unpack64_of_length_40 {bs : List (BitVec 8)} (h : bs.length = 40) :
    ∃ w0 w1 w2 w3 w4 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
            ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : (bs.drop 32).length = 8 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 h1
  refine ⟨w0, w1, w2, w3, w4, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  rw [hsplit, pointsToBytes_append, h0, hp0, hw4, ← pointsTo64_eq_pointsToBytes]
  simp only [sepConj_assoc]

theorem exists_unpack64_of_length_104 {bs : List (BitVec 8)} (h : bs.length = 104) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : BitVec 64,
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
            ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
            ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
            ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
            ((a + 96#64) ↦₆₄ w12)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : (bs.drop 64).length = 40 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, w12, hp2⟩ := exists_unpack64_of_length_40 h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, fun a => ?_⟩
  have hsplit1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
  have hsplit2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by
    have hd : (bs.drop 32).drop 32 = bs.drop 64 := by simp [List.drop_drop]
    rw [← hd, List.take_append_drop]
  rw [hsplit1, pointsToBytes_append, h0, hsplit2, pointsToBytes_append, h1, hp0, hp1, hp2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem mr_cut' (sp : BitVec 64) (c c' n k N : Nat) (hN : n + k = N) (hc' : c - n = c')
    (hn : n ≤ c) (hc : c < 2 ^ 64) (h : N ≤ 2 ^ 64) :
    memRegion (sp - BitVec.ofNat 64 c) N =
      memRegion (sp - BitVec.ofNat 64 c) n ∗ memRegion (sp - BitVec.ofNat 64 c') k := by
  subst hN hc'
  refine memRegion_split' rfl ?_ h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt hc
  have h2 : (c - n) % 2 ^ 64 = c - n := Nat.mod_eq_of_lt (by omega)
  have h3 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, h3]
  omega

theorem mr_cut_add (a : BitVec 64) (c n k : Nat) (h : n + k ≤ 2 ^ 64) :
    memRegion (a + BitVec.ofNat 64 c) (n + k) =
      memRegion (a + BitVec.ofNat 64 c) n ∗ memRegion (a + BitVec.ofNat 64 (c + n)) k := by
  refine memRegion_split' rfl ?_ h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

def trFromSavedRegs (sp : BitVec 64) (s : State) : SepProp :=
  ((sp - 96#64) ↦₆₄ s.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s.readReg64 .lr) ∗
  ((sp - 80#64) ↦₆₄ s.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s.readReg64 .x27) ∗
  ((sp - 64#64) ↦₆₄ s.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s.readReg64 .x25) ∗
  ((sp - 48#64) ↦₆₄ s.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s.readReg64 .x23) ∗
  ((sp - 32#64) ↦₆₄ s.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .x21) ∗
  ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)

theorem stackAt_trFrom (sp : BitVec 64) :
    stackAt sp trFromStack =
      stackAt (sp - 496#64) dropVecChainStack ∗
      memRegion (sp - 496#64) 40 ∗
      memRegion (sp - 456#64) 160 ∗
      (∃∗ u_296 : BitVec 64, (sp - 296#64) ↦₆₄ u_296) ∗
      (∃∗ u_288 : BitVec 32, (sp - 288#64) ↦₃₂ u_288) ∗
      (∃∗ u_284 : BitVec 32, (sp - 284#64) ↦₃₂ u_284) ∗
      memRegion (sp - 280#64) 24 ∗
      memRegion (sp - 256#64) 96 ∗
      (∃∗ u_160 : BitVec 64, (sp - 160#64) ↦₆₄ u_160) ∗
      (∃∗ u_152 : BitVec 64, (sp - 152#64) ↦₆₄ u_152) ∗
      (∃∗ u_144 : BitVec 64, (sp - 144#64) ↦₆₄ u_144) ∗
      memRegion (sp - 136#64) 16 ∗
      memRegion (sp - 120#64) 24 ∗
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
  show memRegion (sp - BitVec.ofNat 64 4688) 4688 = _
  rw [mr_cut' sp 4688 496 4192 496 4688 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 496 456 40 456 496 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 456 296 160 296 456 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 296 288 8 288 296 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 288 284 4 284 288 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 284 280 4 280 284 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 280 256 24 256 280 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 256 160 96 160 256 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 160 152 8 152 160 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 152 144 8 144 152 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 144 136 8 136 144 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 136 120 16 120 136 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 120 96 24 96 120 rfl rfl (by decide) (by decide) (by decide)]
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
  have hstk : memRegion (sp - BitVec.ofNat 64 4688) 4192 = stackAt (sp - 496#64) dropVecChainStack := by
    simp only [stackAt, dropVecChainStack, dropVecMessageKeyStack, allocHookStack]
    congr 1; bv_omega
  rw [hstk]
  simp only [memRegion_eight, memRegion_four]

theorem stackAt_trFrom_fold (sp : BitVec 64) (s0 : State) :
    (stackAt (sp - 496#64) dropVecChainStack ∗
      memRegion (sp - 496#64) 400 ∗
      ((sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp - 88#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
      ((sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
      ((sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      stackAt sp trFromStack := by
  show (stackAt (sp - 496#64) dropVecChainStack ∗ memRegion (sp - 496#64) 400 ∗ _) ⊢
    memRegion (sp - BitVec.ofNat 64 4688) 4688
  rw [mr_cut' sp 4688 496 4192 496 4688 rfl rfl (by decide) (by decide) (by decide)]
  rw [mr_cut' sp 496 96 400 96 496 rfl rfl (by decide) (by decide) (by decide)]
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
  have hstk : memRegion (sp - BitVec.ofNat 64 4688) 4192 = stackAt (sp - 496#64) dropVecChainStack := by
    simp only [stackAt, dropVecChainStack, dropVecMessageKeyStack, allocHookStack]
    congr 1; bv_omega
  rw [hstk]
  refine sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) ?_)
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  refine sepConj_mono (pointsTo64_entails_memRegion _ _) ?_
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

theorem trFromGhost_model_snd (x : TrFromGhost) :
    x.model.2 = { x.st with receiverChains := [], pqRatchetState := [] } := by
  rcases x with ⟨ss, G, ⟨sv, lik, rik, rk, pc, sc, rcs, ppk, pqr⟩, ret⟩
  cases rik <;> rfl

theorem trFromGhost_model_fst_some (x : TrFromGhost) (rem : IdentityKey)
    (h : x.st.remoteIdentity = some rem) :
    x.model.1 = .ok ⟨⟨x.st.rootKey, x.st.senderChain, x.st.receiverChains,
      x.st.previousCounter, maxForwardJumps⟩, x.st.pqRatchetState, x.st.localIdentity, rem⟩ := by
  rcases x with ⟨ss, G, ⟨sv, lik, rik, rk, pc, sc, rcs, ppk, pqr⟩, ret⟩
  dsimp only at h
  subst h
  rfl

theorem trFromGhost_model_fst_none (x : TrFromGhost)
    (h : x.st.remoteIdentity = none) :
    x.model.1 = .error (.invalidSessionStructure .missingRemoteIdentity) := by
  rcases x with ⟨ss, G, ⟨sv, lik, rik, rk, pc, sc, rcs, ppk, pqr⟩, ret⟩
  dsimp only at h
  subst h
  rfl

theorem exists_rootKey_split_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (w7 w15 w23 : BitVec 64) (b31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
           ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
           ((a + 7#64) ↦₆₄ w7) ∗ ((a + 15#64) ↦₆₄ w15) ∗ ((a + 23#64) ↦₆₄ w23) ∗
           ((a + 31#64) ↦₈ b31)) := by
  obtain ⟨u0, u1, u2, u3, _, hp⟩ := exists_unpack64_of_length_32 h
  rcases exists_bytes_of_bv64 u0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  rcases exists_bytes_of_bv64 u1 with ⟨b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩
  rcases exists_bytes_of_bv64 u2 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, rfl⟩
  rcases exists_bytes_of_bv64 u3 with ⟨b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩
  refine ⟨b0, b1, b2, b3, b4, b5, b6,
    b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7,
    b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15,
    b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24 ++ b23,
    b31, fun a => ?_⟩
  rw [hp]
  simp only [pointsTo64_eq_bytes8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_remoteIk_split_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (d0 : BitVec 32) (h4 : BitVec 16) (w6 w14 w22 : BitVec 64) (h30 : BitVec 16),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₃₂ d0) ∗ ((a + 4#64) ↦₁₆ h4) ∗ ((a + 6#64) ↦₆₄ w6) ∗
           ((a + 14#64) ↦₆₄ w14) ∗ ((a + 22#64) ↦₆₄ w22) ∗ ((a + 30#64) ↦₁₆ h30)) := by
  obtain ⟨u0, u1, u2, u3, _, hp⟩ := exists_unpack64_of_length_32 h
  rcases exists_bytes_of_bv64 u0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  rcases exists_bytes_of_bv64 u1 with ⟨b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩
  rcases exists_bytes_of_bv64 u2 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, rfl⟩
  rcases exists_bytes_of_bv64 u3 with ⟨b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩
  refine ⟨b3 ++ b2 ++ b1 ++ b0, b5 ++ b4,
    b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6,
    b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15 ++ b14,
    b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24 ++ b23 ++ b22,
    b31 ++ b30, fun a => ?_⟩
  rw [hp]
  simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_localIk_split_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : BitVec 8)
      (w15 w23 : BitVec 64) (b31 : BitVec 8),
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
           ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
           ((a + 6#64) ↦₈ b6) ∗
           ((a + 7#64) ↦₈ b7) ∗
           ((a + 8#64) ↦₈ b8) ∗
           ((a + 9#64) ↦₃₂ (b12 ++ b11 ++ b10 ++ b9)) ∗
           ((a + 13#64) ↦₁₆ (b14 ++ b13)) ∗
           ((a + 15#64) ↦₆₄ w15) ∗
           ((a + 23#64) ↦₆₄ w23) ∗
           ((a + 31#64) ↦₈ b31))) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
           ((a + 4#64) ↦₁₆ (b5 ++ b4)) ∗
           ((a + 6#64) ↦₈ b6) ∗
           ((a + 7#64) ↦₆₄ (b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7)) ∗
           ((a + 15#64) ↦₆₄ w15) ∗
           ((a + 23#64) ↦₆₄ w23) ∗
           ((a + 31#64) ↦₈ b31))) := by
  obtain ⟨u0, u1, u2, u3, _, hp⟩ := exists_unpack64_of_length_32 h
  rcases exists_bytes_of_bv64 u0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  rcases exists_bytes_of_bv64 u1 with ⟨b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩
  rcases exists_bytes_of_bv64 u2 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, rfl⟩
  rcases exists_bytes_of_bv64 u3 with ⟨b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
    b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15,
    b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24 ++ b23,
    b31, fun a => ?_, fun a => ?_⟩
  · rw [hp]
    simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · rw [hp]
    simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_privKey_split (v : List.Vector (BitVec 8) 32)
    (hclamp : Ratchet.clampScalar v = v) :
    ∃ (b0 : BitVec 8) (d1 : BitVec 32) (h5 : BitVec 16) (w7 w15 w23 : BitVec 64) (b31 : BitVec 8),
      (b0.zeroExtend 32 &&& 0xfffffff8#32).zeroExtend 64 = b0.zeroExtend 64 ∧
      (((0x40#32 &&& 0xffffffc0#32) ||| (b31.zeroExtend 32 &&& 0x3f#32)).zeroExtend 64) =
        b31.zeroExtend 64 ∧
      ∀ a : BitVec 64,
        (a ↦ₛ v.toList) =
          ((a ↦₈ b0) ∗ ((a + 1#64) ↦₃₂ d1) ∗ ((a + 5#64) ↦₁₆ h5) ∗
           ((a + 7#64) ↦₆₄ w7) ∗ ((a + 15#64) ↦₆₄ w15) ∗ ((a + 23#64) ↦₆₄ w23) ∗
           ((a + 31#64) ↦₈ b31)) := by
  have hlen : v.toList.length = 32 := v.toList_length
  obtain ⟨u0, u1, u2, u3, hv, hp⟩ := exists_unpack64_of_length_32 hlen
  rcases exists_bytes_of_bv64 u0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  rcases exists_bytes_of_bv64 u1 with ⟨b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩
  rcases exists_bytes_of_bv64 u2 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, rfl⟩
  rcases exists_bytes_of_bv64 u3 with ⟨b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩
  obtain ⟨_, _, hc0, hc31⟩ := clampScalar_bytes_eq v hclamp
    b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
    b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 hv
  refine ⟨b0, b4 ++ b3 ++ b2 ++ b1, b6 ++ b5,
    b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7,
    b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15,
    b30 ++ b29 ++ b28 ++ b27 ++ b26 ++ b25 ++ b24 ++ b23,
    b31, hc0, hc31, fun a => ?_⟩
  rw [hp]
  simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4, pointsTo16_eq_bytes2,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem exists_pubKey_split_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
       b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : BitVec 8)
      (d28 : BitVec 32),
      (∀ a : BitVec 64,
        (a ↦ₛ bs) =
          ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
           ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
           ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
           ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗
           ((a + 15#64) ↦₆₄ (b22 ++ b21 ++ b20 ++ b19 ++ b18 ++ b17 ++ b16 ++ b15)) ∗
           ((a + 23#64) ↦₃₂ (b26 ++ b25 ++ b24 ++ b23)) ∗
           ((a + 27#64) ↦₈ b27) ∗
           ((a + 28#64) ↦₃₂ d28))) ∧
      (∀ a : BitVec 64,
        ((a ↦₆₄ (b3 ++ b2 ++ b1 ++ b0 ++ 0#8 ++ 0#8 ++ 0#8 ++ 1#8)) ∗
         ((a + 8#64) ↦₆₄ (b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4)) ∗
         ((a + 16#64) ↦₆₄ (b19 ++ b18 ++ b17 ++ b16 ++ b15 ++ b14 ++ b13 ++ b12)) ∗
         ((a + 24#64) ↦₆₄ (b27 ++ b26 ++ b25 ++ b24 ++ b23 ++ b22 ++ b21 ++ b20)) ∗
         ((a + 32#64) ↦₃₂ d28)) =
        ((a ↦₈ 1#8) ∗ ((a + 1#64) ↦₈ 0#8) ∗ ((a + 2#64) ↦₈ 0#8) ∗ ((a + 3#64) ↦₈ 0#8) ∗
         ((a + 4#64) ↦ₛ bs))) := by
  obtain ⟨u0, u1, u2, u3, _, hp⟩ := exists_unpack64_of_length_32 h
  rcases exists_bytes_of_bv64 u0 with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  rcases exists_bytes_of_bv64 u1 with ⟨b8, b9, b10, b11, b12, b13, b14, b15, rfl⟩
  rcases exists_bytes_of_bv64 u2 with ⟨b16, b17, b18, b19, b20, b21, b22, b23, rfl⟩
  rcases exists_bytes_of_bv64 u3 with ⟨b24, b25, b26, b27, b28, b29, b30, b31, rfl⟩
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27,
    b31 ++ b30 ++ b29 ++ b28, fun a => ?_, fun a => ?_⟩
  · rw [hp]
    simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  · rw [hp]
    simp only [pointsTo64_eq_bytes8, pointsTo32_eq_bytes4,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]


end ReceiveRatchetFrom
end CryptoVerification.LibsignalTripleRatchet
