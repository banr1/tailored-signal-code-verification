/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
public import LibsignalBinary.Specifications.RecordCodecsBinary
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Specifications.AsmConstants

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-! ## Stack budget and callee addresses -/

/-- Maximum sub-callee stack budget needed below `save_identity::{closure#0}`'s `0xd0` frame. -/
abbrev saveSubMax (getStk putStk : Nat) : Nat :=
  max (max (max getStk putStk) (max 0x60 64))
    (max publicKeySerializeStackX extHookStack)

/-- Minimum stack budget of `save_identity::{closure#0}` (`0xd0` frame + `saveSubMax`). -/
abbrev saveMinStk (getStk putStk : Nat) : Nat :=
  0xd0 + saveSubMax getStk putStk

theorem getStk_le_saveSubMax (getStk putStk : Nat) : getStk ≤ saveSubMax getStk putStk := by
  unfold saveSubMax; omega

theorem putStk_le_saveSubMax (getStk putStk : Nat) : putStk ≤ saveSubMax getStk putStk := by
  unfold saveSubMax; omega

theorem decStk_le_saveSubMax (getStk putStk : Nat) : 0x60 ≤ saveSubMax getStk putStk := by
  unfold saveSubMax; omega

theorem eqStk_le_saveSubMax (getStk putStk : Nat) : 64 ≤ saveSubMax getStk putStk := by
  unfold saveSubMax; omega

theorem serStk_le_saveSubMax (getStk putStk : Nat) :
    publicKeySerializeStackX ≤ saveSubMax getStk putStk := by
  unfold saveSubMax; omega

theorem hookStk_le_saveSubMax (getStk putStk : Nat) :
    extHookStack ≤ saveSubMax getStk putStk := by
  unfold saveSubMax; omega

/-- Stacked 32-bit `black_box` sub-callee stack budget (`64 + extHookStack` for `PublicKey::eq`). -/
abbrev saveSubMaxExt (getStk putStk : Nat) : Nat :=
  max (max (max getStk putStk) 0x60)
    (max publicKeySerializeStackX Getters.publicKeyEqStackExt)

/-- Minimum stack budget of `save_identity::{closure#0}` under `PublicKeyEqOkExt32`. -/
abbrev saveMinStkExt (getStk putStk : Nat) : Nat :=
  0xd0 + saveSubMaxExt getStk putStk

theorem saveSubMax_max_eqStkExt (getStk putStk : Nat) :
    saveSubMax (max getStk Getters.publicKeyEqStackExt) putStk = saveSubMaxExt getStk putStk := by
  unfold saveSubMax saveSubMaxExt Getters.publicKeyEqStackExt
  omega

theorem saveMinStk_max_eqStkExt (getStk putStk : Nat) :
    saveMinStk (max getStk Getters.publicKeyEqStackExt) putStk = saveMinStkExt getStk putStk := by
  unfold saveMinStk saveMinStkExt
  rw [saveSubMax_max_eqStkExt]

theorem dirGet_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr idSavePollName +
      bv% (2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::get" -
        ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr dirGetName := by
  have h1 := idSavePoll_fnOff
  have h2 := dirGet_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idSavePollName, dirGetName, h1, h2]
  bv_omega

theorem identityKeyDecode_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr idSavePollName +
      bv% (2 ^ 64 + ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode" -
        ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr identityKeyDecodeName := by
  have h1 := idSavePoll_fnOff
  have h2 : libsignalSessionCode.fnOff identityKeyDecodeName =
      num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
      (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idSavePollName,
    identityKeyDecodeName, h1, h2]
  bv_omega

theorem publicKeyEq_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr idSavePollName +
      bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
        ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr Getters.publicKeyEqName := by
  have h1 := idSavePoll_fnOff
  have h2 : libsignalSessionCode.fnOff Getters.publicKeyEqName =
      num% (ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
      (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idSavePollName,
    Getters.publicKeyEqName, h1, h2]
  bv_omega

theorem publicKeySerialize_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr idSavePollName +
      bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
        ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr publicKeySerializeName := by
  have h1 := idSavePoll_fnOff
  have h2 : libsignalSessionCode.fnOff publicKeySerializeName =
      num% (ls_off% "<libsignal_core::curve::PublicKey>::serialize") :=
    Eq.trans (congrArg libsignalSessionCode.fnOff rfl)
      (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::serialize")
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idSavePollName,
    publicKeySerializeName, h1, h2]
  bv_omega

theorem dirPutStr_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr idSavePollName +
      bv% (2 ^ 64 + ls_off% "<libsignal_cli::stores::Dir>::put::<&str>" -
        ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}") =
      (tripleRatchetProgAtExt b ext).fnAddr dirPutStrName := by
  have h1 := idSavePoll_fnOff
  have h2 := dirPutStr_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, idSavePollName,
    dirPutStrName, h1, h2]
  bv_omega

theorem ispoll_dealloc_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName +
        bv% (ls_rel%
          "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"
          "__rustc::__rust_dealloc"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hC (name := idSavePollName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"
      "__rustc::__rust_dealloc"))
    (by rw [idSavePoll_fnOff, (ls_stub% "__rustc::__rust_dealloc")])

theorem ispoll_serialize_ok_at {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hC : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      ((publicKeySerializeSpecX A).inImage img) := by
  rw [publicKeySerialize_fnAddr_eq]
  exact public_key_serialize_ok_ext_x hC

theorem ispoll_publicKeyEq_ok_at {b : BitVec 64} {ext : String → Option (State → State)}
    (hEq : Getters.PublicKeyEqOkExt b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      Getters.publicKeyEqSpec := by
  rw [publicKeyEq_fnAddr_eq]
  exact hEq

theorem ispoll_publicKeyEq_ok_at_ext32 {b : BitVec 64} {ext : String → Option (State → State)}
    (hEq : Getters.PublicKeyEqOkExt32 b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr idSavePollName +
        bv% (2 ^ 64 + ls_off% "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" -
          ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity::{closure#0}"))
      Getters.publicKeyEqSpecExt := by
  rw [publicKeyEq_fnAddr_eq]
  exact hEq

/-! ## Sub-word overlapping 7-byte & 32-byte chunk views -/

/-- Aligned-at-`a` view of 7 consecutive bytes `b0 .. b6` (`4 + 1 + 2` bytes). -/
def overlap7View1 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₁₆ (b6 ++ b5))

/-- Aligned-at-`a + 3` view of the same 7 consecutive bytes `b0 .. b6` (`2 + 1 + 4` bytes). -/
def overlap7View2 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : SepProp :=
  (a ↦₁₆ (b1 ++ b0)) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))

theorem overlap7_realign (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    overlap7View1 a b0 b1 b2 b3 b4 b5 b6 = overlap7View2 a b0 b1 b2 b3 b4 b5 b6 := by
  unfold overlap7View1 overlap7View2
  rw [← pointsTo8_quad a b0 b1 b2 b3, ← pointsTo8_pair (a + 5#64) b5 b6,
      ← pointsTo8_pair a b0 b1, ← pointsTo8_quad (a + 3#64) b3 b4 b5 b6]
  have e4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have e5 : a + 3#64 + 2#64 = a + 5#64 := by bv_omega
  have e6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have e6' : a + 3#64 + 3#64 = a + 6#64 := by bv_omega
  rw [e4, e5, e6, e6']
  ac_rfl

theorem memRegion_7_eq_overlap7View1 (a : BitVec 64) :
    memRegion a 7 =
      (∃∗ b0 : BitVec 8, ∃∗ b1 : BitVec 8, ∃∗ b2 : BitVec 8, ∃∗ b3 : BitVec 8,
       ∃∗ b4 : BitVec 8, ∃∗ b5 : BitVec 8, ∃∗ b6 : BitVec 8,
        overlap7View1 a b0 b1 b2 b3 b4 b5 b6) := by
  rw [show (7 : Nat) = 4 + (1 + 2) by rfl,
      memRegion_split a 4 (1 + 2) (by decide),
      memRegion_split (a + 4#64) 1 2 (by decide),
      ProofLib.memRegion_four a,
      ProofLib.memRegion_one (a + 4#64),
      ProofLib.memRegion_two (a + 4#64 + 1#64),
      show a + 4#64 + 1#64 = a + 5#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun h1 => Entails.sepExists_elim fun b4 =>
      Entails.sepExists_elim fun w0 => ?_
    refine Entails.sepExists_right (w0.extractLsb' 0 8)
      (Entails.sepExists_right (w0.extractLsb' 8 8)
      (Entails.sepExists_right (w0.extractLsb' 16 8)
      (Entails.sepExists_right (w0.extractLsb' 24 8)
      (Entails.sepExists_right b4
      (Entails.sepExists_right (h1.extractLsb' 0 8)
      (Entails.sepExists_right (h1.extractLsb' 8 8) ?_))))))
    unfold overlap7View1
    have hw : (w0.extractLsb' 24 8 ++ w0.extractLsb' 16 8 ++
        w0.extractLsb' 8 8 ++ w0.extractLsb' 0 8) = w0 := by bv_bits
    have hh : (h1.extractLsb' 8 8 ++ h1.extractLsb' 0 8) = h1 := by bv_bits
    rw [hw, hh]
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_elim fun b0 => Entails.sepExists_elim fun b1 =>
      Entails.sepExists_elim fun b2 => Entails.sepExists_elim fun b3 =>
      Entails.sepExists_elim fun b4 => Entails.sepExists_elim fun b5 =>
      Entails.sepExists_elim fun b6 => ?_
    refine Entails.sepExists_right (b6 ++ b5)
      (Entails.sepExists_right b4
      (Entails.sepExists_right (b3 ++ b2 ++ b1 ++ b0) ?_))
    unfold overlap7View1
    exact Entails.of_eq (by ac_rfl)

theorem overlap7View1_entails_memRegion7 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    overlap7View1 a b0 b1 b2 b3 b4 b5 b6 ⊢ memRegion a 7 := by
  rw [memRegion_7_eq_overlap7View1 a]
  exact Entails.sepExists_right b0 (Entails.sepExists_right b1 (Entails.sepExists_right b2
    (Entails.sepExists_right b3 (Entails.sepExists_right b4 (Entails.sepExists_right b5
    (Entails.sepExists_right b6 (Entails.refl _)))))))

theorem overlap7View2_entails_memRegion7 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    overlap7View2 a b0 b1 b2 b3 b4 b5 b6 ⊢ memRegion a 7 := by
  rw [← overlap7_realign]
  exact overlap7View1_entails_memRegion7 a b0 b1 b2 b3 b4 b5 b6

theorem pointsTo64_eq_byte_overlap7View1 (a a1 : BitVec 64) (w : BitVec 64)
    (ha1 : a + 1#64 = a1) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗
      overlap7View1 a1 (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
        (w.extractLsb' 32 8) (w.extractLsb' 40 8) (w.extractLsb' 48 8) (w.extractLsb' 56 8) := by
  subst ha1
  unfold overlap7View1
  rw [pointsTo64_eq_pointsToBytes, unpack64,
      pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_singleton,
      ← pointsTo8_quad (a + 1#64), ← pointsTo8_pair (a + 1#64 + 5#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem byte_overlap7View2_eq_pointsTo64 (a a1 : BitVec 64) (w : BitVec 64)
    (ha1 : a + 1#64 = a1) :
    ((a ↦₈ w.extractLsb' 0 8) ∗
      overlap7View2 a1 (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)
        (w.extractLsb' 32 8) (w.extractLsb' 40 8) (w.extractLsb' 48 8) (w.extractLsb' 56 8)) =
    (a ↦₆₄ w) := by
  rw [← overlap7_realign, ← pointsTo64_eq_byte_overlap7View1 a a1 w ha1]

/-- 32-byte key split matching the exact 7 non-overlapping load/store widths (`4+2+1+8+8+8+1 = 32`). -/
def pkChunksAt (a : BitVec 64) (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8)
    (d3 d4 d5 : BitVec 64) (b6 : BitVec 8) : SepProp :=
  (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₁₆ h1) ∗ ((a + 6#64) ↦₈ b2) ∗
    ((a + 7#64) ↦₆₄ d3) ∗ ((a + 15#64) ↦₆₄ d4) ∗ ((a + 23#64) ↦₆₄ d5) ∗
    ((a + 31#64) ↦₈ b6)

theorem memRegion_32_eq_pkChunksAt (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ w0 : BitVec 32, ∃∗ h1 : BitVec 16, ∃∗ b2 : BitVec 8,
       ∃∗ d3 : BitVec 64, ∃∗ d4 : BitVec 64, ∃∗ d5 : BitVec 64, ∃∗ b6 : BitVec 8,
        pkChunksAt a w0 h1 b2 d3 d4 d5 b6) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 28) (b' := a + 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 4#64) (n := 2) (k := 26) (b' := a + 6#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 6#64) (n := 1) (k := 25) (b' := a + 7#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 7#64) (n := 8) (k := 17) (b' := a + 15#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 15#64) (n := 8) (k := 9) (b' := a + 23#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 23#64) (n := 8) (k := 1) (b' := a + 31#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_four a,
      ProofLib.memRegion_two (a + 4#64),
      ProofLib.memRegion_one (a + 6#64),
      ProofLib.memRegion_eight (a + 7#64),
      ProofLib.memRegion_eight (a + 15#64),
      ProofLib.memRegion_eight (a + 23#64),
      ProofLib.memRegion_one (a + 31#64)]
  simp only [pkChunksAt, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun b6 => Entails.sepExists_elim fun d5 =>
      Entails.sepExists_elim fun d4 => Entails.sepExists_elim fun d3 =>
      Entails.sepExists_elim fun b2 => Entails.sepExists_elim fun h1 =>
      Entails.sepExists_elim fun w0 => ?_
    exact Entails.sepExists_right w0 (Entails.sepExists_right h1 (Entails.sepExists_right b2
      (Entails.sepExists_right d3 (Entails.sepExists_right d4 (Entails.sepExists_right d5
      (Entails.sepExists_right b6 (Entails.of_eq (by ac_rfl))))))))
  · refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun h1 =>
      Entails.sepExists_elim fun b2 => Entails.sepExists_elim fun d3 =>
      Entails.sepExists_elim fun d4 => Entails.sepExists_elim fun d5 =>
      Entails.sepExists_elim fun b6 => ?_
    exact Entails.sepExists_right b6 (Entails.sepExists_right d5 (Entails.sepExists_right d4
      (Entails.sepExists_right d3 (Entails.sepExists_right b2 (Entails.sepExists_right h1
      (Entails.sepExists_right w0 (Entails.of_eq (by ac_rfl))))))))

theorem pkChunksAt_entails_memRegion32 (a : BitVec 64)
    (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8) (d3 d4 d5 : BitVec 64) (b6 : BitVec 8) :
    pkChunksAt a w0 h1 b2 d3 d4 d5 b6 ⊢ memRegion a 32 := by
  rw [memRegion_32_eq_pkChunksAt a]
  exact Entails.sepExists_right w0 (Entails.sepExists_right h1 (Entails.sepExists_right b2
    (Entails.sepExists_right d3 (Entails.sepExists_right d4 (Entails.sepExists_right d5
    (Entails.sepExists_right b6 (Entails.refl _)))))))

theorem pointsToBytes_32_exists_pkChunksAt {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    ∃ (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8) (d3 d4 d5 : BitVec 64) (b6 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ bs) = pkChunksAt a w0 h1 b2 d3 d4 d5 b6 := by
  refine ⟨pack32 (bs.getD 0 0#8) (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8),
    pack16 (bs.getD 4 0#8) (bs.getD 5 0#8),
    bs.getD 6 0#8,
    pack64 (bs.getD 7 0#8) (bs.getD 8 0#8) (bs.getD 9 0#8) (bs.getD 10 0#8)
      (bs.getD 11 0#8) (bs.getD 12 0#8) (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  rw [pointsToBytes_take_drop a 4 bs (by omega),
      pointsToBytes_take_drop (a + 4#64) 2 (bs.drop 4) (by simp [List.length_drop, hlen]),
      List.drop_drop,
      pointsToBytes_take_drop (a + 4#64 + 2#64) 1 (bs.drop 6) (by simp [List.length_drop, hlen]),
      List.drop_drop,
      pointsToBytes_take_drop (a + 4#64 + 2#64 + 1#64) 8 (bs.drop 7) (by simp [List.length_drop, hlen]),
      List.drop_drop,
      pointsToBytes_take_drop (a + 4#64 + 2#64 + 1#64 + 8#64) 8 (bs.drop 15) (by simp [List.length_drop, hlen]),
      List.drop_drop,
      pointsToBytes_take_drop (a + 4#64 + 2#64 + 1#64 + 8#64 + 8#64) 8 (bs.drop 23) (by simp [List.length_drop, hlen]),
      List.drop_drop]
  have hc0 := pointsToBytes_take4_eq_pointsTo32 a bs 0 (by omega)
  simp only [List.drop_zero] at hc0
  have hc4 := pointsToBytes_take2_eq_pointsTo16 (a + 4#64) bs 4 (by omega)
  let rec hdrop : ∀ (l : List (BitVec 8)) (n : Nat),
      n < l.length → (l.drop n).take 1 = [l.getD n 0#8]
    | [], _, h => absurd h (Nat.not_lt_zero _)
    | _ :: _, 0, _ => rfl
    | _ :: xs, n + 1, h => hdrop xs n (Nat.lt_of_succ_lt_succ h)
  have hc6 : ((bs.drop 6).take 1) = [bs.getD 6 0#8] := hdrop bs 6 (by omega)
  have hc31 : bs.drop 31 = [bs.getD 31 0#8] := by
    rw [← List.take_of_length_le (l := bs.drop 31) (i := 1) (by simp [List.length_drop, hlen])]
    exact hdrop bs 31 (by omega)
  have hc7 := pointsToBytes_take8_eq_pointsTo64 (a + 7#64) bs 7 (by omega)
  have hc15 := pointsToBytes_take8_eq_pointsTo64 (a + 15#64) bs 15 (by omega)
  have hc23 := pointsToBytes_take8_eq_pointsTo64 (a + 23#64) bs 23 (by omega)
  simp only [Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hc6, hc31, pointsToBytes_singleton]
  rw [hc0, hc4, hc7, hc15, hc23]
  unfold pkChunksAt
  ac_rfl

/-! ## Stack frame, 48-byte slots, `speAt`, `idSaveOutAt`, `protocolAddressAt` -/

theorem s48_split_byte7 (sp s48 s56w : BitVec 64) :
    (((sp - 0xa0#64) ↦₆₄ s48) ∗ ((sp - 0x98#64) ↦₆₄ s56w)) =
      (((sp - 0xa0#64) ↦₆₄ s48) ∗ ((sp - 0x98#64) ↦₈ s56w.extractLsb' 0 8) ∗
        overlap7View1 (sp - 0x97#64) (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8)
          (s56w.extractLsb' 24 8) (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8)
          (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8)) := by
  rw [pointsTo64_eq_byte_overlap7View1 (sp - 0x98#64) (sp - 0x97#64) s56w (by bv_omega)]

theorem s48_words_entail_memRegion16 (sp s48 s56w : BitVec 64) :
    (((sp - 0xa0#64) ↦₆₄ s48) ∗ ((sp - 0x98#64) ↦₆₄ s56w)) ⊢
      memRegion (sp - 0xa0#64) 16 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0xa0#64) (n := 8) (k := 8)
        (b' := sp - 0x98#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem s48_byte7_entails_memRegion16 (sp s48 : BitVec 64) (s56 d1 d2 d3 d4 d5 d6 d7 : BitVec 8) :
    (((sp - 0xa0#64) ↦₆₄ s48) ∗ ((sp - 0x98#64) ↦₈ s56) ∗
      overlap7View1 (sp - 0x97#64) d1 d2 d3 d4 d5 d6 d7) ⊢
      memRegion (sp - 0xa0#64) 16 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
        (overlap7View1_entails_memRegion7 _ _ _ _ _ _ _ _))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x98#64) (n := 1) (k := 7)
        (b' := sp - 0x97#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0xa0#64) (n := 8) (k := 8)
        (b' := sp - 0x98#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {k m : Nat} (hle : k ≤ m) (hm : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  have heq : m = k + (m - k) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp k (m - k) (by omega), ← heq]

theorem sepWPp_conseq {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp}
    {Q Qp : State → SepProp → Prop} (h : P ⊢ P')
    (hw : SepWPp prog ret s P' Q Qp) : SepWPp prog ret s P Q Qp :=
  fun R hm hL => hw R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem sepWPp_of_sepWP_final {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog ret s P Q) : SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, hok | hoom⟩
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_with_stk_bound {prog : Program} {ret : BitVec 64} {s : State}
    {stk : Nat} {a v : BitVec 64} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P ⊢ stackAt s.sp stk ∗ (a ↦₆₄ v) ∗ Rest)
    (hw : stk ≤ 2 ^ 64 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := fun R hm hL => by
  have hm' : s.mem ⊨ memRegion (s.sp - BitVec.ofNat 64 stk) stk ∗ ((a ↦₆₄ v) ∗ (Rest ∗ R)) := by
    have h1 := Satisfies.mono (sepConj_mono_left hfoc) hm
    simpa only [stackAt, sepConj_assoc] using h1
  exact hw (memRegion_bound_of_pointsTo64 hm') R hm hL

def savedCalleeSlots (s0 : State) : SepProp :=
  ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
  ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 .x19)

/-- Exact 208-byte (`0xd0`) frame decomposition of `save_identity::{closure#0}`. -/
def savePollFrameSlots (sp : BitVec 64)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8) (s48 s56w : BitVec 64)
    (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : BitVec 64) : SepProp :=
  memRegion (sp - 0xd0#64) 8 ∗
  overlap7View1 (sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
  ((sp - 0xc1#64) ↦₈ c15) ∗
  ((sp - 0xc0#64) ↦₆₄ s16) ∗
  ((sp - 0xb8#64) ↦₈ s24) ∗
  memRegion (sp - 0xb7#64) 7 ∗
  ((sp - 0xb0#64) ↦₆₄ s32) ∗
  ((sp - 0xa8#64) ↦₈ s40) ∗
  memRegion (sp - 0xa7#64) 7 ∗
  ((sp - 0xa0#64) ↦₆₄ s48) ∗
  ((sp - 0x98#64) ↦₆₄ s56w) ∗
  memRegion (sp - 0x90#64) 48 ∗
  ((sp - 0x60#64) ↦₆₄ g0) ∗ ((sp - 0x58#64) ↦₆₄ g1) ∗
  ((sp - 0x50#64) ↦₆₄ g2) ∗ ((sp - 0x48#64) ↦₆₄ g3) ∗
  ((sp - 0x40#64) ↦₆₄ g4) ∗ ((sp - 0x38#64) ↦₆₄ g5) ∗
  ((sp - 0x30#64) ↦₆₄ g6) ∗ ((sp - 0x28#64) ↦₆₄ g7) ∗
  ((sp - 0x20#64) ↦₆₄ g8) ∗ ((sp - 0x18#64) ↦₆₄ g9) ∗
  ((sp - 0x10#64) ↦₆₄ g10) ∗ ((sp - 0x08#64) ↦₆₄ g11)

theorem stackAt_savePoll_eq (sp : BitVec 64) {sub : Nat} (hsub : 0xd0 + sub ≤ 2 ^ 64) :
    stackAt sp (0xd0 + sub) =
      stackAt (sp - 0xd0#64) sub ∗
      (∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8, ∃∗ c4 : BitVec 8,
       ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8, ∃∗ c7 : BitVec 8, ∃∗ c15 : BitVec 8,
       ∃∗ s16 : BitVec 64, ∃∗ s24 : BitVec 8, ∃∗ s32 : BitVec 64, ∃∗ s40 : BitVec 8,
       ∃∗ s48 : BitVec 64, ∃∗ s56w : BitVec 64,
       ∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64, ∃∗ g3 : BitVec 64,
       ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64, ∃∗ g6 : BitVec 64, ∃∗ g7 : BitVec 64,
       ∃∗ g8 : BitVec 64, ∃∗ g9 : BitVec 64, ∃∗ g10 : BitVec 64, ∃∗ g11 : BitVec 64,
        savePollFrameSlots sp c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s48 s56w
          g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11) := by
  have htop : stackAt sp (sub + 208) = stackAt (sp - 0xd0#64) sub ∗ memRegion (sp - 0xd0#64) 208 := by
    simp only [stackAt]
    have hbv : sp - BitVec.ofNat 64 (sub + 208) = sp - 0xd0#64 - BitVec.ofNat 64 sub := by bv_omega
    rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (sub + 208))
          (n := sub) (k := 208) (b' := sp - 0xd0#64)
          (by omega) (by bv_omega) (by omega), hbv]
  rw [show 0xd0 + sub = sub + 208 by omega, htop,
      ProofLib.memRegion_split' (b := sp - 0xd0#64) (n := 8) (k := 200) (b' := sp - 0xc8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xc8#64) (n := 7) (k := 193) (b' := sp - 0xc1#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xc1#64) (n := 1) (k := 192) (b' := sp - 0xc0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xc0#64) (n := 8) (k := 184) (b' := sp - 0xb8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xb8#64) (n := 1) (k := 183) (b' := sp - 0xb7#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xb7#64) (n := 7) (k := 176) (b' := sp - 0xb0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xb0#64) (n := 8) (k := 168) (b' := sp - 0xa8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xa8#64) (n := 1) (k := 167) (b' := sp - 0xa7#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xa7#64) (n := 7) (k := 160) (b' := sp - 0xa0#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0xa0#64) (n := 8) (k := 152) (b' := sp - 0x98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x98#64) (n := 8) (k := 144) (b' := sp - 0x90#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 48) (k := 96) (b' := sp - 0x60#64) rfl (by bv_omega) (by decide),
      memRegion_7_eq_overlap7View1 (sp - 0xc8#64),
      ProofLib.memRegion_one (sp - 0xc1#64),
      ProofLib.memRegion_eight (sp - 0xc0#64),
      ProofLib.memRegion_one (sp - 0xb8#64),
      ProofLib.memRegion_eight (sp - 0xb0#64),
      ProofLib.memRegion_one (sp - 0xa8#64),
      ProofLib.memRegion_eight (sp - 0xa0#64),
      ProofLib.memRegion_eight (sp - 0x98#64),
      show (96 : Nat) = 8 * 12 by rfl,
      ProofLib.memRegion_cells (sp - 0x60#64) 12 (by decide)]
  have hc12 : cells (sp - 0x60#64) 12 =
      (∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64, ∃∗ g3 : BitVec 64,
       ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64, ∃∗ g6 : BitVec 64, ∃∗ g7 : BitVec 64,
       ∃∗ g8 : BitVec 64, ∃∗ g9 : BitVec 64, ∃∗ g10 : BitVec 64, ∃∗ g11 : BitVec 64,
        ((sp - 0x60#64) ↦₆₄ g0) ∗ ((sp - 0x58#64) ↦₆₄ g1) ∗
        ((sp - 0x50#64) ↦₆₄ g2) ∗ ((sp - 0x48#64) ↦₆₄ g3) ∗
        ((sp - 0x40#64) ↦₆₄ g4) ∗ ((sp - 0x38#64) ↦₆₄ g5) ∗
        ((sp - 0x30#64) ↦₆₄ g6) ∗ ((sp - 0x28#64) ↦₆₄ g7) ∗
        ((sp - 0x20#64) ↦₆₄ g8) ∗ ((sp - 0x18#64) ↦₆₄ g9) ∗
        ((sp - 0x10#64) ↦₆₄ g10) ∗ ((sp - 0x08#64) ↦₆₄ g11)) := by
    cells_unfold
  rw [hc12]
  simp only [savePollFrameSlots, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun g0 => Entails.sepExists_elim fun g1 =>
      Entails.sepExists_elim fun g2 => Entails.sepExists_elim fun g3 =>
      Entails.sepExists_elim fun g4 => Entails.sepExists_elim fun g5 =>
      Entails.sepExists_elim fun g6 => Entails.sepExists_elim fun g7 =>
      Entails.sepExists_elim fun g8 => Entails.sepExists_elim fun g9 =>
      Entails.sepExists_elim fun g10 => Entails.sepExists_elim fun g11 =>
      Entails.sepExists_elim fun s56w => Entails.sepExists_elim fun s48 =>
      Entails.sepExists_elim fun s40 =>
      Entails.sepExists_elim fun s32 => Entails.sepExists_elim fun s24 =>
      Entails.sepExists_elim fun s16 => Entails.sepExists_elim fun c15 =>
      Entails.sepExists_elim fun c1 => Entails.sepExists_elim fun c2 =>
      Entails.sepExists_elim fun c3 => Entails.sepExists_elim fun c4 =>
      Entails.sepExists_elim fun c5 => Entails.sepExists_elim fun c6 =>
      Entails.sepExists_elim fun c7 => ?_
    exact Entails.sepExists_right c1 (Entails.sepExists_right c2 (Entails.sepExists_right c3
      (Entails.sepExists_right c4 (Entails.sepExists_right c5 (Entails.sepExists_right c6
      (Entails.sepExists_right c7 (Entails.sepExists_right c15 (Entails.sepExists_right s16
      (Entails.sepExists_right s24 (Entails.sepExists_right s32 (Entails.sepExists_right s40
      (Entails.sepExists_right s48 (Entails.sepExists_right s56w
      (Entails.sepExists_right g0 (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right g3 (Entails.sepExists_right g4
      (Entails.sepExists_right g5 (Entails.sepExists_right g6 (Entails.sepExists_right g7
      (Entails.sepExists_right g8 (Entails.sepExists_right g9 (Entails.sepExists_right g10
      (Entails.sepExists_right g11 (Entails.of_eq (by ac_rfl)))))))))))))))))))))))))))
  · refine Entails.sepExists_elim fun c1 => Entails.sepExists_elim fun c2 =>
      Entails.sepExists_elim fun c3 => Entails.sepExists_elim fun c4 =>
      Entails.sepExists_elim fun c5 => Entails.sepExists_elim fun c6 =>
      Entails.sepExists_elim fun c7 => Entails.sepExists_elim fun c15 =>
      Entails.sepExists_elim fun s16 => Entails.sepExists_elim fun s24 =>
      Entails.sepExists_elim fun s32 => Entails.sepExists_elim fun s40 =>
      Entails.sepExists_elim fun s48 => Entails.sepExists_elim fun s56w =>
      Entails.sepExists_elim fun g0 =>
      Entails.sepExists_elim fun g1 => Entails.sepExists_elim fun g2 =>
      Entails.sepExists_elim fun g3 => Entails.sepExists_elim fun g4 =>
      Entails.sepExists_elim fun g5 => Entails.sepExists_elim fun g6 =>
      Entails.sepExists_elim fun g7 => Entails.sepExists_elim fun g8 =>
      Entails.sepExists_elim fun g9 => Entails.sepExists_elim fun g10 =>
      Entails.sepExists_elim fun g11 => ?_
    exact Entails.sepExists_right g0 (Entails.sepExists_right g1 (Entails.sepExists_right g2
      (Entails.sepExists_right g3 (Entails.sepExists_right g4 (Entails.sepExists_right g5
      (Entails.sepExists_right g6 (Entails.sepExists_right g7 (Entails.sepExists_right g8
      (Entails.sepExists_right g9 (Entails.sepExists_right g10 (Entails.sepExists_right g11
      (Entails.sepExists_right s56w (Entails.sepExists_right s48 (Entails.sepExists_right s40
      (Entails.sepExists_right s32 (Entails.sepExists_right s24 (Entails.sepExists_right s16
      (Entails.sepExists_right c15
      (Entails.sepExists_right c1 (Entails.sepExists_right c2 (Entails.sepExists_right c3
      (Entails.sepExists_right c4 (Entails.sepExists_right c5 (Entails.sepExists_right c6
      (Entails.sepExists_right c7 (Entails.of_eq (by ac_rfl)))))))))))))))))))))))))))

theorem restore_savePollStack (s0 : State) {getStk putStk stk : Nat}
    (hstk : saveMinStk getStk putStk ≤ stk) (hhi : stk ≤ 2 ^ 64)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8) :
    (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
      stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
      memRegion (s0.sp - 0xd0#64) 8 ∗
      overlap7View2 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
      ((s0.sp - 0xc1#64) ↦₈ c15) ∗
      ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
      ((s0.sp - 0xb8#64) ↦₈ s24) ∗
      memRegion (s0.sp - 0xb7#64) 7 ∗
      ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
      ((s0.sp - 0xa8#64) ↦₈ s40) ∗
      memRegion (s0.sp - 0xa7#64) 7 ∗
      memRegion (s0.sp - 0xa0#64) 16 ∗
      memRegion (s0.sp - 0x90#64) 48 ∗
      savedCalleeSlots s0) ⊢
      stackAt s0.sp stk := by
  have hmin : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
  rw [stackAt_sub_split s0.sp hstk hhi]
  refine sepConj_mono_right ?_
  rw [stackAt_savePoll_eq s0.sp hmin,
      ProofLib.memRegion_split' (b := s0.sp - 0xa0#64) (n := 8) (k := 8)
        (b' := s0.sp - 0x98#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (s0.sp - 0xa0#64),
      ProofLib.memRegion_eight (s0.sp - 0x98#64),
      ← overlap7_realign]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun s56w => Entails.sepExists_elim fun s48 => ?_
  refine Entails.sepExists_right c1 (Entails.sepExists_right c2 (Entails.sepExists_right c3
    (Entails.sepExists_right c4 (Entails.sepExists_right c5 (Entails.sepExists_right c6
    (Entails.sepExists_right c7 (Entails.sepExists_right c15 (Entails.sepExists_right s16
    (Entails.sepExists_right s24 (Entails.sepExists_right s32 (Entails.sepExists_right s40
    (Entails.sepExists_right s48 (Entails.sepExists_right s56w
      (Entails.sepExists_right (s0.readReg64 .x29) (Entails.sepExists_right (s0.readReg64 .lr)
      (Entails.sepExists_right (s0.readReg64 .x28) (Entails.sepExists_right (s0.readReg64 .x27)
      (Entails.sepExists_right (s0.readReg64 .x26) (Entails.sepExists_right (s0.readReg64 .x25)
      (Entails.sepExists_right (s0.readReg64 .x24) (Entails.sepExists_right (s0.readReg64 .x23)
      (Entails.sepExists_right (s0.readReg64 .x22) (Entails.sepExists_right (s0.readReg64 .x21)
      (Entails.sepExists_right (s0.readReg64 .x20) (Entails.sepExists_right (s0.readReg64 .x19)
        (by unfold savePollFrameSlots savedCalleeSlots; exact Entails.of_eq (by ac_rfl)))))))))))))))))))))))))))

/-! ## `protocolAddressAt`, `Vec<u8>`, `speAt`, and `idSaveOutAt` lemmas -/

def vecU8Tail (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  if cap = 0#64 then emp
  else A.live ptr cap.toNat 1 ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8_eq_bytes_tail (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8))
    (v8 v16 : BitVec 64) (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16) :
    vecU8 A v bs =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs) := by
  subst hv8; subst hv16
  unfold vecU8 vecU8At vecHeader vecU8Tail SpqrV1.ChainProofs.bytesAt
  simp only [Bool.false_eq_true, ite_false]
  refine ProofLib.sepExists_congr fun cap => ProofLib.sepExists_congr fun ptr => ?_
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero]
  by_cases hc : cap = 0#64
  · subst hc
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, ite_true]
    have hcomm :
        (((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) ∗
          ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗ emp) =
        (⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length))) := by
      rw [sepConj_emp]
      ac_rfl
    rw [hcomm]
    apply sepProp_ext <;>
      (apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
       have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
       subst hbs
       apply Entails.pure_right ⟨hlen, hlt, hptr⟩
       simp only [pointsToBytes_nil, sepConj_emp]
       exact Entails.refl _)
  · simp only [hc, ite_false]
    ac_rfl

/-- Borrow `SpqrV1.ChainProofs.bytesAt false g.name.ptr g.name.bytes` out of `protocolAddressAt`. -/
def addrRestAt (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) : SepProp :=
  ⌜g.name.bytes.length ≤ g.name.cap.toNat ∧ g.name.cap.toNat < 2 ^ 63 ∧ g.name.ptr ≠ 0#64⌝ ∗
  (addr ↦₆₄ g.name.cap) ∗
  vecU8Tail A g.name.cap g.name.ptr g.name.bytes ∗
  ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7

theorem protocolAddressAt_borrow (A : RustAlloc) (g : AddrGhost) (addr : BitVec 64) :
    protocolAddressAt A g addr =
      (((addr + 8#64) ↦₆₄ g.name.ptr) ∗
        ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
        SpqrV1.ChainProofs.bytesAt false g.name.ptr g.name.bytes ∗
        addrRestAt A g addr) := by
  unfold protocolAddressAt vecGhostAt vecU8At vecHeader addrRestAt vecU8Tail SpqrV1.ChainProofs.bytesAt
  simp only [Bool.false_eq_true, ite_false]
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  rw [hzero]
  by_cases hc : g.name.cap = 0#64
  · rw [hc]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, ite_true]
    apply sepProp_ext
    · refine Entails.trans (Entails.of_eq (by ac_rfl :
          ((((addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length)) ∗
            ⌜g.name.bytes.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ g.name.ptr ≠ 0#64⌝ ∗ emp) ∗
            ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7) =
          (⌜g.name.bytes.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ g.name.ptr ≠ 0#64⌝ ∗
            ((addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
              ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
              ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7)))) ?_
      apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
      have hbs : g.name.bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hbs] at hlen ⊢
      simp only [pointsToBytes_nil, emp_sepConj]
      refine Entails.trans (Entails.pure_right (φ := ([] : List (BitVec 8)).length ≤ 0 ∧ 0 < 2 ^ 63 ∧ g.name.ptr ≠ 0#64) ⟨hlen, hlt, hptr⟩ (Entails.refl _)) ?_
      exact Entails.of_eq (by ac_rfl)
    · refine Entails.trans (Entails.of_eq (by ac_rfl :
          (((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗
            ⌜g.name.bytes.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ g.name.ptr ≠ 0#64⌝ ∗
            (addr ↦₆₄ 0#64) ∗ emp ∗
            ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7) =
          (⌜g.name.bytes.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ g.name.ptr ≠ 0#64⌝ ∗
            ((addr + 8#64) ↦₆₄ g.name.ptr) ∗
            ((addr + 16#64) ↦₆₄ BitVec.ofNat 64 g.name.bytes.length) ∗
            (g.name.ptr ↦ₛ g.name.bytes) ∗
            (addr ↦₆₄ 0#64) ∗
            ((addr + 24#64) ↦₈ g.device) ∗ memRegion (addr + 25#64) 7))) ?_
      apply Entails.pure_left; rintro ⟨hlen, hlt, hptr⟩
      have hbs : g.name.bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hbs] at hlen ⊢
      simp only [pointsToBytes_nil, emp_sepConj]
      refine Entails.trans (Entails.pure_right (φ := ([] : List (BitVec 8)).length ≤ 0 ∧ 0 < 2 ^ 63 ∧ g.name.ptr ≠ 0#64) ⟨hlen, hlt, hptr⟩ (Entails.refl _)) ?_
      exact Entails.of_eq (by ac_rfl)
  · simp only [hc, ite_false]
    ac_rfl

theorem vecU8_free_zero (A : RustAlloc) (ptr : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length ≤ (0#64 : BitVec 64).toNat) :
    (SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8Tail A 0#64 ptr bs) ⊢ emp := by
  have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
  subst hbs
  simp only [SpqrV1.ChainProofs.bytesAt, vecU8Tail, Bool.false_eq_true, ite_false, ite_true,
    pointsToBytes_nil, emp_sepConj]
  exact Entails.refl _

theorem vecU8_free_ne (A : RustAlloc) {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hc : cap ≠ 0#64) (hlen : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    (SpqrV1.ChainProofs.bytesAt false ptr bs ∗ vecU8Tail A cap ptr bs) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  simp only [SpqrV1.ChainProofs.bytesAt, vecU8Tail, Bool.false_eq_true, hc, ite_false]
  have hpull :
      ((ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) =
      (A.live ptr cap.toNat 1 ∗
        ((ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
    ac_rfl
  rw [hpull]
  refine sepConj_mono_right ?_
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)) ?_
  have hmerge := (ProofLib.memRegion_split (b := ptr) bs.length (cap.toNat - bs.length) (by omega)).symm
  rw [hmerge, show bs.length + (cap.toNat - bs.length) = cap.toNat by omega]
  exact Entails.refl _

theorem layoutOk_u8_of_ne_zero {cap : BitVec 64} (hc : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h => hc (BitVec.eq_of_toNat_eq h))
  exact ⟨hpos, ⟨0, rfl⟩, by omega⟩

theorem boxU8Buf_to_vecU8_33 (A : RustAlloc) (sp serPtr : BitVec 64) (key : IdentityKey) :
    (((sp - 0x90#64) ↦₆₄ 33#64) ∗ ((sp - 0x88#64) ↦₆₄ serPtr) ∗
      ((sp - 0x80#64) ↦₆₄ 33#64) ∗ boxU8Buf A serPtr key.publicKey.serialize) ⊢
      vecU8 A (sp - 0x90#64) key.serialize := by
  have hlen : key.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize]
  have hpklen : key.publicKey.serialize.length = 33 := hlen
  have hser : key.publicKey.serialize = key.serialize := rfl
  unfold boxU8Buf vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 33#64 (Entails.sepExists_right serPtr ?_)
  have e8 : sp - 0x90#64 + 8#64 = sp - 0x88#64 := by bv_omega
  have e16 : sp - 0x90#64 + 16#64 = sp - 0x80#64 := by bv_omega
  have hnil : key.publicKey.serialize ≠ [] := by
    simp [PublicKey.serialize]
  have h33nat : (33#64 : BitVec 64).toNat = 33 := rfl
  have h0eq : (0 : BitVec 64) = 0#64 := rfl
  have hne : (33#64 : BitVec 64) ≠ 0#64 := by decide
  simp only [e8, e16, hnil, ite_false]
  rw [hpklen, hlen, h33nat, h0eq]
  simp only [hne, ite_false, Nat.sub_self, ProofLib.memRegion_zero, sepConj_emp, hser]
  refine Entails.trans (Entails.of_eq (by ac_rfl :
      (((sp - 0x90#64) ↦₆₄ 33#64) ∗ ((sp - 0x88#64) ↦₆₄ serPtr) ∗
        ((sp - 0x80#64) ↦₆₄ 33#64) ∗
        (⌜serPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗ (A.live serPtr 33 1 ∗ (serPtr ↦ₛ key.serialize)))) =
      (⌜serPtr ≠ 0#64 ∧ 33 < 2 ^ 63⌝ ∗
        (((sp - 0x90#64) ↦₆₄ 33#64) ∗ ((sp - 0x88#64) ↦₆₄ serPtr) ∗
          ((sp - 0x80#64) ↦₆₄ 33#64) ∗
          A.live serPtr 33 1 ∗ (serPtr ↦ₛ key.serialize))))) ?_
  apply Entails.pure_left; rintro ⟨hnz, hlt⟩
  refine Entails.trans
    (Entails.pure_right (φ := 33 ≤ 33 ∧ 33 < 2 ^ 63 ∧ serPtr ≠ 0#64) ⟨by omega, hlt, hnz⟩ (Entails.refl _)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem getResultAt_ok_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 0x90#64) (.ok bs) =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 0x90#64) ↦₆₄ okTagVec) ∗
        ((sp - 0x88#64) ↦₆₄ cap) ∗
        ((sp - 0x80#64) ↦₆₄ ptr) ∗
        ((sp - 0x78#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs ∗
        memRegion (sp - 0x70#64) 16) := by
  dsimp only [getResultAt, vecResultAt]
  have e1 : sp - 0x90#64 + 8#64 = sp - 0x88#64 := by bv_omega
  have e2 : sp - 0x90#64 + 0x20#64 = sp - 0x70#64 := by bv_omega
  rw [e1, e2, vecU8_eq_bytes_tail A (sp - 0x88#64) bs (sp - 0x80#64) (sp - 0x78#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepProp_ext <;>
    (refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl))))

theorem slot90_words4_collapse (sp w0 w1 w2 w3 : BitVec 64) :
    (((sp - 0x90#64) ↦₆₄ w0) ∗ ((sp - 0x88#64) ↦₆₄ w1) ∗
      ((sp - 0x80#64) ↦₆₄ w2) ∗ ((sp - 0x78#64) ↦₆₄ w3) ∗
      memRegion (sp - 0x70#64) 16) ⊢
      memRegion (sp - 0x90#64) 48 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x78#64) (n := 8) (k := 16) (b' := sp - 0x70#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x80#64) (n := 8) (k := 24) (b' := sp - 0x78#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x88#64) (n := 8) (k := 32) (b' := sp - 0x80#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 8) (k := 40) (b' := sp - 0x88#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot90_pk88_to_32_16 (sp wtag : BitVec 64)
    (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8) (d3 d4 d5 : BitVec 64) (b6 : BitVec 8) :
    (((sp - 0x90#64) ↦₆₄ wtag) ∗
      pkChunksAt (sp - 0x88#64) w0 h1 b2 d3 d4 d5 b6 ∗
      memRegion (sp - 0x68#64) 8) ⊢
      memRegion (sp - 0x90#64) 32 ∗ memRegion (sp - 0x70#64) 16 := by
  refine Entails.trans
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pkChunksAt_entails_memRegion32 _ _ _ _ _ _ _ _) (Entails.refl _))) ?_
  rw [← ProofLib.memRegion_split' (b := sp - 0x88#64) (n := 32) (k := 8) (b' := sp - 0x68#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 8) (k := 40) (b' := sp - 0x88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 32) (k := 16) (b' := sp - 0x70#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot90_bytes32_16_collapse (sp : BitVec 64) {bs : List (BitVec 8)} (hlen : bs.length = 32) :
    (((sp - 0x90#64) ↦ₛ bs) ∗ memRegion (sp - 0x70#64) 16) ⊢ memRegion (sp - 0x90#64) 48 := by
  refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion _ _)) ?_
  rw [hlen, ← ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 32) (k := 16)
        (b' := sp - 0x70#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem slot90_split_vec24 (sp : BitVec 64) :
    memRegion (sp - 0x90#64) 48 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 0x90#64) ↦₆₄ v0) ∗ ((sp - 0x88#64) ↦₆₄ v1) ∗
        ((sp - 0x80#64) ↦₆₄ v2) ∗ memRegion (sp - 0x78#64) 24) := by
  rw [ProofLib.memRegion_split' (b := sp - 0x90#64) (n := 8) (k := 40) (b' := sp - 0x88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x88#64) (n := 8) (k := 32) (b' := sp - 0x80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 0x80#64) (n := 8) (k := 24) (b' := sp - 0x78#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun v2 => Entails.sepExists_elim fun v1 =>
      Entails.sepExists_elim fun v0 => ?_
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1
      (Entails.sepExists_right v2 (Entails.of_eq (by ac_rfl))))
  · refine Entails.sepExists_elim fun v0 => Entails.sepExists_elim fun v1 =>
      Entails.sepExists_elim fun v2 => ?_
    exact Entails.sepExists_right v2 (Entails.sepExists_right v1
      (Entails.sepExists_right v0 (Entails.of_eq (by ac_rfl))))

theorem speAt_read_invalidState_unpack (A : RustAlloc) (sp : BitVec 64) :
    speAt A (utf8 "read") (sp - 0x90#64) .invalidState =
      (∃∗ bs : List (BitVec 8), ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ fnPtr : BitVec 64,
        ((sp - 0x90#64) ↦₆₄ speWord 1) ∗
        ((sp - 0x88#64) ↦₆₄ cap) ∗ ((sp - 0x80#64) ↦₆₄ ptr) ∗
        ((sp - 0x78#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((sp - 0x70#64) ↦₆₄ fnPtr) ∗
        ((sp - 0x68#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          if cap = 0#64 then emp
          else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
            memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗
        (fnPtr ↦ᵣ utf8 "read")) := by
  unfold speAt vecU8 vecU8At vecHeader strRefAt
  have e1 : sp - 0x90#64 + asm64% spePayloadOff = sp - 0x88#64 := by bv_omega
  have e2 : sp - 0x88#64 + 8#64 = sp - 0x80#64 := by bv_omega
  have e3 : sp - 0x88#64 + 16#64 = sp - 0x78#64 := by bv_omega
  have e4 : sp - 0x90#64 + asm64% speInvalidStateFnOff = sp - 0x70#64 := by bv_omega
  have e5 : sp - 0x70#64 + 8#64 = sp - 0x68#64 := by bv_omega
  rw [e1, e4]
  simp only [e2, e3, e5, sepExists_sepConj_left, sepExists_sepConj_right]
  apply sepProp_ext
  · refine Entails.sepExists_elim fun fnPtr => Entails.sepExists_elim fun bs =>
      Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
    refine Entails.sepExists_right bs (Entails.sepExists_right cap
      (Entails.sepExists_right ptr (Entails.sepExists_right fnPtr ?_)))
    exact Entails.of_eq (by ac_rfl)
  · refine Entails.sepExists_elim fun bs => Entails.sepExists_elim fun cap =>
      Entails.sepExists_elim fun ptr => Entails.sepExists_elim fun fnPtr => ?_
    refine Entails.sepExists_right fnPtr (Entails.sepExists_right bs
      (Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)))
    exact Entails.of_eq (by ac_rfl)


end CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
