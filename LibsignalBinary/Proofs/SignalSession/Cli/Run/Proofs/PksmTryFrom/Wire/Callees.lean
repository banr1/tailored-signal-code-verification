/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBase
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DropDecodeError
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.Fetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSlice
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.SepLogic.WPp

/-!
# Callee Contracts and `IdentityKey::try_from` Specifications for `PreKeySignalMessage::try_from`

Proves the `Ok` and `Err` specifications of `<IdentityKey as TryFrom<&[u8]>>::try_from`
(preserving exact `speAt` error payloads via `ikErrWords`) and packages all callee contracts
of `PreKeySignalMessage::try_from` into `PksmCallees` from image loading and allocator hooks.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire
open CryptoVerification.SignalSession.Cli.RunProofs

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Local kernel-checked BitVec normalizers -/

private theorem bv_sub_add_lit'X (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem bv_sub_sub_litX (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

private theorem bv_add_neg_8X (x : BitVec 64) : x + bv% (2 ^ 64 - 8) = x - 8#64 := by bv_omega
private theorem bv_add_neg_16X (x : BitVec 64) : x + bv% (2 ^ 64 - 16) = x - 16#64 := by bv_omega
private theorem bv_add_neg_24X (x : BitVec 64) : x + bv% (2 ^ 64 - 24) = x - 24#64 := by bv_omega
private theorem bv_add_neg_32X (x : BitVec 64) : x + bv% (2 ^ 64 - 32) = x - 32#64 := by bv_omega
private theorem bv_add_neg_40X (x : BitVec 64) : x + bv% (2 ^ 64 - 40) = x - 40#64 := by bv_omega
private theorem bv_add_neg_48X (x : BitVec 64) : x + bv% (2 ^ 64 - 48) = x - 48#64 := by bv_omega
private theorem bv_add_neg_55X (x : BitVec 64) : x + bv% (2 ^ 64 - 55) = x - 55#64 := by bv_omega
private theorem bv_add_neg_56X (x : BitVec 64) : x + bv% (2 ^ 64 - 56) = x - 56#64 := by bv_omega
private theorem bv_add_neg_64X (x : BitVec 64) : x + bv% (2 ^ 64 - 64) = x - 64#64 := by bv_omega
private theorem bv_add_neg_72X (x : BitVec 64) : x + bv% (2 ^ 64 - 72) = x - 72#64 := by bv_omega
private theorem bv_add_neg_80X (x : BitVec 64) : x + bv% (2 ^ 64 - 80) = x - 80#64 := by bv_omega
private theorem bv_add_neg_87X (x : BitVec 64) : x + bv% (2 ^ 64 - 87) = x - 87#64 := by bv_omega
private theorem bv_add_neg_88X (x : BitVec 64) : x + bv% (2 ^ 64 - 88) = x - 88#64 := by bv_omega
private theorem bv_add_neg_96X (x : BitVec 64) : x + bv% (2 ^ 64 - 96) = x - 96#64 := by bv_omega
private theorem bv_add_neg_104X (x : BitVec 64) : x + bv% (2 ^ 64 - 104) = x - 104#64 := by bv_omega
private theorem bv_add_neg_112X (x : BitVec 64) : x + bv% (2 ^ 64 - 112) = x - 112#64 := by bv_omega
private theorem bv_add_neg_128X (x : BitVec 64) : x + bv% (2 ^ 64 - 128) = x - 128#64 := by bv_omega
private theorem bv_add_neg_136X (x : BitVec 64) : x + bv% (2 ^ 64 - 136) = x - 136#64 := by bv_omega
private theorem bv_add_neg_152X (x : BitVec 64) : x + bv% (2 ^ 64 - 152) = x - 152#64 := by bv_omega
private theorem bv_add_neg_160X (x : BitVec 64) : x + bv% (2 ^ 64 - 160) = x - 160#64 := by bv_omega
private theorem bv_add_neg_168X (x : BitVec 64) : x + bv% (2 ^ 64 - 168) = x - 168#64 := by bv_omega
private theorem bv_add_neg_176X (x : BitVec 64) : x + bv% (2 ^ 64 - 176) = x - 176#64 := by bv_omega
private theorem bv_add_neg_184X (x : BitVec 64) : x + bv% (2 ^ 64 - 184) = x - 184#64 := by bv_omega
private theorem bv_add_neg_186X (x : BitVec 64) : x + bv% (2 ^ 64 - 186) = x - 186#64 := by bv_omega
private theorem bv_add_neg_191X (x : BitVec 64) : x + bv% (2 ^ 64 - 191) = x - 191#64 := by bv_omega
private theorem bv_add_neg_192X (x : BitVec 64) : x + bv% (2 ^ 64 - 192) = x - 192#64 := by bv_omega
private theorem bv_add_neg_196X (x : BitVec 64) : x + bv% (2 ^ 64 - 196) = x - 196#64 := by bv_omega
private theorem bv_add_neg_200X (x : BitVec 64) : x + bv% (2 ^ 64 - 200) = x - 200#64 := by bv_omega
private theorem bv_add_neg_216X (x : BitVec 64) : x + bv% (2 ^ 64 - 216) = x - 216#64 := by bv_omega
private theorem bv_add_neg_512X (x : BitVec 64) : x + bv% (2 ^ 64 - 512) = x - 512#64 := by bv_omega

private theorem extract8_mask32_0X (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = a := by
  bv_slice
private theorem extract8_mask32_8X (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = b := by
  bv_slice
private theorem extract8_mask32_16X (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = c := by
  bv_slice
private theorem extract8_mask32_24X (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = d := by
  bv_slice
private theorem extract8_mask32_32X (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 32 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 32 8 w := by bv_bits
private theorem extract8_mask32_40X (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 40 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 40 8 w := by bv_bits
private theorem extract8_mask32_48X (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 48 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 48 8 w := by bv_bits
private theorem extract8_mask32_56X (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 56 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 56 8 w := by bv_bits

private theorem extract8_concat8_0X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 0 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b0 := by bv_slice
private theorem extract8_concat8_8X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 8 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b1 := by bv_slice
private theorem extract8_concat8_16X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 16 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b2 := by bv_slice
private theorem extract8_concat8_24X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 24 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b3 := by bv_slice
private theorem extract8_concat8_32X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 32 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b4 := by bv_slice
private theorem extract8_concat8_40X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 40 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b5 := by bv_slice
private theorem extract8_concat8_48X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 48 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b6 := by bv_slice
private theorem extract8_concat8_56X (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 56 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b7 := by bv_slice

private theorem pointsTo64_eq_extract_bytes8X (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦₈ w.extractLsb' 0 8) ∗ ((a + 1#64) ↦₈ w.extractLsb' 8 8) ∗
      ((a + 2#64) ↦₈ w.extractLsb' 16 8) ∗ ((a + 3#64) ↦₈ w.extractLsb' 24 8) ∗
      ((a + 4#64) ↦₈ w.extractLsb' 32 8) ∗ ((a + 5#64) ↦₈ w.extractLsb' 40 8) ∗
      ((a + 6#64) ↦₈ w.extractLsb' 48 8) ∗ ((a + 7#64) ↦₈ w.extractLsb' 56 8) := by
  have hw : w = w.extractLsb' 56 8 ++ w.extractLsb' 48 8 ++ w.extractLsb' 40 8 ++
      w.extractLsb' 32 8 ++ w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++
      w.extractLsb' 8 8 ++ w.extractLsb' 0 8 := by bv_bits
  conv => lhs; rw [hw]
  exact pointsTo64_eq_bytes8 a _ _ _ _ _ _ _ _

attribute [local arm64_norm, local wp_norm]
  extract8_mask32_0X extract8_mask32_8X extract8_mask32_16X extract8_mask32_24X
  extract8_mask32_32X extract8_mask32_40X extract8_mask32_48X extract8_mask32_56X
  extract8_concat8_0X extract8_concat8_8X extract8_concat8_16X extract8_concat8_24X
  extract8_concat8_32X extract8_concat8_40X extract8_concat8_48X extract8_concat8_56X
  bv_sub_add_lit'X bv_sub_sub_litX
  bv_add_neg_8X bv_add_neg_16X bv_add_neg_24X bv_add_neg_32X bv_add_neg_40X
  bv_add_neg_48X bv_add_neg_55X bv_add_neg_56X bv_add_neg_64X bv_add_neg_72X
  bv_add_neg_80X bv_add_neg_87X bv_add_neg_88X bv_add_neg_96X bv_add_neg_104X
  bv_add_neg_112X bv_add_neg_128X bv_add_neg_136X bv_add_neg_152X bv_add_neg_160X
  bv_add_neg_168X bv_add_neg_176X bv_add_neg_184X bv_add_neg_186X bv_add_neg_191X
  bv_add_neg_192X bv_add_neg_196X bv_add_neg_200X bv_add_neg_216X bv_add_neg_512X
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue.append64_extract_lo
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue.append64_extract_hi

/-! ## Section 1: `<IdentityKey as TryFrom<&[u8]>>::try_from` Ok & Err Specs and Proofs -/

private theorem cells_12_identityKey_pre (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      memRegion (sp - 48#64) 8 ∗
      memRegion (sp - 40#64) 8 ∗
      (∃∗ w_32 : BitVec 64, (sp - 32#64) ↦₆₄ w_32) ∗
      (∃∗ w_24 : BitVec 64, (sp - 24#64) ↦₆₄ w_24) ∗
      (∃∗ w_16 : BitVec 64, (sp - 16#64) ↦₆₄ w_16) ∗
      memRegion (sp - 8#64) 8 := by
  rw [← ProofLib.memRegion_cells (sp - 96#64) 12 (by decide),
    Prost.memRegion_split (sp - 96#64) 8 88 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64) 40 48 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64) 8 40 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64) 8 32 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split (sp - 96#64 + 8#64 + 40#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]
  rw [ProofLib.memRegion_eight (sp - 32#64),
      ProofLib.memRegion_eight (sp - 24#64),
      ProofLib.memRegion_eight (sp - 16#64)]

private theorem memRegion_40_identityKey_post (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗
      memRegion_8_bytes_mr_rhs (sp - 87#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 79#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 71#64) ∗
      memRegion_8_bytes_mr_rhs (sp - 63#64) ∗
      memRegion (sp - 55#64) 7 := by
  rw [Prost.memRegion_split (sp - 88#64) 1 39 (by decide),
    Prost.memRegion_split (sp - 88#64 + 1#64) 8 31 (by decide),
    Prost.memRegion_split (sp - 88#64 + 1#64 + 8#64) 8 23 (by decide),
    Prost.memRegion_split (sp - 88#64 + 1#64 + 8#64 + 8#64) 8 15 (by decide),
    Prost.memRegion_split (sp - 88#64 + 1#64 + 8#64 + 8#64 + 8#64) 8 7 (by decide)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]
  rw [memRegion_8_bytes_mr (sp - 87#64),
      memRegion_8_bytes_mr (sp - 79#64),
      memRegion_8_bytes_mr (sp - 71#64),
      memRegion_8_bytes_mr (sp - 63#64)]

def pkTryFromOk40SpecX (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × PublicKey × BitVec 64) where
  pre := fun (p, bs, pk, out) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = out ∧ PublicKey.deserialize bs = .ok pk⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out 40 ∗ logOff img
  post := fun (p, bs, pk, out) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ pk.bytes.toList) ∗
      memRegion (out + 33#64) 7 ∗ logOff img

theorem pkTryFromOk40_ok_atX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName +
        BitVec.ofNat 64 (num% (ls_off% pkTryFromName - ls_off% identityKeyTryFromSliceName)))
      (pkTryFromOk40SpecX img) := by
  have hk : libsignalSessionCode.fnOff identityKeyTryFromSliceName +
      (num% (ls_off% pkTryFromName - ls_off% identityKeyTryFromSliceName)) =
      libsignalSessionCode.fnOff pkTryFromName := by
    rw [(ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from"),
        (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")]
  refine subroutine_ok_map
    (pk_try_from_ok_at_ext img ext himg identityKeyTryFromSliceName
      (num% (ls_off% pkTryFromName - ls_off% identityKeyTryFromSliceName)) hk) ?_
  rintro ⟨p, bs, pk, out⟩ R s0 hpre
  simp only [pkTryFromOk40SpecX, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, out), R, ?_, fun sf hpost => ?_⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  · simp only [pkTryFromCodeSpec, pkTryFromSpec, hdes, pkTryFromResultAt,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [pkTryFromOk40SpecX, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hpost⟩

set_option maxHeartbeats 3200000 in
theorem identityKeyTryFromSlice_okX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceOkSpec img) := by
  unfold identityKeyTryFromSliceOkSpec
  have hpk := pkTryFromOk40_ok_atX (ext := ext) himg
  simp only [pkTryFromOk40SpecX] at hpk
  have hfn : libsignalSessionCode.fnOff identityKeyTryFromSliceName =
      num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.ResponderWire.responderWireBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")) 264
  clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpk ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr identityKeyTryFromSliceName = entry
  wp_init x s0
  examples_hide_fetches
  rcases x with ⟨p, bs, pk, outPtr⟩
  dsimp only at *
  subst h_1 h_3
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk_bytes⟩ := exists_bytes32_of_vector32 pk.bytes
  have hstk_eq : stackAt s0.sp 96 = cells (s0.sp - 96#64) 12 := by
    simp only [stackAt]
    exact ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)
  rw [hstk_eq]
  rw (occs := .pos [1]) [cells_12_identityKey_pre s0.sp]
  wp_pull_exists
  wp_steps
  wp_call hpk (s0.readReg64 (.gpr 0#5), bs, pk, s0.sp - 88#64)
  rw [memRegion_40_words (s0.readReg64 (.gpr 8#5)),
      memRegion_8_bytes (s0.sp - 48#64),
      memRegion_8_bytes (s0.sp - 40#64),
      memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]
  wp_pull_exists
  rw [hpk_bytes (s0.sp - 87#64),
      hpk_bytes (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8X (s0.readReg64 (.gpr 8#5) + 8#64),
      pointsTo64_eq_extract_bytes8X (s0.readReg64 (.gpr 8#5) + 16#64),
      pointsTo64_eq_extract_bytes8X (s0.readReg64 (.gpr 8#5) + 24#64),
      pointsTo64_eq_extract_bytes8X (s0.readReg64 (.gpr 8#5) + 32#64),
      cells_12_identityKey_pre s0.sp,
      memRegion_40_identityKey_post s0.sp,
      memRegion_8_bytes_mr (s0.sp - 48#64),
      memRegion_8_bytes_mr (s0.sp - 40#64),
      memRegion_8_bytes_mr (s0.sp - 8#64)]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit'X, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

/-! ### `IdentityKey::try_from` Err half (`ikErrWords` + exact `speAt` bridge) -/

/-- The `(tag, payload)` words `<IdentityKey as TryFrom<&[u8]>>::try_from` stores via
`stp x8, x9, [x19]` at `out`, `out + 8` on the `Err` arms of `PublicKey::try_from`:
`x8 = speWord 7 / 8 / 9 / 10` for discriminants `0 / 1 / 2 / ≥ 3`, and `x9 = 7` / byte / usize. -/
def ikErrWords : SignalProtocolError → BitVec 64 × BitVec 64
  | .noKeyTypeIdentifier => (speWord 7, 7#64)
  | .badKeyType t => (speWord 8, t.zeroExtend 64)
  | .badKeyLength n => (speWord 9, BitVec.ofNat 64 n)
  | .invalidKeyAgreement => (speWord 10, 0#64)
  | _ => (0#64, 0#64)

theorem ikErrWords_fst_ne (e : SignalProtocolError) :
    (ikErrWords e).1 ≠ 0xfffffffffffffffe#64 := by
  unfold ikErrWords; split <;> simp [speWord]

/-- `PublicKey::deserialize` fails with one of the three public-key decode errors. -/
theorem deserialize_error_cases {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : PublicKey.deserialize bs = .error e) :
    e = .noKeyTypeIdentifier ∨ (∃ t, e = .badKeyType t) ∨ ∃ n, e = .badKeyLength n := by
  unfold PublicKey.deserialize at h
  split at h
  · cases h; exact Or.inl rfl
  · split at h
    · cases h; exact Or.inr (Or.inl ⟨_, rfl⟩)
    · split at h
      · cases h
      · cases h; exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- Word-level Err specification of `<IdentityKey as TryFrom<&[u8]>>::try_from` on 40-byte sret
(`memRegion outPtr 40`): writes `ikErrWords e` at `outPtr`, `outPtr + 8`, leaving `outPtr + 16 .. 40`
untouched (`memRegion (outPtr + 16) 24`). -/
def identityKeyTryFromSliceWordsErrSpec (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × SignalProtocolError × BitVec 64) where
  pre := fun (p, bs, e, outPtr) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = outPtr ∧ PublicKey.deserialize bs = .error e⌝ ∗
      (p ↦ₛ bs) ∗ memRegion outPtr 40 ∗ logOff img ∗
      stackAt s.sp 96
  post := fun (p, bs, e, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      (outPtr ↦₆₄ (ikErrWords e).1) ∗ ((outPtr + 8#64) ↦₆₄ (ikErrWords e).2) ∗
      memRegion (outPtr + 16#64) 24 ∗
      logOff img ∗
      stackAt s0.sp 96

private theorem ik_low8_merge (n : BitVec 64) :
    n &&& (-256#64) ||| n &&& 255#64 = n := by
  rw [← BitVec.and_or_distrib_left, show (-256#64 ||| 255#64) = BitVec.allOnes 64 by decide,
    BitVec.and_allOnes]

private theorem memRegion_40_stp (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      memRegion (a + 16#64) 24 := by
  rw [ProofLib.memRegion_split a 8 32 (by decide), ProofLib.memRegion_split (a + 8#64) 8 24 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_40_ikErr_small (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗ memRegion (sp - 87#64) 7 ∗ memRegion (sp - 80#64) 1 ∗
      memRegion (sp - 79#64) 1 ∗ memRegion (sp - 78#64) 30 := by
  rw [ProofLib.memRegion_split (sp - 88#64) 1 39 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64) 7 32 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64) 1 31 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64) 1 30 (by decide)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]

private theorem memRegion_40_ikErr_len (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      memRegion (sp - 88#64) 1 ∗ memRegion (sp - 87#64) 7 ∗ memRegion (sp - 80#64) 1 ∗
      memRegion (sp - 79#64) 7 ∗ (∃∗ w : BitVec 64, (sp - 72#64) ↦₆₄ w) ∗
      memRegion (sp - 64#64) 16 := by
  rw [ProofLib.memRegion_split (sp - 88#64) 1 39 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64) 7 32 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64) 1 31 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64) 7 24 (by decide),
    ProofLib.memRegion_split (sp - 88#64 + 1#64 + 7#64 + 1#64 + 7#64) 8 16 (by decide)]
  simp only [bv_sub_add_lit'X, BitVec.reduceSub]
  rw [ProofLib.memRegion_eight (sp - 72#64)]

private theorem memRegion_31_byte (a : BitVec 64) :
    memRegion a 31 = (∃∗ v : BitVec 8, a ↦₈ v) ∗ memRegion (a + 1#64) 30 := by
  rw [ProofLib.memRegion_split a 1 30 (by decide), ProofLib.memRegion_one]

set_option maxHeartbeats 3200000 in
theorem identityKeyTryFromSlice_wordsErrX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceWordsErrSpec img) := by
  unfold identityKeyTryFromSliceWordsErrSpec
  have hpk := pk_try_from_ok_at_ext img ext himg identityKeyTryFromSliceName
    (num% (ls_off% pkTryFromName - ls_off% identityKeyTryFromSliceName))
    (by
      rw [(ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from"),
          (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")])
  simp only [pkTryFromCodeSpec, pkTryFromSpec] at hpk
  have hfn : libsignalSessionCode.fnOff identityKeyTryFromSliceName =
      num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from") :=
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.ResponderWire.responderWireBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")) 264
  clear hfn
  dsimp only [contractProg, tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hpk ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr identityKeyTryFromSliceName = entry
  wp_init x s0
  examples_hide_fetches
  rcases x with ⟨p, bs, e, outPtr⟩
  dsimp only at *
  subst h_1 h_3
  have hstk_eq : stackAt s0.sp 96 = cells (s0.sp - 96#64) 12 := by
    simp only [stackAt]
    exact ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide)
  rw [hstk_eq]
  rw (occs := .pos [1]) [cells_12_identityKey_pre s0.sp]
  rw (occs := .pos [1]) [memRegion_40_stp (s0.readReg64 (.gpr 8#5))]
  wp_pull_exists
  wp_steps
  wp_call hpk (s0.readReg64 (.gpr 0#5), bs, s0.sp - 88#64)
  rw [h]
  rcases deserialize_error_cases h with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · simp only [pkTryFromResultAt, ikErrWords, speWord, bv_sub_add_lit'X, BitVec.reduceSub]
    rw [memRegion_31_byte (s0.sp - 79#64)]
    simp only [bv_sub_add_lit'X, BitVec.reduceSub]
    rw [cells_12_identityKey_pre s0.sp, memRegion_40_ikErr_small s0.sp]
    wp_pull_exists
    wp_steps
    wp_done
  · simp only [pkTryFromResultAt, ikErrWords, speWord, bv_sub_add_lit'X, BitVec.reduceSub]
    rw [cells_12_identityKey_pre s0.sp, memRegion_40_ikErr_small s0.sp]
    wp_pull_exists
    wp_steps
    wp_done
  · simp only [pkTryFromResultAt, ikErrWords, speWord, bv_sub_add_lit'X, BitVec.reduceSub]
    rw [cells_12_identityKey_pre s0.sp, memRegion_40_ikErr_len s0.sp]
    wp_pull_exists
    wp_steps
    simp only [ik_low8_merge]
    wp_done

/-- The two words stored by `stp x8, x9, [a]` plus a
32-byte trailing region (`a + 16 .. a + 48`) entail `speAt A fn a e` for every error `e` of
`PublicKey.deserialize`. -/
theorem ikErrWords_entails_speAt {bs : List (BitVec 8)} {e : SignalProtocolError}
    (h : PublicKey.deserialize bs = .error e)
    (A : RustAlloc) (fn : List (BitVec 8)) (a : BitVec 64) :
    (a ↦₆₄ (ikErrWords e).1) ∗ ((a + 8#64) ↦₆₄ (ikErrWords e).2) ∗
      memRegion (a + 16#64) 32 ⊢
    speAt A fn a e := by
  rcases deserialize_error_cases h with rfl | ⟨t, rfl⟩ | ⟨n, rfl⟩
  · simp only [ikErrWords, speAt]
    rw [show memRegion (a + asm64% spePayloadOff) (asm% (speSize - spePayloadOff)) =
        memRegion (a + 8#64) 8 ∗ memRegion (a + 16#64) 32 by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using
        ProofLib.memRegion_split (a + 8#64) 8 32 (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (a + 8#64) 7#64))
  · simp only [ikErrWords, speAt]
    have hb0 : ((t.zeroExtend 64).extractLsb' 0 8) = t := by bv_bits
    have hzext : ((a + 8#64) ↦₆₄ t.zeroExtend 64) ⊢
        ((a + 8#64) ↦₈ t) ∗ memRegion (a + 9#64) 7 := by
      rw [pointsTo64_eq_pointsToBytes]
      change ((a + 8#64) ↦ₛ ((t.zeroExtend 64).extractLsb' 0 8 ::
        [(t.zeroExtend 64).extractLsb' 8 8, (t.zeroExtend 64).extractLsb' 16 8,
         (t.zeroExtend 64).extractLsb' 24 8, (t.zeroExtend 64).extractLsb' 32 8,
         (t.zeroExtend 64).extractLsb' 40 8, (t.zeroExtend 64).extractLsb' 48 8,
         (t.zeroExtend 64).extractLsb' 56 8])) ⊢ _
      rw [hb0, pointsToBytes_cons, show a + 8#64 + 1#64 = a + 9#64 by bv_omega]
      exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)
    rw [show memRegion (a + asm64% (spePayloadOff + 1)) (asm% (speSize - (spePayloadOff + 1))) =
        memRegion (a + 9#64) 7 ∗ memRegion (a + 16#64) 32 by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using
        ProofLib.memRegion_split (a + 9#64) 7 32 (by decide)]
    refine sepConj_mono_right ?_
    rw [← sepConj_assoc]
    exact Entails.trans (sepConj_mono_left hzext) (by apply entails_of_eq; ac_rfl)
  · simp only [ikErrWords, speAt]
    exact Entails.refl _

/-- Exact `speAt` Err specification of `<IdentityKey as TryFrom<&[u8]>>::try_from` on a 48-byte
sret (`memRegion outPtr 48`): produces exact `speAt A fn outPtr e`. -/
def identityKeyTryFromSliceErrSpec (A : RustAlloc) (fn : List (BitVec 8)) (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × SignalProtocolError × BitVec 64) where
  pre := fun (p, bs, e, outPtr) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = outPtr ∧ PublicKey.deserialize bs = .error e⌝ ∗
      (p ↦ₛ bs) ∗ memRegion outPtr 48 ∗ logOff img ∗
      stackAt s.sp 96
  post := fun (p, bs, e, outPtr) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗
      speAt A fn outPtr e ∗
      logOff img ∗
      stackAt s0.sp 96

theorem identityKeyTryFromSlice_errX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (A : RustAlloc) (fn : List (BitVec 8))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceErrSpec A fn img) := by
  refine subroutine_ok_map (identityKeyTryFromSlice_wordsErrX (ext := ext) himg) ?_
  rintro ⟨p, bs, e, outPtr⟩ R s0 hpre
  have h48 : memRegion outPtr 48 = memRegion outPtr 40 ∗ memRegion (outPtr + 40#64) 8 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      ProofLib.memRegion_split outPtr 40 8 (by decide)
  simp only [identityKeyTryFromSliceErrSpec, h48, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hdes⟩, hmem⟩
  refine ⟨(p, bs, e, outPtr), memRegion (outPtr + 40#64) 8 ∗ R, ?_, fun sf hpost => ?_⟩
  · simp only [identityKeyTryFromSliceWordsErrSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8, hdes⟩, ?_⟩
    ac_nf at hmem ⊢
  · simp only [identityKeyTryFromSliceWordsErrSpec, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [identityKeyTryFromSliceErrSpec, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    have h32 : memRegion (outPtr + 16#64) 24 ∗ memRegion (outPtr + 40#64) 8 =
        memRegion (outPtr + 16#64) 32 := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using
        (ProofLib.memRegion_split (outPtr + 16#64) 24 8 (by decide)).symm
    have hreg : sf.mem ⊨
        ((outPtr ↦₆₄ (ikErrWords e).1) ∗ ((outPtr + 8#64) ↦₆₄ (ikErrWords e).2) ∗
          (memRegion (outPtr + 16#64) 24 ∗ memRegion (outPtr + 40#64) 8)) ∗
          ((p ↦ₛ bs) ∗ logOff img ∗ stackAt s0.sp 96 ∗ R) := by
      ac_nf at hpost ⊢
    rw [h32] at hreg
    have hspe := Satisfies.mono (sepConj_mono_left (ikErrWords_entails_speAt hdes A fn outPtr)) hreg
    ac_nf at hspe ⊢

/-! ## Section 2: Callee Offset Wrappers from `preKeyTryFromName` -/

theorem int32Merge_ok_at_prekey_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : Int32MergeOkExt b A ext) :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% int32MergeName - ls_off% preKeyTryFromName) % 2 ^ 64))
      (int32MergeSpec A) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")
    (by decide)]
  exact h

theorem int32Merge_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : Int32MergeOkExtX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% int32MergeName - ls_off% preKeyTryFromName) % 2 ^ 64))
      ((int32MergeSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")
    (by decide)]
  exact h

theorem bytesMerge_ok_at_prekey_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : BytesMergeOkExt img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% bytesMergeName - ls_off% preKeyTryFromName) % 2 ^ 64))
      (bytesMergeSpec A img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")
    (by decide)]
  exact h

theorem bytesMerge_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : BytesMergeOkExtX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% bytesMergeName - ls_off% preKeyTryFromName) % 2 ^ 64))
      (bytesMergeSpecX A img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")
    (by decide)]
  exact h

theorem dropSpe_ok_at_prekey_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropSpeOkExt img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% dropSpeName - ls_off% preKeyTryFromName) % 2 ^ 64))
      ((dropSpeSpec A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")
    (by decide)]
  exact h

theorem dropSpe_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : DropSpeOkX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% dropSpeName - ls_off% preKeyTryFromName) % 2 ^ 64))
      ((dropSpeSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]")
    (by decide)]
  exact h

theorem deserializeFull_ok_at_contractProg {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {off k : Nat}
    (hfn : libsignalSessionCode.fnOff name = off)
    (hk : off + k = num% (ls_off% deserializeName)) :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr name + BitVec.ofNat 64 k)
      (deserializeFullSpec b) := by
  rw [← Program.fnAddr_rel hfn
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey>::deserialize") hk]
  exact deserializeFull_ok b (Rust.withPanics ext)

def IntoBoxedSliceOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg b ext)
    ((contractProg b ext).fnAddr intoBoxedSliceName)
    (intoBoxedSliceSpec A)

def IntoBoxedSliceOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr intoBoxedSliceName)
    ((intoBoxedSliceSpecX A).inImage img)

def TryCloneFromRefOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg b ext)
    ((contractProg b ext).fnAddr tryCloneFromRefName)
    (tryCloneFromRefSpec A)

def TryCloneFromRefOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext)
    ((contractProg img.base ext).fnAddr tryCloneFromRefName)
    ((tryCloneFromRefSpecX A).inImage img)

theorem panic_at_handle_alloc_error2_ext {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff "alloc::alloc::handle_alloc_error" := by simp only [arm64_norm]) :
    (contractProg b ext).externAt?
      ((contractProg b ext).fnAddr name + BitVec.ofNat 64 k) =
      some Rust.panicked :=
  panic_at_handle_alloc_error_ext b ext name k hk

theorem deserialize_ok_at_prekeyX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% deserializeName - ls_off% preKeyTryFromName))
      (deserializeOk33Spec img) := by
  have hfull := deserializeFull_ok_at_contractProg (b := img.base) (ext := ext)
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (k := num% (ls_off% deserializeName - ls_off% preKeyTryFromName)) (by decide)
  refine subroutine_ok_map hfull ?_
  rintro ⟨ptr, bs, pk, sret⟩ R s0 hpre
  simp only [deserializeOk33Spec, logOff, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hlen, hdes⟩, hmem⟩
  refine ⟨(ptr, bs, sret), R, ?_, fun sf hpost => ?_⟩
  · simp only [deserializeFullSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8, hlen, ProofLib.ObjectLoad.base_aligned_of_loads himg⟩, hmem⟩
  · simp only [deserializeFullSpec, hdes, deserializeResult33At,
      sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨htr, hpost⟩
    simp only [deserializeOk33Spec, logOff, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htr, hpost⟩

theorem intoBoxedSlice_ok_at_prekey_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : IntoBoxedSliceOkExt b A ext) :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% intoBoxedSliceName - ls_off% preKeyTryFromName) % 2 ^ 64))
      (intoBoxedSliceSpec A) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "<alloc::vec::Vec<u8>>::into_boxed_slice")
    (by decide)]
  exact h

theorem intoBoxedSlice_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : IntoBoxedSliceOkX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% intoBoxedSliceName - ls_off% preKeyTryFromName) % 2 ^ 64))
      ((intoBoxedSliceSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "<alloc::vec::Vec<u8>>::into_boxed_slice")
    (by decide)]
  exact h

theorem identityKeyTryFrom_ok_at_prekeyX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% identityKeyTryFromSliceName - ls_off% preKeyTryFromName))
      (identityKeyTryFromSliceOkSpec img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")
    (by decide)]
  exact identityKeyTryFromSlice_okX himg

theorem identityKeyTryFrom_wordsErr_at_prekeyX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% identityKeyTryFromSliceName - ls_off% preKeyTryFromName))
      (identityKeyTryFromSliceWordsErrSpec img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")
    (by decide)]
  exact identityKeyTryFromSlice_wordsErrX himg

theorem identityKeyTryFrom_err_at_prekeyX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (A : RustAlloc) (fn : List (BitVec 8))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% identityKeyTryFromSliceName - ls_off% preKeyTryFromName))
      (identityKeyTryFromSliceErrSpec A fn img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey as core::convert::TryFrom<&[u8]>>::try_from")
    (by decide)]
  exact identityKeyTryFromSlice_errX A fn himg

theorem signalTryFrom_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr tryFromName) (tryFromSpec A img)) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% tryFromName - ls_off% preKeyTryFromName) % 2 ^ 64))
      (tryFromSpec A img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "<libsignal_protocol::protocol::SignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (by decide)]
  exact h

theorem tryCloneFromRef_ok_at_prekey_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : TryCloneFromRefOkExt b A ext) :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% tryCloneFromRefName - ls_off% preKeyTryFromName) % 2 ^ 64))
      (tryCloneFromRefSpec A) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")
    (by decide)]
  exact h

theorem tryCloneFromRef_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : TryCloneFromRefOkX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% ((2 ^ 64 + ls_off% tryCloneFromRefName - ls_off% preKeyTryFromName) % 2 ^ 64))
      ((tryCloneFromRefSpecX A).inImage img) := by
  rw [fnAddr_sub_rel
    (ls_lemma% fnOff "<libsignal_protocol::protocol::PreKeySignalMessage as core::convert::TryFrom<&[u8]>>::try_from")
    (ls_lemma% fnOff "<alloc::boxed::Box<[u8]>>::try_clone_from_ref_in")
    (by decide)]
  exact h

theorem dealloc_ok_at_prekey_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (contractProg b ext)
      ((contractProg b ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName))
      (rustDeallocSpec A) :=
  dealloc_ok_at_norm_ext hA (name := preKeyTryFromName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName))

theorem dealloc_ok_at_prekeyX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsX img A ext) :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img) :=
  dealloc_ok_at_norm_ext_x hA (name := preKeyTryFromName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% preKeyTryFromName))

theorem panic_at_prekey_handle_alloc_errorX {b : BitVec 64}
    {ext : String → Option (State → State)} :
    (contractProg b ext).externAt?
      ((contractProg b ext).fnAddr preKeyTryFromName +
        bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% preKeyTryFromName)) =
      some Rust.panicked :=
  panic_at_handle_alloc_error2_ext (name := preKeyTryFromName)
    (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% preKeyTryFromName))

/-! ## Section 3: Native Closed Callee Bundle `PksmCallees` & `pksmCallees_of_loads` -/

private def pksmDummyCrypto : Crypto where
  F := fun s _ => s
  E := fun _ b => b
  D := fun _ b => b
  X := fun _ pk => pk
  pubKey := fun sk => sk

private def pksmDummySpqr : SpqrModel :=
  ⟨fun _ _ => none, fun _ _ => 0, fun _ _ => .error false, fun _ _ => False, fun _ _ => False⟩

/-- All callee contracts used by `PreKeySignalMessage::try_from`, discharged natively in
`LibsignalBinary` from `(himg : Obj.Loads libsignalSessionImage img)` and
`(hA : AllocContractsX img A ext)` via `RunProofs.cliTryFromHooksW_ok`, `cliTryFromDeps_ok`,
and `cliSigTryFrom_ok`. -/
structure PksmCallees (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : AllocHooksW img A ext
  decodeErrorFrom :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img)
  decodeErrorPush :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img)
  decodeVarintSlow :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr varintSlowName)
      ((decodeVarintSlowSpecWithStack A (64 + 2 * extHookStack)).inImage img)
  varintSlice : Prost.DecodeVarintSliceOkExtX img A ext
  int32Merge : Prost.Int32MergeOkExtX img A ext
  skipField : Prost.SkipFieldOkExtX img A ext
  bytesMerge : Prost.BytesMergeOkExtX img A ext
  dropDecodeError : Prost.DropDecodeErrorOkExtX img A ext
  dropSpe : DropSpeOkX img A ext
  intoBoxed : IntoBoxedSliceOkX img A ext
  tryClone : TryCloneFromRefOkX img A ext
  sigTryFrom :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr tryFromName)
      (tryFromSpec A img)
  hooks : ∀ (C : Crypto) (S : SpqrModel), TripleRatchetHooksW img C A S ext
  deps : ∀ (C : Crypto) (ctl : BitVec 64), TryFromDeps img C A ctl ext
  identityKeyOk :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceOkSpec img)
  identityKeyErr :
    ∀ (f : List (BitVec 8)),
      subroutine_ok (contractProg img.base ext)
        ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
        (identityKeyTryFromSliceErrSpec A f img)
  identityKeyWordsErr :
    subroutine_ok (contractProg img.base ext)
      ((contractProg img.base ext).fnAddr identityKeyTryFromSliceName)
      (identityKeyTryFromSliceWordsErrSpec img)
  baseAligned : img.base &&& 4095#64 = 0#64

/-- Discharges every callee contract of `PreKeySignalMessage::try_from` natively from image
loading `himg` and allocator contracts `hA`. -/
theorem pksmCallees_of_loads {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContractsX img A ext) :
    PksmCallees img A ext := by
  have hh0 := cliTryFromHooksW_ok pksmDummyCrypto pksmDummySpqr himg hA
  have hd0 := cliTryFromDeps_ok pksmDummyCrypto 0#64 himg hA
  exact
    { alloc := hh0.alloc
      decodeErrorFrom := hh0.decodeErrorFrom
      decodeErrorPush := hh0.decodeErrorPush
      decodeVarintSlow := hh0.decodeVarintSlow
      varintSlice := hd0.varintSlice
      int32Merge := hd0.int32Merge
      skipField := hd0.skipField
      bytesMerge := hd0.bytesMerge
      dropDecodeError := hd0.dropDecodeError
      dropSpe := hd0.dropSpe
      intoBoxed := into_boxed_slice_ok_ext_x hA
      tryClone := try_clone_from_ref_ok_ext_x hA
      sigTryFrom := cliSigTryFrom_ok pksmDummyCrypto himg hA
      hooks := fun C S => cliTryFromHooksW_ok C S himg hA
      deps := fun C ctl => cliTryFromDeps_ok C ctl himg hA
      identityKeyOk := identityKeyTryFromSlice_okX himg
      identityKeyErr := fun f => identityKeyTryFromSlice_errX A f himg
      identityKeyWordsErr := identityKeyTryFromSlice_wordsErrX himg
      baseAligned := ProofLib.ObjectLoad.base_aligned_of_loads himg }

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

