/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.Deps
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode.Fetches
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode.Layout
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Verification of `IdentityKey::decode`

Proves `IdentityKey::decode` (`protocol/src/identity_key.rs:52–55`, frame `sub sp, sp, #0x60`)
against `identityKeyDecodeSpec` (any 4 KiB-aligned image base) and `identityKeyDecodePlacedSpec`
(`[LibsignalPlacement]`, Block `18`): delegates to `<PublicKey as TryFrom<&[u8]>>::try_from` into a
40-byte stack slot and repacks the result into a 48-byte `Result<IdentityKey, SignalProtocolError>`.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary.IdentityKeyDecode

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open ProofLib.ProgramReflection CryptoVerification PublicKeyTryFrom Helpers

attribute [local irreducible] Program.fetch Program.externAt?

set_option maxHeartbeats 1000000 in
/-- `IdentityKey::decode` meets `identityKeyDecodeSpec` at any 4 KiB-aligned image base, given
the in-image `PublicKey::try_from` contract. -/
theorem identityKeyDecode_ok_of_pkTryFrom {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hpk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkTryFromName) (pkTryFromCodeSpec img))
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr identityKeyDecodeName)
      (identityKeyDecodeSpec A img) := by
  let _ := hb
  apply subroutine_ok_inImage_of_subroutine_ok img
  have hcall := ikDec_pkTryFrom_call_ok hpk
  clear hpk
  simp only [pkTryFromCodeSpec, pkTryFromSpec, sepConj_assoc] at hcall
  code_fetches_from CryptoVerification.libsignalSessionCode ikDec img.base
    (Rust.withPanics ext)
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode")
    (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode")) 0 268
  dsimp only [tripleRatchetProgAtExt, identityKeyDecodeName, BitVec.ofNat_eq_ofNat] at hcall ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::identity_key::IdentityKey>::decode" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨bytesA, bytes, ret⟩ := x
  dsimp only at *
  subst h h_1
  rcases publicKey_deserialize_cases bytes with
    ⟨pk, hdes, hdec⟩ | ⟨hdes, hdec⟩ | ⟨t, hdes, hdec⟩ | ⟨n, hdes, hdec⟩
  · have hbs32 : pk.bytes.toList.length = 32 := by simp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
      exists_ikKeyChunks_of_length_32 hbs32
    rw [hdec, memRegion_48_ok_split (s0.readReg64 (Reg.gpr 8#5)),
        identityKeyResultAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 8#64),
        ikKeyChunks_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_ok_post s0.sp]
    wp_pull_exists
    wp_steps
    wp_apply
    rw [hdes, pkTryFrom_sp_88_ok s0.sp pk, hchunks (s0.sp - 87#64), ikKeyChunks_sp_87 s0.sp]
    simp only [sepConj_assoc]
    wp_steps
    rw [sevenLo_sp_87 s0.sp]
    wp_steps
    rw [sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    wp_steps
    rw [sp_88_repack s0.sp]
    wp_steps
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    rw [← sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_noKeyType_post A (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_nil_post s0.sp]
    wp_pull_exists
    wp_steps
    wp_apply
    rw [hdes, pkTryFrom_sp_88_nil s0.sp]
    wp_steps
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_badKeyType_post A (s0.readReg64 (Reg.gpr 8#5)) t]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badType_post s0.sp]
    wp_pull_exists
    wp_steps
    wp_apply
    rw [hdes, pkTryFrom_sp_88_badType s0.sp t]
    wp_steps
    try rw [zero_orr_zext8_mask]
    rw [pointsTo64_zext8_split (s0.readReg64 (Reg.gpr 8#5)) t]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badLen_post s0.sp]
    wp_pull_exists
    wp_steps
    wp_apply
    rw [hdes, pkTryFrom_sp_88_badLen s0.sp n]
    wp_steps
    try rw [mask_split_64]
    dsimp only [identityKeyResultAt, speAt]
    wp_done

/-! ## Relocatable Per-Block Proofs (`[LibsignalPlacement]`, Block `18`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

set_option maxHeartbeats 1000000 in
/-- Relocatable `IdentityKey::decode` (Block `18`) meets `identityKeyDecodePlacedSpec`, given the
relocatable `PublicKey::try_from` contract (Block `211`). -/
theorem identityKey_decode_placed_ok_of_pkTryFrom [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hpk : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedSpec) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedSpec A) := by
  have hcall := ikDec_pkTryFrom_placed_call_ok hpk
  clear hpk
  simp only [withLsCl, pkTryFromPlacedSpec, pkTryFromSpec, sepConj_assoc] at hcall
  simp only [identityKeyDecodePlacedSpec, withLsCodeLoaded, identityKeyDecodeRawSpec]
  wp_init x s0
  obtain ⟨bytesA, bytes, ret⟩ := x
  dsimp only at *
  subst h_1 h_2
  rcases publicKey_deserialize_cases bytes with
    ⟨pk, hdes, hdec⟩ | ⟨hdes, hdec⟩ | ⟨t, hdes, hdec⟩ | ⟨n, hdes, hdec⟩
  · have hbs32 : pk.bytes.toList.length = 32 := by simp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
      exists_ikKeyChunks_of_length_32 hbs32
    rw [hdec, memRegion_48_ok_split (s0.readReg64 (Reg.gpr 8#5)),
        identityKeyResultAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 8#64),
        ikKeyChunks_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_ok_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl h (mid := lsmpl.base 211); wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_ok s0.sp pk, hchunks (s0.sp - 87#64), ikKeyChunks_sp_87 s0.sp]
    simp only [sepConj_assoc]
    wp_steps
    rw [sevenLo_sp_87 s0.sp]
    wp_steps
    rw [sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    wp_steps
    rw [sp_88_repack s0.sp]
    wp_steps
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate16_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    try rw [truncate8_zeroExtend32]
    rw [← sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_noKeyType_post A (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_nil_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl h (mid := lsmpl.base 211); wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_nil s0.sp]
    wp_steps
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5)),
        spe_badKeyType_post A (s0.readReg64 (Reg.gpr 8#5)) t]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badType_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl h (mid := lsmpl.base 211); wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_badType s0.sp t]
    wp_steps
    try rw [zero_orr_zext8_mask]
    rw [pointsTo64_zext8_split (s0.readReg64 (Reg.gpr 8#5)) t]
    wp_done
  · rw [hdec, memRegion_48_err_split (s0.readReg64 (Reg.gpr 8#5))]
    nth_rw 1 [stackAt_ikDec_split s0.sp]
    rw [stackAt_ikDec_split s0.sp, memRegion_sp_88_badLen_post s0.sp]
    wp_pull_exists
    apply sepWP_seq_lscl h (mid := lsmpl.base 211); wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
    wp_apply
    rw [hdes, pkTryFrom_sp_88_badLen s0.sp n]
    wp_steps
    try rw [mask_split_64]
    dsimp only [identityKeyResultAt, speAt]
    wp_done

/-- Relocatable `IdentityKey::decode` (Block `18`) meets `identityKeyDecodePlacedSpec` for any hooks `H`. -/
theorem identityKey_decode_placed_ok [LibsignalPlacement] {A : RustAlloc} (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedSpec A) :=
  identityKey_decode_placed_ok_of_pkTryFrom (pkTryFrom_placed_ok H)

end Placed

end CryptoVerification.RecordCodecsBinary.IdentityKeyDecode

