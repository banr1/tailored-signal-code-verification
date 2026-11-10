/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Epilogue
import LibsignalBinary.Proofs.RecordCodecs.DecodeKyberPreKey.Fetches
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `signal_session::stores::decode_kyber_pre_key`

Proves `decode_kyber_pre_key` against `decodeKyberPreKeySpec` (at any 4 KiB-aligned image base) and
`decodeKyberPreKeyPlacedSpec` (`[LibsignalPlacement]`, Block `595`): invokes the inner
`SignedPreKeyRecordStructure` decoder into an 88-byte stack slot, copies the `Ok` payload to `x0`
or drops `DecodeError` (`drop_glue::<DecodeError> [local#3]`) and writes `InvalidProtobufEncoding`
(`speWord 2`).
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open ProofLib.ProgramReflection CryptoVerification.LibsignalTripleRatchet.Wire Helpers

attribute [local irreducible] Program.fetch Program.externAt?

/-- `decode_kyber_pre_key` meets `decodeKyberPreKeySpec` at any 4 KiB-aligned image base,
given the inner decoder's contract and the ported `drop_glue::<DecodeError> [local#3]`. -/
theorem decodeKyberPreKey_ok_of_decode {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDecode : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName) (signedDecodeSpec A img))
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name)
      (Prost.dropDecodeErrorSpec A))
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName)
      (decodeKyberPreKeySpec A img) := by
  let _ := hb
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [decodeKyberPreKeySpec, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2_nat, hne, hlt⟩, hmem⟩
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have hcall := signedDecode_call_ok hDecode
  have hsp128 := kpkSpAligned_sub128 hsp
  let retDecOff : BitVec 64 := bv% (28)
  have hfull : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (kpkPost img A x s0)
      (tryFromQp s0) := by
    rw [kpkStack_smallRoot_split s0.sp]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (kpkFrame32_unpack (s0.sp - 128#64))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Wire.SepWPp.exists_pre fun c0 => Wire.SepWPp.exists_pre fun c1 =>
      Wire.SepWPp.exists_pre fun c2 => Wire.SepWPp.exists_pre fun c3 => ?_
    have heok := @epilogue_ok_wp img A ext x s0
    have heerr := @epilogue_err_wp img A ext hDrop x s0
    clear hDecode hDrop
    code_fetches_from CryptoVerification.libsignalSessionCode kpkDec
      img.base (Rust.withPanics ext) kpkDec_fnOff kpkDecOff 0 28
    dsimp only [tripleRatchetProgAtExt, decodeKyberPreKeyName] at hcall heok heerr hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      "libsignal_cli::stores::decode_kyber_pre_key" = entry
    examples_hide_fetches
    have h0 : s0.readReg64 (Reg.gpr 0#5) = x.ret := hx0
    have h1 : s0.readReg64 (Reg.gpr 1#5) = x.bytesA := hx1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + signedDecodeRelOff) ?_
    wp_steps
    refine Wire.SepWP.done (by dsimp only [signedDecodeRelOff]; simp [arm64_norm])
      (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    have hsp120 : s0.sp - 120#64 = s0.sp - 128#64 + 8#64 := by bv_omega
    refine Wire.SepWPp.call_tryFrom ⟨x.bytesA, x.bytes, s0.sp - 128#64 + 8#64⟩ hcall
      (by dsimp only [signedDecodeRelOff]; simp [arm64_norm])
      (by simp [hrun, arm64_norm])
      (by simpa [State.spAligned, arm64_norm] using hsp128) hF1 hsym1
      (ret_pc := entry + retDecOff) (by dsimp only [retDecOff]; simp [arm64_norm])
      (by simp [arm64_norm])
      (T := (x.bytesA ↦ₛ x.bytes) ∗ memRegion (s0.sp - 128#64 + 8#64) 88 ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗ A.pool)
      (φ := (s0.readReg64 .x2).toNat = x.bytes.length ∧
        0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32)
      (by simp [h1, hsp120, arm64_norm])
      ⟨hx2_nat, hne, hlt⟩
      (by sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 128#64 := by simpa [arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [h0, arm64_norm] using hcs2.1
    have hsaved2 : KpkSavedRegs s0 s2 := KpkSavedRegs.of_calleeSaved
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩ hcs2
    have hasub : s0.sp - 128#64 - 65408#64 = s0.sp - 65536#64 := by bv_omega
    have ha96 : s0.sp - 128#64 + 96#64 = s0.sp - 32#64 := by bv_omega
    have ha104 : s0.sp - 128#64 + 104#64 = s0.sp - 24#64 := by bv_omega
    have ha112 : s0.sp - 128#64 + 112#64 = s0.sp - 16#64 := by bv_omega
    have ha120 : s0.sp - 128#64 + 120#64 = s0.sp - 8#64 := by bv_omega
    dsimp only [retDecOff] at hpc2
    dsimp only
    cases hdec : CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.decode x.bytes with
    | none =>
      dsimp only [signedDecodeResultAt]
      have ha16 : s0.sp - 128#64 + 8#64 + 8#64 = s0.sp - 128#64 + 16#64 := by bv_omega
      have ha24 : s0.sp - 128#64 + 8#64 + 16#64 = s0.sp - 128#64 + 24#64 := by bv_omega
      rw [ha16, ha24]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Wire.SepWPp.exists_pre fun e => ?_
      have he := @heerr s2 e hdec hpc2 hrun2 hsp2_eq hsp2_align hF2 hsym2
        (by simpa [arm64_norm] using htr2) hx19_2 hsaved2
      refine Wire.SepWPp.mono_pre ?_ he
      simp only [kpkSubStack, arm64_norm]
      rw [hasub, ha96, ha104, ha112, ha120]
      apply entails_of_eq; ac_rfl
    | some m =>
      dsimp only [signedDecodeResultAt]
      have he := @heok s2 m hdec hpc2 hrun2 hsp2_eq hsp2_align hF2 hsym2
        (by simpa [arm64_norm] using htr2) hx19_2 hsaved2
      refine Wire.SepWPp.mono_pre ?_ he
      simp only [kpkSubStack, arm64_norm]
      rw [hasub, ha96, ha104, ha112, ha120]
      apply entails_of_eq; ac_rfl
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim

/-! ## Relocatable `[LibsignalPlacement]` Proof (Block `595`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

/-- Relocatable `decode_kyber_pre_key` (block `595`) meets `decodeKyberPreKeyPlacedSpec`,
given the relocatable inner decoder contract (block `562`) and `drop_glue::<DecodeError> [local#3]`
(block `555`). -/
theorem decodeKyberPreKey_placed_ok_of_decode [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hDecode : subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodePlacedSpec A))
    (hDrop : subroutine_ok (lsProg_551 H) (blkPl_551).base (Prost.dropDecodeErrorSpec A)) :
    subroutine_ok (lsProg_595 H) (blkPl_595).base (decodeKyberPreKeyPlacedSpec A) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  obtain ⟨hcrl, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [decodeKyberPreKeyRawSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hne, hlt⟩, hmem⟩
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have hcall := signedDecode_placed_call_ok hDecode
  have hsp128 := kpkSpAligned_sub128 hsp
  have hfull : Wire.SepWPp (lsProg_595 H)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 88 ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (kpkPostPlaced A x s0)
      (tryFromQp s0) := by
    rw [kpkStack_smallRoot_split s0.sp]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (kpkFrame32_unpack (s0.sp - 128#64))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Wire.SepWPp.exists_pre fun c0 => Wire.SepWPp.exists_pre fun c1 =>
      Wire.SepWPp.exists_pre fun c2 => Wire.SepWPp.exists_pre fun c3 => ?_
    have heok := @epilogue_ok_placed_wp _ A H x s0
    have heerr := @epilogue_err_placed_wp _ A H hDrop x s0
    clear hDecode hDrop
    have h0 : s0.readReg64 (Reg.gpr 0#5) = x.ret := hx0
    have h1 : s0.readReg64 (Reg.gpr 1#5) = x.bytesA := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]; rfl)
      (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    have hsp120 : s0.sp - 120#64 = s0.sp - 128#64 + 8#64 := by bv_omega
    refine sepWPp_call_lscro ⟨x.bytesA, x.bytes, s0.sp - 128#64 + 8#64⟩ hcall
      (by simp [arm64_norm]; rfl)
      (by simp [hrun, arm64_norm])
      (by simpa [State.spAligned, arm64_norm] using hsp128) hcrl1
      (ret_pc := (blkPl_595).base + kpkOff_retDec) (by simp [arm64_norm])
      (by simp [arm64_norm])
      (T := (x.bytesA ↦ₛ x.bytes) ∗ memRegion (s0.sp - 128#64 + 8#64) 88 ∗
        stackAt (s0.sp - 128#64) signedDecodeStack ∗ A.pool)
      (φ := (s0.readReg64 .x2).toNat = x.bytes.length ∧
        0 < x.bytes.length ∧ x.bytes.length < 2 ^ 32)
      (by simp [signedDecodeRawSpec, h1, hsp120, arm64_norm])
      ⟨hx2_nat, hne, hlt⟩
      (by sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [signedDecodeRawSpec]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 128#64 := by simpa [arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [h0, arm64_norm] using hcs2.1
    have hsaved2 : KpkSavedRegs s0 s2 := KpkSavedRegs.of_calleeSaved
      ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
       by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩ hcs2
    have hasub : s0.sp - 128#64 - 65408#64 = s0.sp - 65536#64 := by bv_omega
    have ha96 : s0.sp - 128#64 + 96#64 = s0.sp - 32#64 := by bv_omega
    have ha104 : s0.sp - 128#64 + 104#64 = s0.sp - 24#64 := by bv_omega
    have ha112 : s0.sp - 128#64 + 112#64 = s0.sp - 16#64 := by bv_omega
    have ha120 : s0.sp - 128#64 + 120#64 = s0.sp - 8#64 := by bv_omega
    cases hdec : CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.decode x.bytes with
    | none =>
      dsimp only [signedDecodeResultAt]
      have ha16 : s0.sp - 128#64 + 8#64 + 8#64 = s0.sp - 128#64 + 16#64 := by bv_omega
      have ha24 : s0.sp - 128#64 + 8#64 + 16#64 = s0.sp - 128#64 + 24#64 := by bv_omega
      rw [ha16, ha24]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Wire.SepWPp.exists_pre fun e => ?_
      have he := @heerr s2 e hdec hpc2 hrun2 hsp2_eq hsp2_align hcrl2
        (by simpa [arm64_norm] using htr2) hx19_2 hsaved2
      refine Wire.SepWPp.mono_pre ?_ he
      simp only [kpkSubStack, arm64_norm]
      rw [hasub, ha96, ha104, ha112, ha120]
      apply entails_of_eq; ac_rfl
    | some m =>
      dsimp only [signedDecodeResultAt]
      have he := @heok s2 m hdec hpc2 hrun2 hsp2_eq hsp2_align hcrl2
        (by simpa [arm64_norm] using htr2) hx19_2 hsaved2
      refine Wire.SepWPp.mono_pre ?_ he
      simp only [kpkSubStack, arm64_norm]
      rw [hasub, ha96, ha104, ha112, ha120]
      apply entails_of_eq; ac_rfl
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim

end Placed

end CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey
