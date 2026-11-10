/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedDeps
public import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymD
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RecordCodecs.Deps

/-!
# `decode_kyber_pre_key` Instruction Fetches and Call Transfer

Instruction-fetch lemmas and `[LibsignalPlacement]` cross-block call combinators for
`signal_session::stores::decode_kyber_pre_key` (Block `595`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers

open Arm64 ProofLib CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecsBinary

abbrev kpkDecOff : Nat :=
  num% (ls_off% "libsignal_cli::stores::decode_kyber_pre_key")

theorem kpkDec_fnOff :
    libsignalSessionCode.fnOff decodeKyberPreKeyName = kpkDecOff :=
  ls_lemma% fnOff "libsignal_cli::stores::decode_kyber_pre_key"

gen_decodes CryptoVerification.libsignalSessionCode_tree kpkDec
  [(num% (ls_off% "libsignal_cli::stores::decode_kyber_pre_key")) →
   (num% (ls_off% "libsignal_cli::stores::decode_kyber_pre_key" + 128))]

abbrev signedDecodeRelOff : BitVec 64 :=
  bv% (2 ^ 64 +
    (ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>") -
    ls_off% "libsignal_cli::stores::decode_kyber_pre_key")

abbrev dropDecodeError3RelOff : BitVec 64 :=
  bv% (2 ^ 64 +
    (ls_off% "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]") -
    ls_off% "libsignal_cli::stores::decode_kyber_pre_key")

theorem signedDecode_call_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDecode : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName) (signedDecodeSpec A img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + signedDecodeRelOff)
      (signedDecodeSpec A img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + signedDecodeRelOff =
      (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName := by
    dsimp only [signedDecodeRelOff]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_cli::stores::decode_kyber_pre_key"),
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")]
    bv_omega
  rw [heq]; exact hDecode

theorem dropDecodeError3_call_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hDrop : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name)
      (Prost.dropDecodeErrorSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + dropDecodeError3RelOff)
      ((Prost.dropDecodeErrorSpec A).inImage img) := by
  have heq :
      (tripleRatchetProgAtExt img.base ext).fnAddr decodeKyberPreKeyName + dropDecodeError3RelOff =
      (tripleRatchetProgAtExt img.base ext).fnAddr dropDecodeError3Name := by
    dsimp only [dropDecodeError3RelOff]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_cli::stores::decode_kyber_pre_key"),
      (ls_lemma% fnOff "core::ptr::drop_glue::<prost::error::DecodeError> [local#3]")]
    bv_omega
  rw [heq]; exact subroutine_ok_inImage_of_subroutine_ok img hDrop

/-! ## Relocatable `[LibsignalPlacement]` Call Transfer (Block `595`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

theorem signedDecode_placed_call_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDecode : subroutine_ok (lsProg_562 H) (blkPl_562).base (signedDecodePlacedSpec A)) :
    subroutine_ok (lsProg_595 H) (blkPl_562).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (signedDecodeRawSpec A)) :=
  ls_subroutine_ok_lscro_of_block (callerProg := lsProg_595 H) hDecode

theorem dropDecodeError3_placed_call_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hDrop : subroutine_ok (lsProg_551 H) (blkPl_551).base (Prost.dropDecodeErrorSpec A)) :
    subroutine_ok (lsProg_595 H) (blkPl_551).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.dropDecodeErrorSpec A)) :=
  ls_subroutine_ok_lscro_of_plain (callerProg := lsProg_595 H) hDrop

/-- Non-panicking specialization of `sepWPp_call_lscro` (`spec.onPanic x s sf = ⌜False⌝`). -/
theorem sepWPp_call_noPanic_lscro {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {ret entry ret_pc : BitVec 64} {s0 s : Arm64.State} {P T F : SepProp} {φ : Prop}
    {Q : Arm64.State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hcrl : LibsignalTripleRatchet.LibsignalCodeRoLoaded pl s.mem)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F := by sep_focus)
    (hnext : ∀ sf : Arm64.State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → LibsignalTripleRatchet.LibsignalCodeRoLoaded pl sf.mem →
      CalleeSavedPreserved s sf →
      Wire.SepWPp prog ret sf (spec.post x s sf ∗ F) Q (Wire.tryFromQp s0))
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝ := by intros; rfl)
    (hpan : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intros; rfl)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    Wire.SepWPp prog ret s P Q (Wire.tryFromQp s0) := by
  intro R' hm hL
  have hpre : s.mem ⊨ (LibsignalTripleRatchet.withLsCodeRoLoaded pl spec).pre x s ∗ (F ∗ R') := by
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hoom⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hspm_align : sm.spAligned = true := by
      rw [Arm64.State.spAligned, hspm, ← Arm64.State.spAligned]; exact hsp
    have hcrl_m := hcrl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', ⟨hpcf, hrunf, Pf, hmf, hqf, hvf⟩ | hpanf⟩ :=
      hnext sm hpcm hrunm hspm hspm_align hcrl_m hcsm R' hpost (hsteps.codeLoaded hL)
    · exact ⟨sf, hsteps.trans hsteps',
        Or.inl ⟨hpcf, hrunf, Pf, hmf, hqf, hvf.trans hcsm.2.2.2.2.2.2.2.2.2.2.2⟩⟩
    · exact ⟨sf, hsteps.trans hsteps', Or.inr hpanf⟩
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    rw [hpan sm] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost
    rw [hexit sm code] at hpost
    exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded] at hoom
    rw [hoom_eq sm] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

end Placed

end CryptoVerification.RecordCodecsBinary.DecodeKyberPreKey.Helpers
