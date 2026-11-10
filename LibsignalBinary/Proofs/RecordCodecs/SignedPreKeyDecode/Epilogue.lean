/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs
import LibsignalBinary.Proofs.RecordCodecs.Deps
import LibsignalBinary.Proofs.RecordCodecs.SignedPreKeyDecode.ErrTails
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostCleanup
import ProofLib.SepLogic.WPp

/-!
# `SignedPreKeyRecordStructure::decode` Convergence and Return Epilogue

Verifies the shared convergence tail from `+656` (`spkOff_converge`) to return across both `Ok`
(`+760 .. +820`) and `Err` (`Vec<u8>` deallocations `+680 .. +732` and `+736 .. +756`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
attribute [local arm64_norm] BitVec.toNat_zero

namespace CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Final return from `+656` (`spkOff_converge`) to `s0.readReg64 .x30` -/

abbrev spkRetPost (cfg : SpkCfg) (A : RustAlloc) (s0 : State) (x : DecodeGhost)
    (out : Option SignedPreKeyRecordStructure) : State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧
      (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
      (Pf ⊢ ⌜sf.trace = s0.trace⌝ ∗ signedDecodeResultAt A x.ret out ∗
        (x.bytesA ↦ₛ x.bytes) ∗ stackAt s0.sp (224 + cfg.subStack) ∗ A.pool)

/-- Shared epilogue `+736..+756` (`Err` return). -/
theorem retErr_736_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeState img s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_freeSigRet)
    (hrun : s.status = .Running) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (signedDecodeResultAt A x.ret out ∗
        memRegion (s0.sp - 224#64) 16 ∗
        memRegion (s0.sp - 224#64 + 16#64) 88 ∗
        ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) cfg.subStack)
      (spkRetPost cfg A s0 x out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hF, hsym, htr, _hx24, _hx19, hsaved⟩
  unfold spkCalleeSavedAt
  simp only [sepConj_assoc]
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 736 24
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  refine Wire.SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _ _
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x25,
      by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27,
      by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm], hv⟩
  · rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := spkStack_unsplit cfg s0.sp s0
    unfold spkCalleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
    apply entails_of_eq
    simp only [hsp_eq, arm64_norm]
    ac_rfl

/-- Shared epilogue `+800..+820` (`Ok` return). -/
theorem retOk_800_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeState img s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_retOk)
    (hrun : s.status = .Running) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (signedDecodeResultAt A x.ret out ∗
        memRegion (s0.sp - 224#64) 16 ∗
        memRegion (s0.sp - 224#64 + 16#64) 88 ∗
        ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) cfg.subStack)
      (spkRetPost cfg A s0 x out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hF, hsym, htr, _hx24, _hx19, hsaved⟩
  unfold spkCalleeSavedAt
  simp only [sepConj_assoc]
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
    img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 800 24
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
  examples_hide_fetches
  refine Wire.SepWPp.of_sepWP_end hF hsym ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _ _
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x25,
      by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27,
      by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm], hv⟩
  · rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := spkStack_unsplit cfg s0.sp s0
    unfold spkCalleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
    apply entails_of_eq
    simp only [hsp_eq, arm64_norm]
    ac_rfl

/-- Free `sig` buffer (`+716..+732` → `+736`). -/
theorem freeSig_716_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {x : DecodeGhost} {s0 s : State}
    {sigCap sigPtr : BitVec 64} {sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeState img s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_freePrivRet)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = sigCap)
    (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (vecU8Buf A sigCap sigPtr sigBs ∗
        signedDecodeResultAt A x.ret out ∗
        memRegion (s0.sp - 224#64) 16 ∗
        memRegion (s0.sp - 224#64 + 16#64) 88 ∗
        ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) cfg.subStack)
      (spkRetPost cfg A s0 x out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hx24, hx19, hsaved⟩
  have hnext := @retErr_736_wp cfg img A ext x s0
  by_cases hcap : sigCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A sigPtr sigBs)) ?_
    rw [emp_sepConj]
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 716 4
    dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    have h20 : s.readReg64 (Reg.gpr 20#5) = 0#64 := hx20
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_freeSigRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext (out := out)
      ⟨by simp [hsp_eq, arm64_norm],
       by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hF1, hsym1, by simp [htr, arm64_norm],
       by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27,
        by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A sigCap sigPtr sigBs hcap)) ?_
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := B.dealloc
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 716 20
    dsimp only [tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split (s0.sp - 224#64) cfg.deallocStk cfg.subStack
      (spkCfg_split_dealloc cfg) (spkCfg_subStack_le cfg)
    have h20 : s.readReg64 (Reg.gpr 20#5) = sigCap := hx20
    have h21 : s.readReg64 (Reg.gpr 21#5) = sigPtr := hx21
    have hbeq : (sigCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (sigPtr, sigCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + spkOff_freeSigRet) (by simp [arm64_norm])
      (T := A.pool ∗ A.live sigPtr sigCap.toNat 1 ∗ memRegion sigPtr sigCap.toNat ∗
        stackAt (s0.sp - 224#64) cfg.deallocStk)
      (φ := LayoutOk sigCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, hsp_eq, h20, h21, hbeq, arm64_norm])
      (layoutOk_align1 hpos hlt)
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine Wire.SepWPp.mono_pre ?_
      (hnext (s := s2) (out := out)
        ⟨hsp2_eq, hsp2_align, hF2, hsym2, by simpa [htr2, arm64_norm] using htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2)
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    apply entails_of_eq
    rw [hstack, hb1, hb2, hb3]
    simp only [hsp_eq, hsp2_eq, arm64_norm]
    ac_rfl

/-- Free `priv` buffer (`+696..+712` → `+716`). -/
theorem freePriv_696_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {x : DecodeGhost} {s0 s : State}
    {privCap privPtr sigCap sigPtr : BitVec 64} {privBs sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeState img s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_freePubRet)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = privCap)
    (hx23 : s.readReg64 .x23 = privPtr)
    (hx20 : s.readReg64 .x20 = sigCap)
    (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (vecU8Buf A privCap privPtr privBs ∗
        vecU8Buf A sigCap sigPtr sigBs ∗
        signedDecodeResultAt A x.ret out ∗
        memRegion (s0.sp - 224#64) 16 ∗
        memRegion (s0.sp - 224#64 + 16#64) 88 ∗
        ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) cfg.subStack)
      (spkRetPost cfg A s0 x out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hx24, hx19, hsaved⟩
  have hnext := @freeSig_716_wp cfg img A ext B x s0
  by_cases hcap : privCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A privPtr privBs)) ?_
    rw [emp_sepConj]
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 696 4
    dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    have h22 : s.readReg64 (Reg.gpr 22#5) = 0#64 := hx22
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_freePrivRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext (sigCap := sigCap) (sigPtr := sigPtr) (sigBs := sigBs) (out := out)
      ⟨by simp [hsp_eq, arm64_norm],
       by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hF1, hsym1, by simp [htr, arm64_norm],
       by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27,
        by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx20, arm64_norm]) (by simp [hx21, arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A privCap privPtr privBs hcap)) ?_
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := B.dealloc
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 696 20
    dsimp only [tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split (s0.sp - 224#64) cfg.deallocStk cfg.subStack
      (spkCfg_split_dealloc cfg) (spkCfg_subStack_le cfg)
    have h22 : s.readReg64 (Reg.gpr 22#5) = privCap := hx22
    have h23 : s.readReg64 (Reg.gpr 23#5) = privPtr := hx23
    have hbeq : (privCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (privPtr, privCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + spkOff_freePrivRet) (by simp [arm64_norm])
      (T := A.pool ∗ A.live privPtr privCap.toNat 1 ∗ memRegion privPtr privCap.toNat ∗
        stackAt (s0.sp - 224#64) cfg.deallocStk)
      (φ := LayoutOk privCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, hsp_eq, h22, h23, hbeq, arm64_norm])
      (layoutOk_align1 hpos hlt)
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = sigCap := by simpa [hx20, hbeq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = sigPtr := by simpa [hx21, hbeq, arm64_norm] using hcs2.2.2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine Wire.SepWPp.mono_pre ?_
      (hnext (s := s2) (sigCap := sigCap) (sigPtr := sigPtr) (sigBs := sigBs) (out := out)
        ⟨hsp2_eq, hsp2_align, hF2, hsym2, by simpa [htr2, arm64_norm] using htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2 hx20_2 hx21_2)
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    apply entails_of_eq
    rw [hstack, hb1, hb2, hb3]
    simp only [hsp_eq, hsp2_eq, arm64_norm]
    ac_rfl

/-- Free `pub` buffer (`+680..+692` → `+696`). -/
theorem freePub_680_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {x : DecodeGhost} {s0 s : State}
    {pubCap pubPtr privCap privPtr sigCap sigPtr : BitVec 64}
    {pubBs privBs sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeState img s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_freePub)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = pubCap)
    (hx0 : s.readReg64 .x0 = pubPtr)
    (hx22 : s.readReg64 .x22 = privCap)
    (hx23 : s.readReg64 .x23 = privPtr)
    (hx20 : s.readReg64 .x20 = sigCap)
    (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (vecU8Buf A pubCap pubPtr pubBs ∗
        vecU8Buf A privCap privPtr privBs ∗
        vecU8Buf A sigCap sigPtr sigBs ∗
        signedDecodeResultAt A x.ret out ∗
        memRegion (s0.sp - 224#64) 16 ∗
        memRegion (s0.sp - 224#64 + 16#64) 88 ∗
        ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
        stackAt (s0.sp - 224#64) cfg.subStack)
      (spkRetPost cfg A s0 x out)
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hx24, hx19, hsaved⟩
  have hnext := @freePriv_696_wp cfg img A ext B x s0
  by_cases hcap : pubCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A pubPtr pubBs)) ?_
    rw [emp_sepConj]
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 680 4
    dsimp only [tripleRatchetProgAtExt] at hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    have h8 : s.readReg64 (Reg.gpr 8#5) = 0#64 := hx8
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_freePubRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    exact hnext (privCap := privCap) (privPtr := privPtr) (sigCap := sigCap) (sigPtr := sigPtr)
      (privBs := privBs) (sigBs := sigBs) (out := out)
      ⟨by simp [hsp_eq, arm64_norm],
       by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hF1, hsym1, by simp [htr, arm64_norm],
       by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27,
        by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx22, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx20, arm64_norm]) (by simp [hx21, arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A pubCap pubPtr pubBs hcap)) ?_
    simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun ⟨hpos, hlt, _⟩ => ?_
    have hcall := B.dealloc
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 680 16
    dsimp only [tripleRatchetProgAtExt] at hcall hnext hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    have hstack := stackAt_sub_split (s0.sp - 224#64) cfg.deallocStk cfg.subStack
      (spkCfg_split_dealloc cfg) (spkCfg_subStack_le cfg)
    have h8 : s.readReg64 (Reg.gpr 8#5) = pubCap := hx8
    have h0 : s.readReg64 (Reg.gpr 0#5) = pubPtr := hx0
    have hbeq : (pubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine Wire.SepWPp.of_sepWP_frozen hF hsym
      (mid := entry + bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "<libsignal_protocol::proto::storage::SignedPreKeyRecordStructure as prost::message::Message>::decode::<&[u8]>")) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.call_noPanic_tryFrom (pubPtr, pubCap.toNat, 1) hcall
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hF1 hsym1
      (ret_pc := entry + spkOff_freePubRet) (by simp [arm64_norm])
      (T := A.pool ∗ A.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗
        stackAt (s0.sp - 224#64) cfg.deallocStk)
      (φ := LayoutOk pubCap.toNat 1)
      (by simp [rustDeallocExternSpecWithStack, hsp_eq, h8, h0, hbeq, arm64_norm])
      (layoutOk_align1 hpos hlt)
      (by rw [hstack]; sep_focus)
      ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hF2 hsym2 hcs2
    dsimp only [rustDeallocExternSpecWithStack]
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = sigCap := by simpa [hx20, hbeq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = sigPtr := by simpa [hx21, hbeq, arm64_norm] using hcs2.2.2.1
    have hx22_2 : s2.readReg64 .x22 = privCap := by simpa [hx22, hbeq, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 .x23 = privPtr := by simpa [hx23, hbeq, arm64_norm] using hcs2.2.2.2.2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine Wire.SepWPp.mono_pre ?_
      (hnext (s := s2) (privCap := privCap) (privPtr := privPtr) (sigCap := sigCap) (sigPtr := sigPtr)
        (privBs := privBs) (sigBs := sigBs) (out := out)
        ⟨hsp2_eq, hsp2_align, hF2, hsym2, by simpa [htr2, arm64_norm] using htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2 hx22_2 hx23_2 hx20_2 hx21_2)
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    apply entails_of_eq
    rw [hstack, hb1, hb2, hb3]
    simp only [hsp_eq, hsp2_eq, arm64_norm]
    ac_rfl

/-- Unified convergence theorem `+656` (`spkOff_converge`) → `s0.readReg64 .x30` covering both
`out = some m` (`+656..+668 → +760..+820`) and `out = none` (`+656..+756`). -/
theorem converge_656_to_ret_wp {cfg : SpkCfg} {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (B : SpkBundle cfg img A ext)
    {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeState img s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr signedDecodeName + spkOff_converge)
    (hrun : s.status = .Running) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s
      (spkConvergeMemAt cfg.subStack A (s0.sp - 224#64) x.ret x.bytesA x.bytes out (s.readReg64 .x1) ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (spkRetPost cfg A s0 x out)
      (tryFromQp s0) := by
  let sp' := s0.sp - 224#64
  rcases hst with ⟨hsp_eq, hsp, hF, hsym, htr, hx24, hx19, hsaved⟩
  cases out with
  | some m =>
    unfold spkConvergeMemAt spkStructOf
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun g => ?_
    refine Wire.SepWPp.pure_pre fun hx1_zero => ?_
    unfold spkStructAt
    rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf, vecU8At_eq_header_buf]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (memRegion_four_entails (sp' + 100#64))
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (spkMemRegion88_unpack x.ret)))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
      Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
      Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 =>
      Wire.SepWPp.exists_pre fun r6 => Wire.SepWPp.exists_pre fun r7 =>
      Wire.SepWPp.exists_pre fun r8 => Wire.SepWPp.exists_pre fun r9 =>
      Wire.SepWPp.exists_pre fun r10 => Wire.SepWPp.exists_pre fun pad32 => ?_
    have hp96 : ((s0.sp - 224#64 + 96#64) ↦₃₂ m.id) ∗ ((s0.sp - 224#64 + 100#64) ↦₃₂ pad32) =
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ m.id)) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (s0.sp - 224#64 + 96#64) m.id pad32
    have hret := @retOk_800_wp cfg img A ext x s0
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 656 16
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 760 40
    dsimp only [tripleRatchetProgAtExt, sp'] at hret hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    refine Wire.SepWPp.mono_pre
      (P' := ((s0.sp - 224#64 + 16#64) ↦₆₄ g.pub.cap) ∗ ((s0.sp - 224#64 + 24#64) ↦₆₄ g.pub.ptr) ∗
        ((s0.sp - 224#64 + 32#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
        ((s0.sp - 224#64 + 40#64) ↦₆₄ g.priv.cap) ∗ ((s0.sp - 224#64 + 48#64) ↦₆₄ g.priv.ptr) ∗
        ((s0.sp - 224#64 + 56#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((s0.sp - 224#64 + 64#64) ↦₆₄ g.sig.cap) ∗ ((s0.sp - 224#64 + 72#64) ↦₆₄ g.sig.ptr) ∗
        ((s0.sp - 224#64 + 80#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
        ((s0.sp - 224#64 + 88#64) ↦₆₄ m.timestamp) ∗
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ m.id)) ∗
        vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
        vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ∗
        vecU8Buf A g.sig.cap g.sig.ptr m.signature ∗
        memRegion (s0.sp - 224#64) 16 ∗ ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
        ((x.ret + 24#64) ↦₆₄ r3) ∗ ((x.ret + 32#64) ↦₆₄ r4) ∗ ((x.ret + 40#64) ↦₆₄ r5) ∗
        ((x.ret + 48#64) ↦₆₄ r6) ∗ ((x.ret + 56#64) ↦₆₄ r7) ∗ ((x.ret + 64#64) ↦₆₄ r8) ∗
        ((x.ret + 72#64) ↦₆₄ r9) ∗ ((x.ret + 80#64) ↦₆₄ r10) ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗ stackAt (s0.sp - 224#64) cfg.subStack ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (by
        dsimp only [vecHeader]
        rw [← sepConj_assoc ((s0.sp - 224#64 + 96#64) ↦₃₂ m.id), hp96]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        apply entails_of_eq; ac_rfl) ?_
    have h1 : s.readReg64 (Reg.gpr 1#5) = 0#64 := hx1_zero
    have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
    have h24 : s.readReg64 (Reg.gpr 24#5) = s0.sp - 224#64 + 16#64 := hx24
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_retOk) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre ?_
      (hret (out := some m)
        ⟨by simp [hsp_eq, arm64_norm],
         by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hF1, hsym1, by simp [htr, arm64_norm],
         by simp [h24, arm64_norm], by simp [h19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25,
          by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27,
          by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]))
    have h88 : ((s0.sp - 224#64 + 16#64) ↦₆₄ g.pub.cap) ∗ ((s0.sp - 224#64 + 24#64) ↦₆₄ g.pub.ptr) ∗
        ((s0.sp - 224#64 + 32#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
        ((s0.sp - 224#64 + 40#64) ↦₆₄ g.priv.cap) ∗ ((s0.sp - 224#64 + 48#64) ↦₆₄ g.priv.ptr) ∗
        ((s0.sp - 224#64 + 56#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
        ((s0.sp - 224#64 + 64#64) ↦₆₄ g.sig.cap) ∗ ((s0.sp - 224#64 + 72#64) ↦₆₄ g.sig.ptr) ∗
        ((s0.sp - 224#64 + 80#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
        ((s0.sp - 224#64 + 88#64) ↦₆₄ m.timestamp) ∗
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ m.id)) ⊢ memRegion (s0.sp - 224#64 + 16#64) 88 := by
      rw [← hp96]
      simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        spkStruct88_pack (s0.sp - 224#64) g.pub.cap g.pub.ptr (BitVec.ofNat 64 m.publicKey.length)
          g.priv.cap g.priv.ptr (BitVec.ofNat 64 m.privateKey.length)
          g.sig.cap g.sig.ptr (BitVec.ofNat 64 m.signature.length)
          m.timestamp m.id pad32
    have hres := spkOk88_intro A g x.ret m pad32 rfl
    refine Entails.trans ?_
      (sepConj_mono hres (sepConj_mono_right (sepConj_mono_left h88)))
    apply entails_of_eq
    simp only [hsp_eq, h19, h24, arm64_norm]
    try ac_rfl
  | none =>
    unfold spkConvergeMemAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun mErr => ?_
    refine Wire.SepWPp.pure_pre fun hx1_nz => ?_
    unfold spkStructOf
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun g => ?_
    unfold spkStructAt
    rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf, vecU8At_eq_header_buf]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (memRegion_four_entails (sp' + 100#64))
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (spkMemRegion88_err_unpack x.ret))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
      Wire.SepWPp.exists_pre fun pad32 => ?_
    have hp96 : ((s0.sp - 224#64 + 96#64) ↦₃₂ mErr.id) ∗ ((s0.sp - 224#64 + 100#64) ↦₃₂ pad32) =
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ mErr.id)) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (s0.sp - 224#64 + 96#64) mErr.id pad32
    have hfree := @freePub_680_wp cfg img A ext B x s0
    code_fetches_from CryptoVerification.libsignalSessionCode
      CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers.spkDec
      img.base (Rust.withPanics ext) spkDec_fnOff spkDecOff 656 24
    dsimp only [tripleRatchetProgAtExt, sp'] at hfree hpc ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr signedDecodeName = entry
    examples_hide_fetches
    refine Wire.SepWPp.mono_pre
      (P' := ((s0.sp - 224#64 + 16#64) ↦₆₄ g.pub.cap) ∗ ((s0.sp - 224#64 + 24#64) ↦₆₄ g.pub.ptr) ∗
        ((s0.sp - 224#64 + 32#64) ↦₆₄ BitVec.ofNat 64 mErr.publicKey.length) ∗
        ((s0.sp - 224#64 + 40#64) ↦₆₄ g.priv.cap) ∗ ((s0.sp - 224#64 + 48#64) ↦₆₄ g.priv.ptr) ∗
        ((s0.sp - 224#64 + 56#64) ↦₆₄ BitVec.ofNat 64 mErr.privateKey.length) ∗
        ((s0.sp - 224#64 + 64#64) ↦₆₄ g.sig.cap) ∗ ((s0.sp - 224#64 + 72#64) ↦₆₄ g.sig.ptr) ∗
        ((s0.sp - 224#64 + 80#64) ↦₆₄ BitVec.ofNat 64 mErr.signature.length) ∗
        ((s0.sp - 224#64 + 88#64) ↦₆₄ mErr.timestamp) ∗
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ mErr.id)) ∗
        vecU8Buf A g.pub.cap g.pub.ptr mErr.publicKey ∗
        vecU8Buf A g.priv.cap g.priv.ptr mErr.privateKey ∗
        vecU8Buf A g.sig.cap g.sig.ptr mErr.signature ∗
        decodeErrorAt A (s.readReg64 .x1) ∗
        memRegion (s0.sp - 224#64) 16 ∗ ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ memRegion (x.ret + 16#64) 72 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗ stackAt (s0.sp - 224#64) cfg.subStack ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (by
        dsimp only [vecHeader]
        rw [← sepConj_assoc ((s0.sp - 224#64 + 96#64) ↦₃₂ mErr.id), hp96]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        apply entails_of_eq; ac_rfl) ?_
    let err := s.readReg64 .x1
    have h1 : s.readReg64 (Reg.gpr 1#5) = err := rfl
    have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
    have hbeq : (err == 0#64) = false := beq_eq_false_iff_ne.mpr hx1_nz
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + spkOff_freePub) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine Wire.SepWPp.mono_pre ?_
      (hfree (pubCap := g.pub.cap) (pubPtr := g.pub.ptr)
        (privCap := g.priv.cap) (privPtr := g.priv.ptr)
        (sigCap := g.sig.cap) (sigPtr := g.sig.ptr)
        (pubBs := mErr.publicKey) (privBs := mErr.privateKey) (sigBs := mErr.signature)
        (out := none)
        ⟨by simp [hsp_eq, arm64_norm],
         by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hF1, hsym1, by simp [htr, arm64_norm],
         by simp [hx24, arm64_norm], by simp [h19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25,
          by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27,
          by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]))
    have h88 : ((s0.sp - 224#64 + 16#64) ↦₆₄ g.pub.cap) ∗ ((s0.sp - 224#64 + 24#64) ↦₆₄ g.pub.ptr) ∗
        ((s0.sp - 224#64 + 32#64) ↦₆₄ BitVec.ofNat 64 mErr.publicKey.length) ∗
        ((s0.sp - 224#64 + 40#64) ↦₆₄ g.priv.cap) ∗ ((s0.sp - 224#64 + 48#64) ↦₆₄ g.priv.ptr) ∗
        ((s0.sp - 224#64 + 56#64) ↦₆₄ BitVec.ofNat 64 mErr.privateKey.length) ∗
        ((s0.sp - 224#64 + 64#64) ↦₆₄ g.sig.cap) ∗ ((s0.sp - 224#64 + 72#64) ↦₆₄ g.sig.ptr) ∗
        ((s0.sp - 224#64 + 80#64) ↦₆₄ BitVec.ofNat 64 mErr.signature.length) ∗
        ((s0.sp - 224#64 + 88#64) ↦₆₄ mErr.timestamp) ∗
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ mErr.id)) ⊢ memRegion (s0.sp - 224#64 + 16#64) 88 := by
      rw [← hp96]
      simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        spkStruct88_pack (s0.sp - 224#64) g.pub.cap g.pub.ptr (BitVec.ofNat 64 mErr.publicKey.length)
          g.priv.cap g.priv.ptr (BitVec.ofNat 64 mErr.privateKey.length)
          g.sig.cap g.sig.ptr (BitVec.ofNat 64 mErr.signature.length)
          mErr.timestamp mErr.id pad32
    have hres := spkErr88_intro A x.ret err (out := none) rfl
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hres (sepConj_mono_right (sepConj_mono_left h88))))))
    apply entails_of_eq
    dsimp only [errTag, err]
    simp only [hsp_eq, h19, arm64_norm]
    try ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Final Return & Cleanup (Block `562`) -/

section Placed

open CryptoVerification.RecordCodecs.Placed

attribute [local irreducible] Program.fetch Program.externAt?

abbrev spkEpilogueTail (A : RustAlloc) (s0 : State) (x : DecodeGhost)
    (out : Option SignedPreKeyRecordStructure) : SepProp :=
  signedDecodeResultAt A x.ret out ∗
    memRegion (s0.sp - 224#64) 16 ∗
    memRegion (s0.sp - 224#64 + 16#64) 88 ∗
    ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
    memRegion (s0.sp - 224#64 + 112#64) 48 ∗
    spkCalleeSavedAt (s0.sp - 224#64) s0 ∗
    (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗
    stackAt (s0.sp - 224#64) (SpqrV1.Varint.skipField3Stack 100)

private def spkDestWords88 (ret r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : BitVec 64) : SepProp :=
  (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
    ((ret + 24#64) ↦₆₄ r3) ∗ ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ∗
    ((ret + 48#64) ↦₆₄ r6) ∗ ((ret + 56#64) ↦₆₄ r7) ∗ ((ret + 64#64) ↦₆₄ r8) ∗
    ((ret + 72#64) ↦₆₄ r9) ∗ ((ret + 80#64) ↦₆₄ r10)

private def spkRawWords88 (spBase : BitVec 64) (g : SpkGhost)
    (m : SignedPreKeyRecordStructure) (pad32 : BitVec 32) : SepProp :=
  ((spBase + 16#64) ↦₆₄ g.pub.cap) ∗ ((spBase + 24#64) ↦₆₄ g.pub.ptr) ∗
    ((spBase + 32#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
    ((spBase + 40#64) ↦₆₄ g.priv.cap) ∗ ((spBase + 48#64) ↦₆₄ g.priv.ptr) ∗
    ((spBase + 56#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
    ((spBase + 64#64) ↦₆₄ g.sig.cap) ∗ ((spBase + 72#64) ↦₆₄ g.sig.ptr) ∗
    ((spBase + 80#64) ↦₆₄ BitVec.ofNat 64 m.signature.length) ∗
    ((spBase + 88#64) ↦₆₄ m.timestamp) ∗ ((spBase + 96#64) ↦₆₄ (pad32 ++ m.id))

private theorem spkRawWords88_pack (spBase : BitVec 64) (g : SpkGhost)
    (m : SignedPreKeyRecordStructure) (pad32 : BitVec 32) :
    spkRawWords88 spBase g m pad32 ⊢ memRegion (spBase + 16#64) 88 := by
  have hp96 : ((spBase + 96#64) ↦₃₂ m.id) ∗ ((spBase + 100#64) ↦₃₂ pad32) =
      ((spBase + 96#64) ↦₆₄ (pad32 ++ m.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (spBase + 96#64) m.id pad32
  unfold spkRawWords88
  rw [← hp96]
  simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
    spkStruct88_pack spBase g.pub.cap g.pub.ptr (BitVec.ofNat 64 m.publicKey.length)
      g.priv.cap g.priv.ptr (BitVec.ofNat 64 m.privateKey.length)
      g.sig.cap g.sig.ptr (BitVec.ofNat 64 m.signature.length)
      m.timestamp m.id pad32

theorem retErr_736_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_freeSigRet)
    (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (spkEpilogueTail A s0 x out) (spkRetPost spkCfgLegacy A s0 x out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hcrl, htr, _hx24, _hx19, hsaved⟩
  unfold spkEpilogueTail spkCalleeSavedAt
  simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_end_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm], hv⟩
  · rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := spkStack_unsplit spkCfgLegacy s0.sp s0
    dsimp only [spkCfgLegacy, SpkCfg.subStack] at hstk
    unfold spkCalleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
    apply entails_of_eq; simp only [hsp_eq, arm64_norm]; ac_rfl

theorem retOk_800_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_retOk)
    (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (spkEpilogueTail A s0 x out) (spkRetPost spkCfgLegacy A s0 x out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, _hsp, hcrl, htr, _hx24, _hx19, hsaved⟩
  unfold spkEpilogueTail spkCalleeSavedAt
  simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_end_lscro hcrl ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro _
  refine ⟨by simp [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
      by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
      by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28,
      by simp [arm64_norm], hv⟩
  · rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := spkStack_unsplit spkCfgLegacy s0.sp s0
    dsimp only [spkCfgLegacy, SpkCfg.subStack] at hstk
    unfold spkCalleeSavedAt at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk)))
    apply entails_of_eq; simp only [hsp_eq, arm64_norm]; ac_rfl

theorem freeSig_716_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {x : DecodeGhost} {s0 s : State}
    {sigCap sigPtr : BitVec 64} {sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_freePrivRet)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = sigCap) (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (vecU8Buf A sigCap sigPtr sigBs ∗ spkEpilogueTail A s0 x out)
      (spkRetPost spkCfgLegacy A s0 x out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx24, hx19, hsaved⟩
  have hnext := @retErr_736_placed_wp _ A H x s0
  by_cases hcap : sigCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A sigPtr sigBs)) ?_
    rw [emp_sepConj]
    have h20 : s.readReg64 (Reg.gpr 20#5) = 0#64 := hx20
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_freeSigRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    exact hnext (out := out)
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hcrl1, by simp [htr, arm64_norm], by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A sigCap sigPtr sigBs hcap)) ?_
    unfold spkEpilogueTail; simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    have hcall := spk_dealloc_placed_ok hH
    have hstack := stackAt_sub_split (s0.sp - 224#64) allocHookStack (SpqrV1.Varint.skipField3Stack 100)
    have h20 : s.readReg64 (Reg.gpr 20#5) = sigCap := hx20
    have h21 : s.readReg64 (Reg.gpr 21#5) = sigPtr := hx21
    have hbeq : (sigCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [lsρ, lsRustDeallocSym, arm64_norm])
      (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine spk_call_noPanic_lscro (sigPtr, sigCap.toNat, 1) hcall
      (by simp [lsρ, lsRustDeallocSym, arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (ret_pc := (blkPl_562).base + spkOff_freeSigRet) (by simp [arm64_norm])
      (T := A.pool ∗ A.live sigPtr sigCap.toNat 1 ∗ memRegion sigPtr sigCap.toNat ∗
        stackAt (s0.sp - 224#64) allocHookStack)
      (φ := True)
      (by simp [rustDeallocSpec, hsp_eq, h20, h21, hbeq, arm64_norm]) trivial
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocSpec]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine Wire.SepWPp.mono_pre ?_
      (hnext (s := s2) (out := out)
        ⟨hsp2_eq, hsp2_align, hcrl2, by simpa [htr2, arm64_norm] using htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2)
    unfold spkEpilogueTail
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    have hb4 : s0.sp - 224#64 - BitVec.ofNat 64 (SpqrV1.Varint.skipField3Stack 100) = s0.sp - 18240#64 := by
      change s0.sp - 224#64 - 18016#64 = s0.sp - 18240#64; bv_omega
    apply entails_of_eq; rw [hstack, hb1, hb2, hb3, hb4]; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl

theorem freePriv_696_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {x : DecodeGhost} {s0 s : State}
    {privCap privPtr sigCap sigPtr : BitVec 64} {privBs sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_freePubRet)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = privCap) (hx23 : s.readReg64 .x23 = privPtr)
    (hx20 : s.readReg64 .x20 = sigCap) (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (vecU8Buf A privCap privPtr privBs ∗ vecU8Buf A sigCap sigPtr sigBs ∗
        spkEpilogueTail A s0 x out)
      (spkRetPost spkCfgLegacy A s0 x out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx24, hx19, hsaved⟩
  have hnext := @freeSig_716_placed_wp _ A H hH x s0
  by_cases hcap : privCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A privPtr privBs)) ?_
    rw [emp_sepConj]
    have h22 : s.readReg64 (Reg.gpr 22#5) = 0#64 := hx22
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_freePrivRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    exact hnext (sigCap := sigCap) (sigPtr := sigPtr) (sigBs := sigBs) (out := out)
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hcrl1, by simp [htr, arm64_norm], by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx20, arm64_norm]) (by simp [hx21, arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A privCap privPtr privBs hcap)) ?_
    unfold spkEpilogueTail; simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    have hcall := spk_dealloc_placed_ok hH
    have hstack := stackAt_sub_split (s0.sp - 224#64) allocHookStack (SpqrV1.Varint.skipField3Stack 100)
    have h22 : s.readReg64 (Reg.gpr 22#5) = privCap := hx22
    have h23 : s.readReg64 (Reg.gpr 23#5) = privPtr := hx23
    have hbeq : (privCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [lsρ, lsRustDeallocSym, arm64_norm])
      (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine spk_call_noPanic_lscro (privPtr, privCap.toNat, 1) hcall
      (by simp [lsρ, lsRustDeallocSym, arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (ret_pc := (blkPl_562).base + spkOff_freePrivRet) (by simp [arm64_norm])
      (T := A.pool ∗ A.live privPtr privCap.toNat 1 ∗ memRegion privPtr privCap.toNat ∗
        stackAt (s0.sp - 224#64) allocHookStack)
      (φ := True)
      (by simp [rustDeallocSpec, hsp_eq, h22, h23, hbeq, arm64_norm]) trivial
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocSpec]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = sigCap := by simpa [hx20, hbeq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = sigPtr := by simpa [hx21, hbeq, arm64_norm] using hcs2.2.2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine Wire.SepWPp.mono_pre ?_
      (hnext (s := s2) (sigCap := sigCap) (sigPtr := sigPtr) (sigBs := sigBs) (out := out)
        ⟨hsp2_eq, hsp2_align, hcrl2, by simpa [htr2, arm64_norm] using htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2 hx20_2 hx21_2)
    unfold spkEpilogueTail
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    have hb4 : s0.sp - 224#64 - BitVec.ofNat 64 (SpqrV1.Varint.skipField3Stack 100) = s0.sp - 18240#64 := by
      change s0.sp - 224#64 - 18016#64 = s0.sp - 18240#64; bv_omega
    apply entails_of_eq; rw [hstack, hb1, hb2, hb3, hb4]; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl

theorem freePub_680_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {x : DecodeGhost} {s0 s : State}
    {pubCap pubPtr privCap privPtr sigCap sigPtr : BitVec 64}
    {pubBs privBs sigBs : List (BitVec 8)}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_freePub)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = pubCap) (hx0 : s.readReg64 .x0 = pubPtr)
    (hx22 : s.readReg64 .x22 = privCap) (hx23 : s.readReg64 .x23 = privPtr)
    (hx20 : s.readReg64 .x20 = sigCap) (hx21 : s.readReg64 .x21 = sigPtr) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (vecU8Buf A pubCap pubPtr pubBs ∗ vecU8Buf A privCap privPtr privBs ∗
        vecU8Buf A sigCap sigPtr sigBs ∗ spkEpilogueTail A s0 x out)
      (spkRetPost spkCfgLegacy A s0 x out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx24, hx19, hsaved⟩
  have hnext := @freePriv_696_placed_wp _ A H hH x s0
  by_cases hcap : pubCap = 0#64
  · subst hcap
    refine Wire.SepWPp.mono_pre (sepConj_mono_left (spk_vecU8Buf_zero_elim A pubPtr pubBs)) ?_
    rw [emp_sepConj]
    have h8 : s.readReg64 (Reg.gpr 8#5) = 0#64 := hx8
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_freePubRet) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    exact hnext (privCap := privCap) (privPtr := privPtr) (sigCap := sigCap) (sigPtr := sigPtr)
      (privBs := privBs) (sigBs := sigBs) (out := out)
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hcrl1, by simp [htr, arm64_norm], by simp [hx24, arm64_norm], by simp [hx19, arm64_norm],
       ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
        by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [hx22, arm64_norm]) (by simp [hx23, arm64_norm])
      (by simp [hx20, arm64_norm]) (by simp [hx21, arm64_norm])
  · refine Wire.SepWPp.mono_pre (sepConj_mono_left (vecU8Buf_dealloc A pubCap pubPtr pubBs hcap)) ?_
    unfold spkEpilogueTail; simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun _ => ?_
    have hcall := spk_dealloc_placed_ok hH
    have hstack := stackAt_sub_split (s0.sp - 224#64) allocHookStack (SpqrV1.Varint.skipField3Stack 100)
    have h8 : s.readReg64 (Reg.gpr 8#5) = pubCap := hx8
    have h0 : s.readReg64 (Reg.gpr 0#5) = pubPtr := hx0
    have hbeq : (pubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    refine sepWPp_of_sepWP_lscro hcrl (mid := lsρ lsRustDeallocSym) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [lsρ, lsRustDeallocSym, arm64_norm])
      (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine spk_call_noPanic_lscro (pubPtr, pubCap.toNat, 1) hcall
      (by simp [lsρ, lsRustDeallocSym, arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
      (ret_pc := (blkPl_562).base + spkOff_freePubRet) (by simp [arm64_norm])
      (T := A.pool ∗ A.live pubPtr pubCap.toNat 1 ∗ memRegion pubPtr pubCap.toNat ∗
        stackAt (s0.sp - 224#64) allocHookStack)
      (φ := True)
      (by simp [rustDeallocSpec, hsp_eq, h8, h0, hbeq, arm64_norm]) trivial
      (by rw [hstack]; sep_focus) ?_
    clear hcall
    intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
    dsimp only [rustDeallocSpec]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    have hsp2_eq : s2.sp = s0.sp - 224#64 := by simpa [hsp_eq, arm64_norm] using hsp2
    have hx19_2 : s2.readReg64 .x19 = x.ret := by simpa [hx19, arm64_norm] using hcs2.1
    have hx20_2 : s2.readReg64 .x20 = sigCap := by simpa [hx20, hbeq, arm64_norm] using hcs2.2.1
    have hx21_2 : s2.readReg64 .x21 = sigPtr := by simpa [hx21, hbeq, arm64_norm] using hcs2.2.2.1
    have hx22_2 : s2.readReg64 .x22 = privCap := by simpa [hx22, hbeq, arm64_norm] using hcs2.2.2.2.1
    have hx23_2 : s2.readReg64 .x23 = privPtr := by simpa [hx23, hbeq, arm64_norm] using hcs2.2.2.2.2.1
    have hx24_2 : s2.readReg64 .x24 = s0.sp - 224#64 + 16#64 :=
      by simpa [hx24, arm64_norm] using hcs2.2.2.2.2.2.1
    have hsaved2 : SpkSavedRegs s0 s2 :=
      ⟨by simpa [hsaved.x25, arm64_norm] using hcs2.2.2.2.2.2.2.1,
       by simpa [hsaved.x26, arm64_norm] using hcs2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x27, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.1,
       by simpa [hsaved.x28, arm64_norm] using hcs2.2.2.2.2.2.2.2.2.2.1⟩
    refine Wire.SepWPp.mono_pre ?_
      (hnext (s := s2) (privCap := privCap) (privPtr := privPtr) (sigCap := sigCap) (sigPtr := sigPtr)
        (privBs := privBs) (sigBs := sigBs) (out := out)
        ⟨hsp2_eq, hsp2_align, hcrl2, by simpa [htr2, arm64_norm] using htr, hx24_2, hx19_2, hsaved2⟩
        hpc2 hrun2 hx22_2 hx23_2 hx20_2 hx21_2)
    unfold spkEpilogueTail
    have hb1 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
    have hb2 : s0.sp - 224#64 + 104#64 = s0.sp - 120#64 := by bv_omega
    have hb3 : s0.sp - 224#64 + 112#64 = s0.sp - 112#64 := by bv_omega
    have hb4 : s0.sp - 224#64 - BitVec.ofNat 64 (SpqrV1.Varint.skipField3Stack 100) = s0.sp - 18240#64 := by
      change s0.sp - 224#64 - 18016#64 = s0.sp - 18240#64; bv_omega
    apply entails_of_eq; rw [hstack, hb1, hb2, hb3, hb4]; simp only [hsp_eq, hsp2_eq, arm64_norm]; ac_rfl

theorem converge_656_to_ret_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} (hH : SignedHooksPlaced A H)
    {x : DecodeGhost} {s0 s : State}
    {out : Option SignedPreKeyRecordStructure}
    (hst : SpkConvergeStatePlaced s0 (s0.sp - 224#64) x.ret s)
    (hpc : s.pc = (blkPl_562).base + spkOff_converge)
    (hrun : s.status = .Running) :
    Wire.SepWPp (lsProg_562 H) (s0.readReg64 .x30) s
      (spkConvergeMem A (s0.sp - 224#64) x.ret x.bytesA x.bytes out (s.readReg64 .x1) ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (spkRetPost spkCfgLegacy A s0 x out) (tryFromQp s0) := by
  let sp' := s0.sp - 224#64
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hx24, hx19, hsaved⟩
  cases out with
  | some m =>
    unfold spkConvergeMem spkStructOf
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hx1_zero => ?_
    unfold spkStructAt
    rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf, vecU8At_eq_header_buf]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (memRegion_four_entails (sp' + 100#64))
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (spkMemRegion88_unpack x.ret)))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
      Wire.SepWPp.exists_pre fun r2 => Wire.SepWPp.exists_pre fun r3 =>
      Wire.SepWPp.exists_pre fun r4 => Wire.SepWPp.exists_pre fun r5 =>
      Wire.SepWPp.exists_pre fun r6 => Wire.SepWPp.exists_pre fun r7 =>
      Wire.SepWPp.exists_pre fun r8 => Wire.SepWPp.exists_pre fun r9 =>
      Wire.SepWPp.exists_pre fun r10 => Wire.SepWPp.exists_pre fun pad32 => ?_
    have hp96 : ((s0.sp - 224#64 + 96#64) ↦₃₂ m.id) ∗ ((s0.sp - 224#64 + 100#64) ↦₃₂ pad32) =
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ m.id)) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (s0.sp - 224#64 + 96#64) m.id pad32
    have hret := @retOk_800_placed_wp _ A H x s0
    dsimp only [sp'] at hret hpc ⊢
    refine Wire.SepWPp.mono_pre
      (P' := spkRawWords88 (s0.sp - 224#64) g m pad32 ∗
        vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗ vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ∗
        vecU8Buf A g.sig.cap g.sig.ptr m.signature ∗
        memRegion (s0.sp - 224#64) 16 ∗ ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        spkDestWords88 x.ret r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗ stackAt (s0.sp - 224#64) (SpqrV1.Varint.skipField3Stack 100) ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (by
        dsimp only [vecHeader, spkRawWords88, spkDestWords88]
        rw [← sepConj_assoc ((s0.sp - 224#64 + 96#64) ↦₃₂ m.id), hp96]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; apply entails_of_eq; ac_rfl) ?_
    unfold spkRawWords88 spkDestWords88; simp only [sepConj_assoc]
    have h1 : s.readReg64 (Reg.gpr 1#5) = 0#64 := hx1_zero
    have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
    have h24 : s.readReg64 (Reg.gpr 24#5) = s0.sp - 224#64 + 16#64 := hx24
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_retOk) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (hret (out := some m)
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm], by simp [h24, arm64_norm], by simp [h19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]))
    unfold spkEpilogueTail
    have h88 := spkRawWords88_pack (s0.sp - 224#64) g m pad32
    unfold spkRawWords88 at h88
    have hres := spkOk88_intro A g x.ret m pad32 rfl
    refine Entails.trans ?_
      (sepConj_mono hres (sepConj_mono_right (sepConj_mono_left h88)))
    apply entails_of_eq; simp only [hsp_eq, h19, h24, arm64_norm]; try ac_rfl
  | none =>
    unfold spkConvergeMem
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun mErr => Wire.SepWPp.pure_pre fun hx1_nz => ?_
    unfold spkStructOf
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun g => ?_
    unfold spkStructAt
    rw [vecU8At_eq_header_buf, vecU8At_eq_header_buf, vecU8At_eq_header_buf]
    simp only [sepConj_assoc]
    refine Wire.SepWPp.mono_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono (memRegion_four_entails (sp' + 100#64))
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (spkMemRegion88_err_unpack x.ret))))))))))))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun r0 => Wire.SepWPp.exists_pre fun r1 =>
      Wire.SepWPp.exists_pre fun pad32 => ?_
    have hp96 : ((s0.sp - 224#64 + 96#64) ↦₃₂ mErr.id) ∗ ((s0.sp - 224#64 + 100#64) ↦₃₂ pad32) =
        ((s0.sp - 224#64 + 96#64) ↦₆₄ (pad32 ++ mErr.id)) := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (s0.sp - 224#64 + 96#64) mErr.id pad32
    have hfree := @freePub_680_placed_wp _ A H hH x s0
    dsimp only [sp'] at hfree hpc ⊢
    refine Wire.SepWPp.mono_pre
      (P' := spkRawWords88 (s0.sp - 224#64) g mErr pad32 ∗
        vecU8Buf A g.pub.cap g.pub.ptr mErr.publicKey ∗ vecU8Buf A g.priv.cap g.priv.ptr mErr.privateKey ∗
        vecU8Buf A g.sig.cap g.sig.ptr mErr.signature ∗ decodeErrorAt A (s.readReg64 .x1) ∗
        memRegion (s0.sp - 224#64) 16 ∗ ((s0.sp - 224#64 + 104#64) ↦₆₄ (s0.sp - 224#64)) ∗
        memRegion (s0.sp - 224#64 + 112#64) 48 ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ memRegion (x.ret + 16#64) 72 ∗
        (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗ stackAt (s0.sp - 224#64) (SpqrV1.Varint.skipField3Stack 100) ∗
        spkCalleeSavedAt (s0.sp - 224#64) s0)
      (by dsimp only [vecHeader, spkRawWords88]; rw [← sepConj_assoc ((s0.sp - 224#64 + 96#64) ↦₃₂ mErr.id), hp96]
          simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; apply entails_of_eq; ac_rfl) ?_
    unfold spkRawWords88
    let err := s.readReg64 .x1
    have h1 : s.readReg64 (Reg.gpr 1#5) = err := rfl
    have h19 : s.readReg64 (Reg.gpr 19#5) = x.ret := hx19
    have hbeq : (err == 0#64) = false := beq_eq_false_iff_ne.mpr hx1_nz
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_562).base + spkOff_freePub) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (hfree (pubCap := g.pub.cap) (pubPtr := g.pub.ptr) (privCap := g.priv.cap) (privPtr := g.priv.ptr)
        (sigCap := g.sig.cap) (sigPtr := g.sig.ptr)
        (pubBs := mErr.publicKey) (privBs := mErr.privateKey) (sigBs := mErr.signature) (out := none)
        ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
         hcrl1, by simp [htr, arm64_norm], by simp [hx24, arm64_norm], by simp [h19, arm64_norm],
         ⟨by simpa [arm64_norm] using hsaved.x25, by simpa [arm64_norm] using hsaved.x26,
          by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]))
    unfold spkEpilogueTail
    have h88 := spkRawWords88_pack (s0.sp - 224#64) g mErr pad32
    unfold spkRawWords88 at h88
    have hres := spkErr88_intro A x.ret err (out := none) rfl
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hres (sepConj_mono_right (sepConj_mono_left h88))))))
    apply entails_of_eq; dsimp only [errTag, err]; simp only [hsp_eq, h19, arm64_norm]; try ac_rfl

end Placed

end CryptoVerification.RecordCodecsBinary.SignedPreKeyDecode.Helpers
