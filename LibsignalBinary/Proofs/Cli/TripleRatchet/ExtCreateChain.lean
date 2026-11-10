/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract

/-!
# `PrivateKey::calculate_agreement` and `RootKey::create_chain` at `extHookStack`

Proves `CalculateAgreementOkX` (`subStack = 16432` B) and `CreateChainOkX` (`callStack = 17360` B)
on `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtCreateChain

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Keys

abbrev agreeHookStackX : Nat := 48 + extHookStack

theorem stackAt_agreeHookX_split (sp : BitVec 64) :
    stackAt sp agreeHookStackX =
      memRegion (sp - 16432#64) 48 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 16432#64) 16432 =
    memRegion (sp - 16432#64) 48 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 16432#64) (n := 48) (k := 16384)
    (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

theorem stackAt_agreeHookX_ctEq (sp : BitVec 64) :
    stackAt sp agreeHookStackX =
      stackFrameFor libsignalSessionImage ctEqName sp ∗
        stackAt (sp - 48#64) extHookStack := by
  change memRegion (sp - 16432#64) 16432 =
    stackFrameFor libsignalSessionImage ctEqName sp ∗ memRegion (sp - 48#64 - 16384#64) 16384
  rw [← memRegion_48_eq_stackFrameFor_ct_eq sp,
    ProofLib.memRegion_split' (b := sp - 16432#64) (n := 16384) (k := 48)
      (b' := sp - 48#64) rfl (by bv_omega) (by decide)]
  have h : sp - 48#64 - 16384#64 = sp - 16432#64 := by bv_omega
  rw [h, sepConj_comm]

theorem dhCallAtX_of {img : Obj.Image} {X : Ratchet.X25519Fn} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry ((withStack (diffieHellmanSpec X) extHookStack).inImage img)) :
    subroutine_ok prog entry (dhCallSpecAt img X agreeHookStackX) := by
  refine subroutine_ok_map h ?_
  rintro ⟨secA, sec, pubA, pub, ret, sp⟩ R s0 hpre
  dsimp only [dhCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx8, hsp⟩, hpre⟩
  subst hsp
  rw [stackAt_agreeHookX_split] at hpre
  refine ⟨(secA, sec, pubA, pub, ret), memRegion (s0.sp - 16432#64) 48 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.inImage, withStack, diffieHellmanSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx8⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [Spec.inImage, withStack, diffieHellmanSpec, dhCallSpecAt] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [stackAt_agreeHookX_split]
    exact ⟨htr, by ac_nf at hpost ⊢⟩

theorem zeroizeCallAtX_of {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry ((withStack zeroizeSecretSpec extHookStack).inImage img)) :
    subroutine_ok prog entry (zeroizeCallSpecAt img agreeHookStackX) := by
  refine subroutine_ok_map h ?_
  rintro ⟨a, sp⟩ R s0 hpre
  dsimp only [zeroizeCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hsp⟩, hpre⟩
  subst hsp
  rw [stackAt_agreeHookX_split] at hpre
  refine ⟨a, memRegion (s0.sp - 16432#64) 48 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.inImage, withStack, zeroizeSecretSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, hx0, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [Spec.inImage, withStack, zeroizeSecretSpec, zeroizeCallSpecAt] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [stackAt_agreeHookX_split]
    exact ⟨htr, by ac_nf at hpost ⊢⟩

theorem shimCallAtX_of {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry ((withStack sessionShimSpec agreeHookStackX).inImage img)) :
    subroutine_ok prog entry (shimCallSpecAt img agreeHookStackX) := by
  refine subroutine_ok_map h ?_
  rintro sp R s0 hpre
  dsimp only [shimCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsp⟩, hpre⟩
  subst hsp
  refine ⟨(), R, ?_, ?_⟩
  · dsimp only [Spec.inImage, withStack, sessionShimSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj, emp_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, hpre⟩
  · intro sf hpost
    dsimp only [Spec.inImage, withStack, sessionShimSpec, shimCallSpecAt] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact hpost

theorem allocCallAtX_of {img : Obj.Image} {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry ((rustAllocSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok prog entry (allocCallSpecAt img A agreeHookStackX) := by
  refine subroutine_ok_map h ?_
  rintro ⟨size, align, sp⟩ R s0 hpre
  dsimp only [allocCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hlay, hsp⟩, hpre⟩
  subst hsp
  rw [stackAt_agreeHookX_split] at hpre
  refine ⟨(size, align), memRegion (s0.sp - 16432#64) 48 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.inImage, rustAllocSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hlay⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [Spec.inImage, rustAllocSpecWithStack, allocCallSpecAt] at hpost ⊢
    rw [stackAt_agreeHookX_split]
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte, sepConj_assoc] at hpost ⊢
      ac_nf at hpost ⊢
    · simp only [h0, ↓reduceIte, sepConj_assoc] at hpost ⊢
      ac_nf at hpost ⊢

theorem ctEqCallAtX_of_ext32 {img : Obj.Image} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (ConsumeMessageKeyTransfer.ctEqSliceROSpecExt.inImage img)) :
    subroutine_ok prog entry (ctEqCallSpecAt img agreeHookStackX) := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [ctEqCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  rw [stackAt_agreeHookX_ctEq sp] at hpre
  refine ⟨(p1, k1, p2, k2, sp), R, ?_, ?_⟩
  · dsimp only [Spec.inImage, ConsumeMessageKeyTransfer.ctEqSliceROSpecExt,
      ConsumeMessageKeyTransfer.ctEqName, ctEqName,
      FindReceiverChainIndex.extHookStack32, extHookStack] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hsp, hk1, hk2⟩, hpre⟩
  · intro sf hpost
    dsimp only [Spec.inImage, ConsumeMessageKeyTransfer.ctEqSliceROSpecExt, ctEqCallSpecAt,
      ConsumeMessageKeyTransfer.ctEqName, ctEqName,
      FindReceiverChainIndex.extHookStack32, extHookStack] at hpost ⊢
    rw [stackAt_agreeHookX_ctEq sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨hres, htr⟩, hpost⟩
    refine ⟨⟨?_, htr⟩, hpost⟩
    have h8 : (sf.readReg64 .x0).setWidth 8 = ((sf.readReg64 .x0).setWidth 32).setWidth 8 :=
      (BitVec.setWidth_setWidth_of_le (sf.readReg64 .x0) (by decide : 8 ≤ 32)).symm
    rw [h8, hres]
    split <;> rfl

abbrev calculateAgreementStackExt' : Nat := 160 + agreeHookStackX
abbrev createChainStackExt' : Nat := 576 + extractStackExt

theorem calculateAgreement_ok_of_ctEq_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsWeak img C A ext)
    (hct : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ctEqName)
      (ConsumeMessageKeyTransfer.ctEqSliceROSpecExt.inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementName)
      ((calculateAgreementSpecAt C.X A agreeHookStackX).inImage img) := by
  have hct_rel : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" -
          ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")))
      (ConsumeMessageKeyTransfer.ctEqSliceROSpecExt.inImage img) := by
    rw [← Program.fnAddr_rel
      (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement")
      (ls_lemma% fnOff "<[u8] as subtle::ConstantTimeEq>::ct_eq") rfl]
    exact hct
  exact calculateAgreement_ok_of_hooks_gen (subStack := agreeHookStackX) (by decide) himg
    (dhCallAtX_of (sub_ok_at_rebase (name := calculateAgreementName) (callee := dhName)
      (k := num% (ls_off% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [(ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement"),
            (ls_stub% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman")]) hC.dh))
    (zeroizeCallAtX_of (sub_ok_at_rebase (name := calculateAgreementName) (callee := sharedDropName)
      (k := num% (ls_off% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [(ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement"),
            (ls_stub% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop")]) hC.shared_drop))
    (ctEqCallAtX_of_ext32 hct_rel)
    (shimCallAtX_of (sub_ok_at_rebase (name := calculateAgreementName)
      (callee := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [(ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement"),
            (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
      (hC.shim agreeHookStackX (by decide) (by decide))))
    (allocCallAtX_of (sub_ok_at_rebase (name := calculateAgreementName)
      (callee := "__rustc::__rust_alloc")
      (k := num% (ls_off% "__rustc::__rust_alloc" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [(ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement"),
            (ls_stub% "__rustc::__rust_alloc")]) hC.alloc))
    (zeroizeCallAtX_of (sub_ok_at_rebase (name := calculateAgreementName) (callee := staticDropName)
      (k := num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" -
        ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement"))
      (by rw [(ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement"),
            (ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")]) hC.static_drop))

theorem stackAt_extract_agree_split (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 768 ∗ stackAt sp calculateAgreementStackExt' := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 768 ∗ memRegion (sp - 16592#64) 16592
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 768) (k := 16592)
    (b' := sp - 16592#64) rfl (by bv_omega) (by decide)

theorem stackAt_extract_expand_split (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 336 ∗ stackAt sp expandMultiInfoStackExt := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 336 ∗ memRegion (sp - 17024#64) 17024
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 336) (k := 17024)
    (b' := sp - 17024#64) rfl (by bv_omega) (by decide)

theorem stackAt_extract_extHook_split (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 976 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 976 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 976) (k := 16384)
    (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

theorem calculateAgreementCallExt_ok_at {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {H : String → Option (State → State)}
    (hag : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr calculateAgreementName)
      ((calculateAgreementSpecAt C.X A agreeHookStackX).inImage img))
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement")) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr name + BitVec.ofNat 64 k)
      ((calculateAgreementCallSpecAt C.X A extractStackExt).inImage img) := by
  have hrel := subroutine_ok_rel_rebase hag
    (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement") hfn hk
  refine subroutine_ok_outcome_intro fun ⟨ourA, our, theirA, their, ret, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, calculateAgreementCallSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hL, ⟨hx0, hx1, hx8, hsp_eq⟩, hpre⟩
  subst hsp_eq
  rw [stackAt_extract_agree_split s0.sp] at hpre
  have hpre' : s0.mem ⊨ ((calculateAgreementSpecAt C.X A agreeHookStackX).inImage img).pre
      ⟨ourA, our, theirA, their, ret⟩ s0 ∗ (memRegion (s0.sp - 17360#64) 768 ∗ R) := by
    dsimp only [Spec.inImage, calculateAgreementSpecAt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hL, ⟨hx0, hx1, hx8⟩, by ac_nf at hpre ⊢⟩
  refine hrel.mono_outcome ⟨ourA, our, theirA, their, ret⟩ (memRegion (s0.sp - 17360#64) 768 ∗ R)
      s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, calculateAgreementSpecAt, calculateAgreementCallSpecAt] at hq ⊢
    rw [stackAt_extract_agree_split s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    exact ⟨htr, by ac_nf at hq ⊢⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [Spec.inImage, calculateAgreementSpecAt, calculateAgreementCallSpecAt] at hq ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hpan_pure, hq⟩
    refine ⟨hpan_pure, ?_⟩
    have hE : (anyHeap ∗ (memRegion (s0.sp - 17360#64) 768 ∗ R)) ⊢ (anyHeap ∗ R) := by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (entails_anyHeap _)
    exact Satisfies.mono hE hq
  · dsimp only [Spec.inImage, calculateAgreementSpecAt] at hq
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact False.elim hq.1
  · dsimp only [Spec.inImage, calculateAgreementSpecAt] at hoom
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hoom
    exact False.elim hoom.2.1

theorem extractKey32StackExt_ok_at {img : Obj.Image} {C : Crypto}
    {H : String → Option (State → State)}
    (hext : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr extractName)
      ((extractSpecExt C.F).inImage img))
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr name + BitVec.ofNat 64 k)
      (extractKey32StackSpecAt C.F img extractStackExt) := by
  have hrel := subroutine_ok_rel_rebase hext
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") hfn hk
  refine subroutine_ok_map hrel ?_
  rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractKey32StackSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp, hsalt_ne, hikm⟩, hpre⟩
  subst hsp
  refine ⟨⟨ret, saltA, some (Ratchet.keyToBytesVec32 rk), ikmA, ikm⟩, R, ?_, ?_⟩
  · dsimp only [Spec.inImage, extractSpecExt, optSaltAt]
    rw [eq_true hsalt_ne, pure_true, emp_sepConj, pointsTo_keyVec_toList]
    simp only [Option.isSome_some, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_and,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx2, hx3, hx4, hikm⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [Spec.inImage, extractSpecExt, ExtractGhost.prk, optSaltAt,
      extractKey32StackSpecAt] at hpost ⊢
    rw [eq_true hsalt_ne, pure_true, emp_sepConj, pointsTo_keyVec_toList] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by ac_nf at hpost ⊢⟩

theorem expandCellsStackExt_ok_at {img : Obj.Image} {C : Crypto}
    {H : String → Option (State → State)}
    (hexp : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr expandMultiInfoName)
      ((expandMultiInfoSpecExt C.F).inImage img))
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info"))
    (n : Nat) (hn : 8 * n ≤ 2 ^ 64) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr name + BitVec.ofNat 64 k)
      (expandCellsStackSpecAt C.F img n extractStackExt) := by
  have hrel := subroutine_ok_rel_rebase hexp
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info") hfn hk
  refine subroutine_ok_map hrel ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [expandCellsStackSpecAt] at hpre
  rw [stackAt_extract_expand_split sp, ← ProofLib.memRegion_cells okmA n hn] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hinfo, hlen⟩, hpre⟩
  subst hsp
  refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, 8 * n⟩,
    memRegion (s0.sp - 17360#64) 336 ∗ R, ?_, ?_⟩
  · dsimp only [Spec.inImage, expandMultiInfoSpecExt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx2, hx3, hprk, hinfo, hlen⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [Spec.inImage, expandMultiInfoSpecExt, expandCellsStackSpecAt] at hpost ⊢
    rw [stackAt_extract_expand_split s0.sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    have hE := sepConj_mono_left
      (Q := (infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand C.F prk info (8 * n)) ∗
        stackAt s0.sp expandMultiInfoStackExt ∗ (memRegion (s0.sp - 17360#64) 336 ∗ R))
      (hmacCore_entails_cells C.F hkdfA prk)
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    simp only [sepConj_assoc] at hpost ⊢
    exact ⟨htr, by ac_nf at hpost ⊢⟩

theorem deallocStackExt_ok_at {A : RustAlloc} {img : Obj.Image}
    {H : String → Option (State → State)} {addr : BitVec 64}
    (hd : subroutine_ok (libsignalSessionCode.rebase img.base H) addr
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H) addr
      (deallocStackSpecAt A img extractStackExt) := by
  refine subroutine_ok_map (deallocExtStack_of_rustDeallocExtern_rebase hd) ?_
  rintro ⟨p, size, align, sp⟩ R s0 hpre
  dsimp only [deallocStackSpecAt] at hpre
  rw [stackAt_extract_extHook_split sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨(p, size, align, sp), memRegion (sp - 17360#64) 976 ∗ R, ?_, ?_⟩
  · dsimp only [deallocExtStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [deallocExtStackSpec, deallocStackSpecAt] at hpost ⊢
    rw [stackAt_extract_extHook_split sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by ac_nf at hpost ⊢⟩

theorem createChain_ok_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2ContractsWeak img C A ext)
    (hHkdf : HkdfContractsExt img C.F ext)
    (hct : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ctEqName)
      (ConsumeMessageKeyTransfer.ctEqSliceROSpecExt.inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName)
      ((createChainSpecAt C A extractStackExt).inImage img) := by
  have hfn : libsignalSessionCode.fnOff createChainName =
      num% (ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain") :=
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")
  have hag := calculateAgreementCallExt_ok_at (calculateAgreement_ok_of_ctEq_x himg hC hct) hfn
    (k := num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")) (by decide)
  have hext_c := extractKey32StackExt_ok_at (extract_ok_ext' img C ext himg hHkdf) hfn
    (k := num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")) (by decide)
  have hexp_c := expandCellsStackExt_ok_at (expand_multi_info_ok_ext' img C ext hHkdf) hfn
    (k := num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")) (by decide) 8 (by decide)
  have hdealloc_c := deallocStackExt_ok_at (sub_ok_at_rebase (name := createChainName)
    (callee := "__rustc::__rust_dealloc")
    (k := num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
    (by rw [(ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"),
          (ls_stub% "__rustc::__rust_dealloc")]) hC.dealloc)
  exact createChain_ok_of_hooks_gen (callStack := extractStackExt) (by decide)
    himg hag hext_c hexp_c hdealloc_c

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtCreateChain
