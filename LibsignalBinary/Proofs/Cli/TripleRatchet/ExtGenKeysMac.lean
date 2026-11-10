/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
public import LibsignalBinary.Proofs.TripleRatchet.Statements
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeys
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

/-!
# Stacked `generate_keys`, `compute_mac`, and `verify_mac_with_addresses`

Proves stacked `extHookStack` contracts for `SignalMessage::compute_mac` (`17424` B),
`SignalMessage::verify_mac_with_addresses` (`17712` B), and `MessageKeyGenerator::generate_keys`
(`17856` B).
-/

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtGenKeysMac

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.SignalSession

theorem computeMac_ok_stacked_ext32
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hHkdf : HkdfContractsExt img C.F ext)
    (h_comp : HookSat ext compress256Name (CliExt.compress256Spec C)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr computeMacName)
      ((Mac.VerifyMacWithAddresses.computeMacSpecWithStack C.F A Statements.computeMacStackExt32).inImage img) :=
  Statements.computeMac_subroutine_ok_stacked_ext32 img C A ext hA h_comp
    (new_from_slice_ok_ext' img C ext himg hHkdf)

theorem verifyMacWithAddresses_ok_stacked_ext32
    (img : Obj.Image) (himg : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsX img A ext)
    (hHkdf : HkdfContractsExt img C.F ext)
    (h_bb : HookSat ext blackBoxName CliExt.blackBoxSpec)
    (h_comp : HookSat ext compress256Name (CliExt.compress256Spec C)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr verifyMacWithAddressesName)
      ((Mac.VerifyMacWithAddresses.verifyMacWithAddressesSpecWithStack img C.F A uuidTryParse
        Statements.computeMacStackExt32).inImage img) :=
  Statements.verifyMacWithAddresses_subroutine_ok_stacked_ext32 img himg C A ext hA h_bb h_comp
    (new_from_slice_ok_ext' img C ext himg hHkdf)

/-! ## Stacked `MessageKeyGenerator::generate_keys` (`496 + extractStackExt = 17856` B) -/

/-- Stack depth of `MessageKeyGenerator::generate_keys` when calling stacked `Hkdf::extract`
(`extractStackExt = 17360` B below its 496-byte frame, total `17856` B). -/
abbrev generateKeysStackExt : Nat := 496 + extractStackExt

def generateKeysSpecExt (F : ShaCompress) (A : RustAlloc) : Spec GenerateKeysGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.genA ∧ s.readReg64 .x1 = x.pqrKeyA ∧ s.readReg64 .x8 = x.ret ∧
      x.g.seed.length = 32⌝ ∗
      mkgAt A x.genA x.g ∗ spqrRecvKeyAt A x.pqrKeyA x.pqrKey ∗ memRegion x.ret 84 ∗
      A.pool ∗ stackAt s.sp generateKeysStackExt
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.genA 40 ∗ memRegion x.pqrKeyA 24 ∗
      messageKeysAt x.ret (x.g.generateKeys F x.pqrKey) ∗
      A.pool ∗ stackAt s0.sp generateKeysStackExt

def GenerateKeysOkExtStacked (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr generateKeysName)
    ((generateKeysSpecExt C.F A).inImage img)

private theorem rodata_whisperMessageKeys {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} (hro : img.RoDataLoaded m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "WhisperMessageKeys")) ↦ᵣ whisperMessageKeys) ∗ P := by
  have hsec : (num% (ls_str% "WhisperMessageKeys"), 18) ∈ libsignalSessionImage.roData := by decide
  have ⟨h1, h2⟩ := rodata_readBytes_disjoint himg
    (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40)
      (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl hsec (by decide) (by decide) (by decide +kernel) (by rfl_kernel) m hro
  have hbytes :
      (libsignalSessionImage.data.drop
        (num% (ls_str% "WhisperMessageKeys") -
          num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40)
            (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 18 =
      whisperMessageKeys := by rfl_kernel
  rw [hbytes] at h2
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem fnFrame_split_generateKeysExt_pre (sp : BitVec 64) :
    stackAt sp generateKeysStackExt =
      stackAt (sp - 496#64) extractStackExt ∗
        ProofLib.cells (sp - 496#64) 10 ∗ ProofLib.cells (sp - 416#64) 4 ∗
        ProofLib.cells (sp - 384#64) 14 ∗ memRegion (sp - 272#64) 176 ∗
        ProofLib.cells (sp - 96#64) 12 := by
  change memRegion (sp - BitVec.ofNat 64 17856) 17856 =
    memRegion (sp - 496#64 - BitVec.ofNat 64 17360) 17360 ∗
      ProofLib.cells (sp - 496#64) 10 ∗ ProofLib.cells (sp - 416#64) 4 ∗
      ProofLib.cells (sp - 384#64) 14 ∗ memRegion (sp - 272#64) 176 ∗
      ProofLib.cells (sp - 96#64) 12
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17856) (n := 17360) (k := 496)
      (b' := sp - 496#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 32) (k := 384) (b' := sp - 384#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 384#64) (n := 112) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 176) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = ProofLib.cells (sp - 496#64) 10),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 416#64) 4 (by decide) :
      memRegion (sp - 416#64) 32 = ProofLib.cells (sp - 416#64) 4),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 384#64) 14 (by decide) :
      memRegion (sp - 384#64) 112 = ProofLib.cells (sp - 384#64) 14),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = ProofLib.cells (sp - 96#64) 12)]
  have hsub : sp - 496#64 - BitVec.ofNat 64 17360 = sp - BitVec.ofNat 64 17856 := by bv_kernel
  rw [hsub]

theorem fnFrame_split_generateKeysExt_post (sp : BitVec 64) :
    stackAt sp generateKeysStackExt =
      stackAt (sp - 496#64) extractStackExt ∗
        ProofLib.cells (sp - 496#64) 10 ∗ ProofLib.cells (sp - 416#64) 8 ∗
        memRegion (sp - 352#64) 80 ∗ ProofLib.cells (sp - 272#64) 4 ∗
        ProofLib.cells (sp - 240#64) 4 ∗ ProofLib.cells (sp - 208#64) 14 ∗
        ProofLib.cells (sp - 96#64) 12 := by
  change memRegion (sp - BitVec.ofNat 64 17856) 17856 =
    memRegion (sp - 496#64 - BitVec.ofNat 64 17360) 17360 ∗
      ProofLib.cells (sp - 496#64) 10 ∗ ProofLib.cells (sp - 416#64) 8 ∗
      memRegion (sp - 352#64) 80 ∗ ProofLib.cells (sp - 272#64) 4 ∗
      ProofLib.cells (sp - 240#64) 4 ∗ ProofLib.cells (sp - 208#64) 14 ∗
      ProofLib.cells (sp - 96#64) 12
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 17856) (n := 17360) (k := 496)
      (b' := sp - 496#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 496#64) (n := 80) (k := 416) (b' := sp - 416#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 416#64) (n := 64) (k := 352) (b' := sp - 352#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 352#64) (n := 80) (k := 272) (b' := sp - 272#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 272#64) (n := 32) (k := 240) (b' := sp - 240#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 240#64) (n := 32) (k := 208) (b' := sp - 208#64) rfl
      (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 208#64) (n := 112) (k := 96) (b' := sp - 96#64) rfl
      (by bv_omega) (by decide),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 496#64) 10 (by decide) :
      memRegion (sp - 496#64) 80 = ProofLib.cells (sp - 496#64) 10),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 416#64) 8 (by decide) :
      memRegion (sp - 416#64) 64 = ProofLib.cells (sp - 416#64) 8),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 272#64) 4 (by decide) :
      memRegion (sp - 272#64) 32 = ProofLib.cells (sp - 272#64) 4),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 240#64) 4 (by decide) :
      memRegion (sp - 240#64) 32 = ProofLib.cells (sp - 240#64) 4),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 208#64) 14 (by decide) :
      memRegion (sp - 208#64) 112 = ProofLib.cells (sp - 208#64) 14),
    (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (sp - 96#64) 12 (by decide) :
      memRegion (sp - 96#64) 96 = ProofLib.cells (sp - 96#64) 12)]
  have hsub : sp - 496#64 - BitVec.ofNat 64 17360 = sp - BitVec.ofNat 64 17856 := by bv_kernel
  rw [hsub]

section GenerateKeysStacked

open CryptoVerification.LibsignalTripleRatchet.Keys.GenerateKeysFacts

attribute [-arm64_norm]
  _root_.CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  _root_.CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  _root_.CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496
attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_sub_lit bv_sub_add_lit bv_add_neg64
attribute [local simp, local arm64_norm] hkdfExtract_length' whisperMessageKeys_length lt_32_18
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

private def extractSomeStackExtSpec (F : ShaCompress) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, saltA, sv, ikmA, ikm, sp) s =>
    ⌜FrozenInv img s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = saltA ∧
      s.readReg64 .x2 = 32#64 ∧ s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ saltA ≠ 0#64 ∧ ikm.length = 32⌝ ∗
      memRegion ret 176 ∗ (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp extractStackExt
  post := fun (ret, saltA, sv, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F (some sv) ikm) ∗
      hmacCoreAt F (ret + 32#64) (hkdfExtract F (some sv) ikm) [] ∗
      (saltA ↦ₛ sv.toList) ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp extractStackExt

private def extractNoneStackExtSpec (F : ShaCompress) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜FrozenInv img s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ ikm.length = 32⌝ ∗
      memRegion ret 176 ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp extractStackExt
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F none ikm) ∗
      hmacCoreAt F (ret + 32#64) (hkdfExtract F none ikm) [] ∗
      (ikmA ↦ₛ ikm) ∗
      stackAt sp extractStackExt

private def extractEmptyStackExtSpec (F : ShaCompress) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (ret, ikmA, ikm, sp) s =>
    ⌜FrozenInv img s ∧ s.readReg64 .x0 = ret ∧ s.readReg64 .x2 = 0#64 ∧
      s.readReg64 .x3 = ikmA ∧ s.readReg64 .x4 = 32#64 ∧
      s.sp = sp ∧ ikm.length = 32⌝ ∗
      memRegion ret 176 ∗ (ikmA ↦ₛ ikm) ∗
      stackAt sp extractStackExt
  post := fun (ret, ikmA, ikm, sp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (ret ↦ₛ hkdfExtract F none ikm) ∗
      hmacCoreAt F (ret + 32#64) (hkdfExtract F none ikm) [] ∗
      (ikmA ↦ₛ ikm) ∗
      stackAt sp extractStackExt

private theorem extractSomeStackExt_ok_at_rebase {img : Obj.Image} {C : Crypto}
    {H : String → Option (State → State)}
    (hext : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr extractName)
      ((extractSpecExt C.F).inImage img))
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr name + BitVec.ofNat 64 k)
      (extractSomeStackExtSpec C.F img) := by
  have hrel := subroutine_ok_rel_rebase hext
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") hfn hk
  refine subroutine_ok_map hrel ?_
  rintro ⟨ret, saltA, sv, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractSomeStackExtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp, hsalt_ne, hikm⟩, hpre⟩
  subst hsp
  refine ⟨⟨ret, saltA, some sv, ikmA, ikm⟩, R, ?_, ?_⟩
  · dsimp only [Spec.inImage, extractSpecExt, optSaltAt]
    rw [eq_true hsalt_ne, pure_true, emp_sepConj]
    simp only [Option.isSome_some, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_and,
      sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx2, hx3, hx4, hikm⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [Spec.inImage, extractSpecExt, ExtractGhost.prk, optSaltAt,
      extractSomeStackExtSpec] at hpost ⊢
    rw [eq_true hsalt_ne, pure_true, emp_sepConj] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by ac_nf at hpost ⊢⟩

private theorem extractNoneStackExt_ok_at_rebase {img : Obj.Image} {C : Crypto}
    {H : String → Option (State → State)}
    (hext : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr extractName)
      ((extractSpecExt C.F).inImage img))
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr name + BitVec.ofNat 64 k)
      (extractNoneStackExtSpec C.F img) := by
  have hrel := subroutine_ok_rel_rebase hext
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") hfn hk
  refine subroutine_ok_map hrel ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractNoneStackExtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx3, hx4, hsp, hikm⟩, hpre⟩
  subst hsp
  refine ⟨⟨ret, 0#64, none, ikmA, ikm⟩, R, ?_, ?_⟩
  · dsimp only [Spec.inImage, extractSpecExt, optSaltAt]
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const, true_or,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx3, hx4, hikm⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [Spec.inImage, extractSpecExt, ExtractGhost.prk, optSaltAt,
      extractNoneStackExtSpec] at hpost ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by ac_nf at hpost ⊢⟩

private theorem extractEmptyStackExt_ok_at_rebase {img : Obj.Image} {C : Crypto}
    {H : String → Option (State → State)}
    (hext : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr extractName)
      ((extractSpecExt C.F).inImage img))
    {name : String} {off k : Nat} (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr name + BitVec.ofNat 64 k)
      (extractEmptyStackExtSpec C.F img) := by
  have hrel := subroutine_ok_rel_rebase hext
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") hfn hk
  refine subroutine_ok_map hrel ?_
  rintro ⟨ret, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [extractEmptyStackExtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx2, hx3, hx4, hsp, hikm⟩, hpre⟩
  subst hsp
  refine ⟨⟨ret, s0.readReg64 .x1, none, ikmA, ikm⟩, R, ?_, ?_⟩
  · dsimp only [Spec.inImage, extractSpecExt, optSaltAt]
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, forall_const,
      true_and, emp_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, Or.inr hx2, hx3, hx4, hikm⟩, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [Spec.inImage, extractSpecExt, ExtractGhost.prk, optSaltAt,
      extractEmptyStackExtSpec] at hpost ⊢
    simp only [emp_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by ac_nf at hpost ⊢⟩

private theorem stackAt_extract_expand_split' (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 336 ∗ stackAt sp expandMultiInfoStackExt := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 336 ∗ memRegion (sp - 17024#64) 17024
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 336) (k := 17024)
    (b' := sp - 17024#64) rfl (by bv_omega) (by decide)

private theorem stackAt_extract_extHook_split' (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 976 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 17360#64) 17360 =
    memRegion (sp - 17360#64) 976 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 17360#64) (n := 976) (k := 16384)
    (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

private theorem expandCellsStackExt_ok_at' {img : Obj.Image} {C : Crypto}
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
  rw [stackAt_extract_expand_split' sp, ← ProofLib.memRegion_cells okmA n hn] at hpre
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
    rw [stackAt_extract_expand_split' s0.sp]
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

private theorem deallocStackExt_ok_at' {A : RustAlloc} {img : Obj.Image}
    {H : String → Option (State → State)} {addr : BitVec 64}
    (hd : subroutine_ok (libsignalSessionCode.rebase img.base H) addr
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H) addr
      (deallocStackSpecAt A img extractStackExt) := by
  refine subroutine_ok_map (deallocExtStack_of_rustDeallocExtern_rebase hd) ?_
  rintro ⟨p, size, align, sp⟩ R s0 hpre
  dsimp only [deallocStackSpecAt] at hpre
  rw [stackAt_extract_extHook_split' sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨(p, size, align, sp), memRegion (sp - 17360#64) 976 ∗ R, ?_, ?_⟩
  · dsimp only [deallocExtStackSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [deallocExtStackSpec, deallocStackSpecAt] at hpost ⊢
    rw [stackAt_extract_extHook_split' sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    exact ⟨htr, by ac_nf at hpost ⊢⟩

set_option maxHeartbeats 6000000 in
/-- `<MessageKeyGenerator>::generate_keys` satisfies `(generateKeysSpecExt C.F A).inImage img`
on `libsignalSessionCode.rebase img.base H` when `extract` and `expand_multi_info` use
stacked `extractSpecExt` / `expandMultiInfoSpecExt`. -/
theorem generateKeys_ok_of_contracts_stacked {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {H : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hext : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr extractName)
      ((extractSpecExt C.F).inImage img))
    (hexp : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr expandMultiInfoName)
      ((expandMultiInfoSpecExt C.F).inImage img))
    (hdealloc_raw : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName +
        bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"))
      ((rustDeallocExternSpecWithStack A extHookStack).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName)
      ((generateKeysSpecExt C.F A).inImage img) := by
  have hb := base_aligned_of_loads himg
  refine subroutine_ok_inImage_rodata' (rodata_whisperMessageKeys himg) ?_
  wp_init x s0
  have hfn : libsignalSessionCode.fnOff generateKeysName =
      num% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") :=
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")
  have hexp' := expandCellsStackExt_ok_at' hexp hfn
    (k := num% ((2^64 + ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" -
      ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") % 2^64))
    (by decide) 10 (by decide)
  simp only [expandCellsStackSpecAt, ProofLib.cells, sepConj_emp,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd] at hexp'
  have hdealloc := deallocStackExt_ok_at' hdealloc_raw
  have hadrp : (((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName + 108#64 &&&
      BitVec.ofNat 64 (2 ^ 64 - 4096)) +
      bv% (ls_str% "WhisperMessageKeys" - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new" + 1768))) =
      img.base + bv% (ls_str% "WhisperMessageKeys") := by
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  have hadrp' : (((libsignalSessionCode.rebase img.base H).fnAddr generateKeysName + 108#64 &&&
      BitVec.ofNat 64 (2 ^ 64 - 4096)) +
      bv% (page% (ls_str% "WhisperMessageKeys") - page% (ls_off% "<libsignal_protocol::protocol::SignalMessage>::new" + 1768)) +
      bv% ((ls_str% "WhisperMessageKeys") % 4096)) =
      img.base + bv% (ls_str% "WhisperMessageKeys") := by
    rw [Program.fnAddr_rebase, hfn]
    revert hb; bv_kernel
  code_fetches libsignalSessionCode libsignalSessionBin img.base H hfn
    (num% (ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys")) 444
  have hpc_eq : s0.pc = (libsignalSessionCode.rebase img.base H).fnAddr generateKeysName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  obtain ⟨genA, ⟨seed, counter⟩, pqrKeyA, pqrKey, out⟩ := x
  dsimp only [generateKeysSpecExt] at *
  have hF0 : FrozenInv img s0 := ‹_›
  have hseed_len : seed.length = 32 := ‹_›
  subst ‹s0.readReg64 (.gpr 0#5) = genA› ‹s0.readReg64 (.gpr 1#5) = pqrKeyA›
    ‹s0.readReg64 (.gpr 8#5) = out›
  rw (occs := .pos [1]) [fnFrame_split_generateKeysExt_pre s0.sp]
  rw [memRegion_out_generateKeys (s0.readReg64 (.gpr 8#5))]
  wp_simp_pre_fast [mkgAt, vecU8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  cells_pre_unfold_fast
  wp_extract_exists
  rename_i seed_cap seed_ptr
  apply SepWP.replace_pre
    (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 0#5) + 8#64) seed_cap seed_ptr seed hseed_len)
    (by sep_focus)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_extract_exists
  rename_i hseed
  obtain ⟨hseed_le, hseed_small, hseed_ptr, hseed_cap_ne⟩ := hseed
  have hseed_pos : 0 < seed_cap.toNat := by omega
  have hseed_cap_beq : (seed_cap == 0#64) = false := beq_eq_false_iff_ne.mpr hseed_cap_ne
  rcases pqrKey with _ | sv
  · obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F none seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed none
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, sepConj_assoc]
    wp_extract_exists
    rename_i isNiche
    cases isNiche
    · have hext_empty := extractEmptyStackExt_ok_at_rebase hext hfn
        (k := num% ((2^64 + ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" -
          ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") % 2^64))
        (by decide)
      clear hpc himg hext hexp hdealloc_raw hfn hb
      generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr generateKeysName = entry
      examples_hide_fetches
      wp_simp_pre_fast [Bool.false_eq_true, ↓reduceIte, vecU8, sepConj_assoc]
      wp_extract_exists
      rename_i pqr_cap pqr_ptr
      apply SepWP.replace_pre
        (hPQ := vecU8At_split_nil A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr)
        (by sep_focus)
      wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      wp_extract_exists
      rename_i hpqr
      obtain ⟨hpqr_small, hpqr_ptr⟩ := hpqr
      have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
      have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false :=
        beq_eq_false_iff_ne.mpr hpqr_add1_ne
      apply SepWP.of_sepWP_frozen hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_frozen hF1
      wp_call hext_empty (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      wp_simp_pre_fast [hadrp, hadrp']
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1b
      apply SepWP.of_sepWP_frozen hF1b
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      by_cases hpqr_cap0 : pqr_cap = 0#64
      · subst hpqr_cap0
        wp_simp_pre_fast [↓reduceIte, emp_sepConj, sepConj_emp, sepConj_assoc]
        wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeysExt_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_empty hexp' hdealloc hprk hokm hgood
        wp_done
      · have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap0
        have hpqr_pos : 0 < pqr_cap.toNat :=
          Nat.pos_of_ne_zero fun h0 => hpqr_cap0 (BitVec.eq_of_toNat_eq (by simpa using h0))
        wp_simp_pre_fast [hpqr_cap0, ↓reduceIte, sepConj_assoc]
        apply SepWP.of_sepWP_frozen hF2
        wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
        intro hF3
        wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
        wp_extract_exists
        wp_steps
        apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
          (by sep_focus)
        apply SepWP.replace_pre
          (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
        apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
          (by sep_focus)
        rw [fnFrame_split_generateKeysExt_post s0.sp,
          messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
        wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        clear hext_empty hexp' hdealloc hprk hokm hgood
        wp_done
    · have hext_none := extractNoneStackExt_ok_at_rebase hext hfn
        (k := num% ((2^64 + ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" -
          ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") % 2^64))
        (by decide)
      clear hpc himg hext hexp hdealloc_raw hfn hb
      generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr generateKeysName = entry
      examples_hide_fetches
      wp_simp_pre_fast [↓reduceIte, noneCap,
        (_root_.CryptoVerification.LibsignalTripleRatchet.memRegion_cells (s0.readReg64 (.gpr 1#5) + 8#64) 2 (by decide) :
          memRegion (s0.readReg64 (.gpr 1#5) + 8#64) 16 = ProofLib.cells (s0.readReg64 (.gpr 1#5) + 8#64) 2),
        sepConj_assoc]
      cells_pre_unfold_fast
      wp_extract_exists
      apply SepWP.of_sepWP_frozen hF0
      wp_steps
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1
      apply SepWP.of_sepWP_frozen hF1
      wp_call hext_none (s0.sp - 272#64, seed_ptr, seed, s0.sp - 496#64)
      wp_extract_exists
      rw [hprk (s0.sp - 272#64)]
      apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
        (by sep_focus)
      wp_extract_exists
      rename_i hgood
      wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
      wp_simp_pre_fast [hadrp, hadrp']
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF1b
      apply SepWP.of_sepWP_frozen hF1b
      wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F none seed, s0.sp - 272#64,
        img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys,
        s0.sp - 496#64, s0.sp - 496#64)
      wp_extract_exists
      wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
        BitVec.reduceSub, sepConj_assoc]
      wp_steps
      apply SepWP.replace_pre
        (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap
          hseed_len hseed_le hseed_small)
        (by sep_focus)
      apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
      intro hF2
      wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
      wp_extract_exists
      wp_steps
      apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _)
        (by sep_focus)
      apply SepWP.replace_pre
        (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
      apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _)
        (by sep_focus)
      rw [fnFrame_split_generateKeysExt_post s0.sp,
        messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
      wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
      clear hext_none hexp' hdealloc hprk hokm hgood
      wp_done
  · have hext_some := extractSomeStackExt_ok_at_rebase hext hfn
      (k := num% ((2^64 + ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" -
        ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys") % 2^64))
      (by decide)
    clear hpc himg hext hexp hdealloc_raw hfn hb
    generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr generateKeysName = entry
    examples_hide_fetches
    obtain ⟨p0, p1, p2, p3, -, hprk⟩ :=
      exists_unpack64_of_length_32 (hkdfExtract_length' C.F (some sv) seed)
    obtain ⟨hck_len, hmk_len, hiv_len, hokm_eq⟩ :=
      deriveMessageKeys_eq C.F seed (some sv)
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, hokm⟩ :=
      exists_unpack64_of_length_80 hck_len hmk_len hiv_len
    wp_simp_pre_fast [spqrRecvKeyAt, vecU8, sepConj_assoc]
    wp_extract_exists
    rename_i pqr_cap pqr_ptr
    have hsv_len : sv.toList.length = 32 := List.Vector.toList_length sv
    apply SepWP.replace_pre
      (hPQ := vecU8At_split_32 A (s0.readReg64 (.gpr 1#5)) pqr_cap pqr_ptr sv.toList hsv_len)
      (by sep_focus)
    wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_extract_exists
    rename_i hpqr
    obtain ⟨hpqr_le, hpqr_small, hpqr_ptr, hpqr_cap_ne⟩ := hpqr
    have hpqr_pos : 0 < pqr_cap.toNat := by omega
    have hpqr_add1_ne : pqr_cap + 1#64 ≠ 0#64 := by bv_omega
    have hpqr_add1_beq : ((pqr_cap + 1#64) == 0#64) = false := beq_eq_false_iff_ne.mpr hpqr_add1_ne
    have hpqr_slt : pqr_cap.slt 1#64 = false := slt_one_eq_false_of_small hpqr_small hpqr_cap_ne
    apply SepWP.of_sepWP_frozen hF0
    wp_steps
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF1
    apply SepWP.of_sepWP_frozen hF1
    wp_call hext_some (s0.sp - 272#64, pqr_ptr, sv, seed_ptr, seed, s0.sp - 496#64)
    wp_extract_exists
    rw [hprk (s0.sp - 272#64)]
    apply SepWP.replace_pre (hPQ := hmacCore_split C.F (s0.sp - 240#64) _)
      (by sep_focus)
    wp_extract_exists
    rename_i hgood
    wp_simp_pre_fast [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre (hPQ := hmacCore_merge_sub416 C.F s0.sp _ hgood) (by sep_focus)
    wp_simp_pre_fast [hadrp, hadrp']
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF1b
    apply SepWP.of_sepWP_frozen hF1b
    wp_call hexp' (s0.sp - 416#64, hkdfExtract C.F (some sv) seed, s0.sp - 272#64,
      img.base + bv% (ls_str% "WhisperMessageKeys"), whisperMessageKeys,
      s0.sp - 496#64, s0.sp - 496#64)
    wp_extract_exists
    wp_simp_pre_fast [hokm_eq, hokm (s0.sp - 496#64), bv_sub_add_lit',
      BitVec.reduceSub, sepConj_assoc]
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 seed_ptr seed seed_cap hseed_len hseed_le hseed_small)
      (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF2
    apply SepWP.of_sepWP_frozen hF2
    wp_call hdealloc (seed_ptr, seed_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre
      (hPQ := pointsToBytes_memRegion_merge_32 pqr_ptr sv.toList pqr_cap hsv_len hpqr_le hpqr_small)
      (by sep_focus)
    apply SepWP.done_frozen (by wp_norm_lhs) (by wp_norm_lhs)
    intro hF3
    wp_call hdealloc (pqr_ptr, pqr_cap.toNat, 1, s0.sp - 496#64)
    wp_extract_exists
    wp_steps
    apply SepWP.replace_pre (hPQ := cells_sub496_10_merge s0.sp _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub416_8_merge s0.sp _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub272_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub240_4_merge s0.sp _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre
      (hPQ := cells_sub208_14_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := cells_sub96_12_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre
      (hPQ := memRegion_gen_merge (s0.readReg64 (.gpr 0#5)) _ _ _ _ _) (by sep_focus)
    apply SepWP.replace_pre (hPQ := memRegion_24_merge (s0.readReg64 (.gpr 1#5)) _ _ _) (by sep_focus)
    rw [fnFrame_split_generateKeysExt_post s0.sp,
      messageKeysAt_generateKeys, hokm (s0.readReg64 (.gpr 8#5))]
    wp_simp_post [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    clear hext_some hexp' hdealloc hprk hokm hgood
    wp_done

theorem generateKeys_ok_stacked_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hHkdf : HkdfContractsExt img C.F ext)
    (hA : AllocContractsX img A ext) :
    GenerateKeysOkExtStacked img C A ext :=
  generateKeys_ok_of_contracts_stacked himg
    (extract_ok_ext' img C ext himg hHkdf)
    (expand_multi_info_ok_ext' img C ext hHkdf)
    (hA.dealloc_ok_at generateKeysName
      (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"))
      (by rw [(ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::MessageKeyGenerator>::generate_keys"),
            (ls_stub% "__rustc::__rust_dealloc")]))

end GenerateKeysStacked

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtGenKeysMac
