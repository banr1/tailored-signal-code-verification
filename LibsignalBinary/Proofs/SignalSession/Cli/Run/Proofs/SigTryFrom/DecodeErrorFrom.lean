/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorFrom.Core
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "alloc::alloc::handle_alloc_error")

theorem stackAt_decodeErrorFromX (sp : BitVec 64) :
    stackAt sp (2 * extHookStack) =
      memRegion (sp - 32768#64) 16352 ∗
        stackAt (sp - 32#64) extHookStack ∗
        cells (sp - 32#64) 4 := by
  have h1 : stackAt sp (2 * extHookStack) =
      memRegion (sp - 32768#64) 16352 ∗ stackAt sp (extHookStack + 32) :=
    ProofLib.stackAt_split_bottom sp (extHookStack + 32) 16352 (by decide)
  have h2 : stackAt sp (extHookStack + 32) =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
    CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 16384 4 (by decide)
  rw [h1, h2]

theorem decodeErrorFrom_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorFromName)
      ((decodeErrorFromSpecWithStack A (2 * extHookStack)).inImage img) := by
  unfold Spec.inImage
  simp only [decodeErrorFromSpecWithStack, stackAt_decodeErrorFromX]
  cells_unfold
  have hshim := shim_ok_at2_ext_x hA
    (name := decodeErrorFromName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  have halloc := alloc_ok_at_norm_ext_x hA
    (name := decodeErrorFromName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  have hpanic := panic_at_handle_alloc_error_ext img.base ext decodeErrorFromName
    (num% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
  clear hA
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff decodeErrorFromName =
      num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") :=
    (ls_lemma% fnOff "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorFrom.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) 92
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr decodeErrorFromName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr decodeErrorFromName = entry
  examples_hide_fetches
  obtain ⟨k, w⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpow2 : ∃ j, 8 = 2 ^ j := ⟨3, rfl⟩
  have hlay : LayoutOk 72 8 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + bv% (32))
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) hinv0
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF1, hsym1⟩
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  rintro ⟨hF2, hsym2⟩
  wp_call halloc (72, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (CryptoVerification.LibsignalTripleRatchet.allocFailedIn_of_eq
          (by simp only [Rust.panicked, arm64_norm, htrace, ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_40_cells (k + 8#64), memRegion_72_cells,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun k0 => SepWPp.exists_elim fun k1 =>
      SepWPp.exists_elim fun k2 => SepWPp.exists_elim fun k3 =>
      SepWPp.exists_elim fun k4 =>
      SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun u4 => SepWPp.exists_elim fun u5 =>
      SepWPp.exists_elim fun u6 => SepWPp.exists_elim fun u7 =>
      SepWPp.exists_elim fun u8 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    apply SepWP.fold (decodeErrorWith_zero_entails A _ w _ _ _ _ _ ‹KindNoHeap w›) (by sep_focus)
    apply SepWP.fold (cells6_entails_memRegion48 k w _ _ _ _ _) (by sep_focus)
    wp_done

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
