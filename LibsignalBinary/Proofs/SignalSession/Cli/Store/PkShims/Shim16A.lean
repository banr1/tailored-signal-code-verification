/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims.Common
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes CryptoVerification.libsignalSessionCode_tree cliSpkGetShimBin
  [(ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key") →
   (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key" + 80)]

gen_decodes CryptoVerification.libsignalSessionCode_tree cliPkGetShimBin
  [(ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") →
   (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key" + 80)]

private theorem spkGetShim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spkGetShimName + bv% (44)) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key" + 0x2c)) := by
  rw [Program.fnAddr_rebase, spkGetShim_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

theorem spkGetShim_fixed_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spkGetShimName)
      (pkShimSpec spkGetFutVtOff A img pkShimStack) := by
  unfold pkShimSpec Spec.inImage
  simp only [pkBoxAt, spkGetFutVtOff, stackAt_pkShim]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff spkGetShimName =
      num% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key") :=
    spkGetShim_fnOff
  have hshim := shim_ok_at2_ext_x hC (name := spkGetShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc := alloc_ok_at_norm_ext_x hC (name := spkGetShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"
      "__rustc::__rust_alloc"))
  have hpanic := panic_at_handle_alloc_error_ext img.base ext spkGetShimName
    (num% (ls_rel%
      "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"
      "alloc::alloc::handle_alloc_error"))
  have hadrp := spkGetShim_adrp (H := Rust.withPanics ext) hb
  code_fetches CryptoVerification.libsignalSessionCode cliSpkGetShimBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key")) 84
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn hC
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr spkGetShimName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨self, id⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := fnBase + bv% (36))
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"
      "__rustc::__rust_alloc"))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro _hinv2
  wp_call halloc (16, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::SignedPreKeyFiles as libsignal_protocol::storage::traits::SignedPreKeyStore>::get_signed_pre_key"
        "alloc::alloc::handle_alloc_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_box, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

private theorem pkGetShim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr pkGetShimName + bv% (44)) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key" + 0x2c)) := by
  rw [Program.fnAddr_rebase, pkGetShim_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

theorem pkGetShim_fixed_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pkGetShimName)
      (pkShimSpec pkGetFutVtOff A img pkShimStack) := by
  unfold pkShimSpec Spec.inImage
  simp only [pkBoxAt, pkGetFutVtOff, stackAt_pkShim]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff pkGetShimName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key") :=
    pkGetShim_fnOff
  have hshim := shim_ok_at2_ext_x hC (name := pkGetShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc := alloc_ok_at_norm_ext_x hC (name := pkGetShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"
      "__rustc::__rust_alloc"))
  have hpanic := panic_at_handle_alloc_error_ext img.base ext pkGetShimName
    (num% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"
      "alloc::alloc::handle_alloc_error"))
  have hadrp := pkGetShim_adrp (H := Rust.withPanics ext) hb
  code_fetches CryptoVerification.libsignalSessionCode cliPkGetShimBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key")) 84
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn hC
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr pkGetShimName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨self, id⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := fnBase + bv% (36))
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"
      "__rustc::__rust_alloc"))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro _hinv2
  wp_call halloc (16, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::get_pre_key"
        "alloc::alloc::handle_alloc_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_box, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

end CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers
