/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkShims.Common
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false

/-!
# PQ `IdentityFiles` Shims and Future-Drop Stub

Proves the `futDrop` 1-instruction stub and the 16-byte boxed future shims for
`get_identity_key_pair` and `get_local_registration_id` on `initProg img W`.
-/

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Store.PkShims.Helpers

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `futDrop` at `initProg img W` (`1`-instruction `ret`) -/

gen_decodes CryptoVerification.libsignalSessionCode_tree cliInitFutDropBin
  [(ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") →
   (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>" + 4)]

theorem futDrop_cli_ok (img : Obj.Image) (W : CliHooks) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr KitInst.cliIdFutDropName) futDropSpec := by
  simp only [futDropSpec]
  have hfn : libsignalSessionCode.fnOff KitInst.cliIdFutDropName =
      num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
    KitInst.cliIdFutDrop_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliInitFutDropBin img.base
    (Rust.withPanics (cliExterns W)) hfn
    (num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) 4
  dsimp only [initProg, tripleRatchetProgAtExt] at ⊢
  clear hfn
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

/-! ## 2. 16-Byte Box Splitter & Stack Lifting for `idOwnShimSpec` -/

theorem memRegion_16_ownBox (p : BitVec 64) :
    memRegion p 16 =
      (∃∗ b0 : BitVec 8, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₈ b0) ∗ memRegion (p + 9#64) 7) := by
  rw [memRegion_split p 8 8 (by decide),
    memRegion_split (p + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem idOwnShim_lift_stk {name : String} {vtOff : BitVec 64}
    {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hInner : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      (idOwnShimSpec vtOff A img pkShimStack))
    (hstk : 32 + extHookStack ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name)
      (idOwnShimSpec vtOff A img stk) := by
  refine subroutine_ok.of_codeLoaded fun self R s0 hpc hrun hpre halign hL => ?_
  have hstk64 : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          ⌜s0.readReg64 .x0 = self⌝ ∗ A.pool ∗ R) := by
      dsimp only [idOwnShimSpec, Spec.inImage] at hpre
      convert hpre using 1
      ac_rfl
    exact stk_le_pow64_of_codeLoaded (prog := tripleRatchetProgAtExt img.base ext)
      libsignalSessionCode_nonempty hL hm_stk
  have hstk' : pkShimStack ≤ stk := by
    dsimp [pkShimStack]
    omega
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pkShimStack) ∗
        stackAt s0.sp pkShimStack := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp pkShimStack
      (stk - pkShimStack) (by omega)
    rwa [Nat.add_sub_of_le hstk'] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pkShimStack) ∗ R
  have hpre' : s0.mem ⊨ (idOwnShimSpec vtOff A img pkShimStack).pre self s0 ∗ R' := by
    dsimp only [idOwnShimSpec, Spec.inImage, R'] at hpre ⊢
    rw [hsplit] at hpre
    convert hpre using 1
    ac_rfl
  refine (hInner.to_outcome self R' s0 hpc hrun hpre' halign).mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [idOwnShimSpec, Spec.inImage, R'] at hpost ⊢
    rw [hsplit]
    convert hpost using 1
    ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [idOwnShimSpec, Spec.inImage, R'] at hpost ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hex).elim
  · dsimp only [idOwnShimSpec, Spec.inImage] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 3. `get_identity_key_pair` Shim (`19` instructions / `76` bytes) -/

gen_decodes CryptoVerification.libsignalSessionCode_tree cliIdKeyPairShimBin
  [(ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") →
   (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair" + 76)]

private theorem idKeyPairShim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr idKeyPairShimName + bv% (36)) &&&
      bv% (2 ^ 64 - 4096)) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair" + 36)) := by
  rw [Program.fnAddr_rebase, idKeyPairShim_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

theorem idKeyPairShim_fixed_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idKeyPairShimName)
      (idOwnShimSpec idKeyPairFutVtOff A img pkShimStack) := by
  unfold idOwnShimSpec Spec.inImage
  simp only [idOwnFutBoxAt, idKeyPairFutVtOff, stackAt_pkShim]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff idKeyPairShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") :=
    idKeyPairShim_fnOff
  have hshim := shim_ok_at2_ext_x hC (name := idKeyPairShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc := alloc_ok_at_norm_ext_x hC (name := idKeyPairShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"
      "__rustc::__rust_alloc"))
  have hpanic := panic_at_handle_alloc_error_ext img.base ext idKeyPairShimName
    (num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"
      "alloc::alloc::handle_alloc_error"))
  have hadrp := idKeyPairShim_adrp (H := Rust.withPanics ext) hb
  code_fetches CryptoVerification.libsignalSessionCode cliIdKeyPairShimBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair")) 76
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn hC
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr idKeyPairShimName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init self s0
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := fnBase + bv% (32))
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"
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
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"
        "alloc::alloc::handle_alloc_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_ownBox, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-! ## 4. `get_local_registration_id` Shim (`19` instructions / `76` bytes) -/

gen_decodes CryptoVerification.libsignalSessionCode_tree cliIdRegIdShimBin
  [(ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") →
   (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id" + 76)]

private theorem idRegIdShim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr idRegIdShimName + bv% (36)) &&&
      bv% (2 ^ 64 - 4096)) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id" + 36)) := by
  rw [Program.fnAddr_rebase, idRegIdShim_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

theorem idRegIdShim_fixed_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idRegIdShimName)
      (idOwnShimSpec idRegIdFutVtOff A img pkShimStack) := by
  unfold idOwnShimSpec Spec.inImage
  simp only [idOwnFutBoxAt, idRegIdFutVtOff, stackAt_pkShim]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff idRegIdShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id") :=
    idRegIdShim_fnOff
  have hshim := shim_ok_at2_ext_x hC (name := idRegIdShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc := alloc_ok_at_norm_ext_x hC (name := idRegIdShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"
      "__rustc::__rust_alloc"))
  have hpanic := panic_at_handle_alloc_error_ext img.base ext idRegIdShimName
    (num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"
      "alloc::alloc::handle_alloc_error"))
  have hadrp := idRegIdShim_adrp (H := Rust.withPanics ext) hb
  code_fetches CryptoVerification.libsignalSessionCode cliIdRegIdShimBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id")) 76
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn hC
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr idRegIdShimName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init self s0
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 16 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := fnBase + bv% (32))
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"
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
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_local_registration_id"
        "alloc::alloc::handle_alloc_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_16_ownBox, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

/-! ## 5. Contract-Parameterized Wrappers (`futDrop_ext_cli_ok`, `idKeyPairShim_ext_ok`, `idRegIdShim_ext_ok`) -/

theorem futDrop_ext_cli_ok (img : Obj.Image) (ext1 : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr KitInst.cliIdFutDropName) futDropSpec := by
  simp only [futDropSpec]
  have hfn : libsignalSessionCode.fnOff KitInst.cliIdFutDropName =
      num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>") :=
    KitInst.cliIdFutDrop_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliInitFutDropBin img.base
    (Rust.withPanics ext1) hfn
    (num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>")) 4
  dsimp only [tripleRatchetProgAtExt] at ⊢
  clear hfn
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  wp_steps
  wp_done

theorem idKeyPairShim_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunSkeleton.RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext1)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr idKeyPairShimName)
      (idOwnShimSpec idKeyPairFutVtOff A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have he : 32 + extHookStack ≤ 516880 := by decide
  exact idOwnShim_lift_stk
    (idKeyPairShim_fixed_ok hh.alloc (RunSkeleton.base_aligned himg))
    (by omega)

theorem idRegIdShim_ext_ok {img : Obj.Image} {A : RustAlloc}
    {ext1 : String → Option (State → State)} (B : RunSkeleton.RunBudgets)
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunSkeleton.RunHooksExt img A ext1)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext1)
      ((tripleRatchetProgAtExt img.base ext1).fnAddr idRegIdShimName)
      (idOwnShimSpec idRegIdFutVtOff A img (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have he : 32 + extHookStack ≤ 516880 := by decide
  exact idOwnShim_lift_stk
    (idRegIdShim_fixed_ok hh.alloc (RunSkeleton.base_aligned himg))
    (by omega)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreCalleesProofs
