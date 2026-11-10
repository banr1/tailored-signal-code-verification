/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Identity
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdTrustShim.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

private theorem libsignalSessionCode_nonempty :
    0 < libsignalSessionCode.code.length :=
  match h : libsignalSessionCode.code with
  | [] => absurd (congrArg List.isEmpty h) (by decide)
  | _ :: _ => Nat.zero_lt_succ _

private theorem stk_le_pow64_of_codeLoaded {prog : Program} {m : Memory}
    {sp : BitVec 64} {stk : Nat} {R : SepProp}
    (hlen : 0 < prog.code.length)
    (hL : prog.CodeLoaded m)
    (hm : m ⊨ stackAt sp stk ∗ R) : stk ≤ 2 ^ 64 := by
  have hrx : m.perm (prog.base + 0#64) = some Perm.rx :=
    ((Program.codeLoaded_iff.mp hL).2.2 0 hlen).2.1
  by_cases hle : stk ≤ 2 ^ 64
  · exact hle
  · have ha : InRegion (sp - BitVec.ofNat 64 stk) stk (prog.base + 0#64) := by
      unfold InRegion
      have := BitVec.isLt (prog.base + 0#64 - (sp - BitVec.ofNat 64 stk))
      omega
    have hrw : m.perm (prog.base + 0#64) = some Perm.rw :=
      (IsBlock.memRegion (sp - BitVec.ofNat 64 stk) stk).perm_rw hm ha
    rw [hrx] at hrw
    exact absurd hrw (by decide)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_decodes CryptoVerification.libsignalSessionCode_tree cliIdTrustShimBin
  [(ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity") →
   (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity" + 100)]

private abbrev idTrustShimStack : Nat := extHookStack + 48

private theorem stackAt_idTrustShim (sp : BitVec 64) :
    stackAt sp idTrustShimStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp extHookStack 6 (by decide)

private theorem memRegion_32_trust_box (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b1 : BitVec 8, ∃∗ b0 : BitVec 8, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64,
        ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        ((p + 25#64) ↦₈ b1) ∗ memRegion (p + 26#64) 6) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 1#64) 1 6 (by decide),
    memRegion_one, memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem idTrustShim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr idTrustShimName + bv% (56)) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity" + 0x38)) := by
  rw [Program.fnAddr_rebase, idTrustShim_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

private theorem idTrustShim_fixed_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustShimName)
      (idTrustShimSpec A img idTrustShimStack) := by
  unfold idTrustShimSpec Spec.inImage
  simp only [idTrustBoxAt, idTrustFutVtOff, stackAt_idTrustShim]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff idTrustShimName =
      num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity") :=
    idTrustShim_fnOff
  have hshim := shim_ok_at2_ext_x hC (name := idTrustShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc := alloc_ok_at_norm_ext_x hC (name := idTrustShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"
      "__rustc::__rust_alloc"))
  have hpanic := panic_at_handle_alloc_error_ext img.base ext idTrustShimName
    (num% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"
      "alloc::alloc::handle_alloc_error"))
  have hadrp := idTrustShim_adrp (H := Rust.withPanics ext) hb
  code_fetches CryptoVerification.libsignalSessionCode cliIdTrustShimBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity")) 104
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn hC
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr idTrustShimName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨⟨self, addrA, keyA⟩, d⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 32 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := fnBase + bv% (48))
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"
      "__rustc::__rust_alloc"))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro _hinv2
  wp_call halloc (32, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::is_trusted_identity"
        "alloc::alloc::handle_alloc_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_32_trust_box, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b1 => SepWPp.exists_elim fun b0 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem idTrustShim_ok_main {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x30 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr idTrustShimName)
      (idTrustShimSpec A img stk) := by
  have hInner := idTrustShim_fixed_ok hC hb
  refine subroutine_ok.of_codeLoaded fun ⟨x, d⟩ R s0 hpc hrun hpre halign hL => ?_
  have hstk64 : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.addrA ∧
            s0.readReg64 .x2 = x.keyA ∧ (s0.readReg64 .x3).setWidth 8 = d⌝ ∗
            A.pool ∗ R) := by
      dsimp only [idTrustShimSpec, Spec.inImage] at hpre
      convert hpre using 1
      ac_rfl
    exact stk_le_pow64_of_codeLoaded (prog := tripleRatchetProgAtExt img.base ext)
      libsignalSessionCode_nonempty hL hm_stk
  have hstk' : idTrustShimStack ≤ stk := by
    dsimp [idTrustShimStack]
    omega
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - idTrustShimStack) ∗
        stackAt s0.sp idTrustShimStack := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp idTrustShimStack
      (stk - idTrustShimStack) (by omega)
    rwa [Nat.add_sub_of_le hstk'] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - idTrustShimStack) ∗ R
  have hpre' : s0.mem ⊨ (idTrustShimSpec A img idTrustShimStack).pre (x, d) s0 ∗ R' := by
    dsimp only [idTrustShimSpec, Spec.inImage, R'] at hpre ⊢
    rw [hsplit] at hpre
    convert hpre using 1
    ac_rfl
  refine (hInner.to_outcome (x, d) R' s0 hpc hrun hpre' halign).mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [idTrustShimSpec, Spec.inImage, R'] at hpost ⊢
    rw [hsplit]
    convert hpost using 1
    ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [idTrustShimSpec, Spec.inImage, R'] at hpost ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hex).elim
  · dsimp only [idTrustShimSpec, Spec.inImage] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.SignalSession.Cli.Store.IdTrustShim.Helpers
