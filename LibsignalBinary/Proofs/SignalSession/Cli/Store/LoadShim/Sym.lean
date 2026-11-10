/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.LoadShim.Helpers

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

gen_decodes CryptoVerification.libsignalSessionCode_tree cliLoadShimBin
  [(ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") →
   (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session" + 76)]

private abbrev sessLoadShimStack : Nat := extHookStack + 32

private theorem stackAt_sessLoadShim (sp : BitVec 64) :
    stackAt sp sessLoadShimStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem memRegion_24_box (p : BitVec 64) :
    memRegion p 24 =
      (∃∗ b0 : BitVec 8, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₈ b0) ∗
        memRegion (p + 17#64) 7) := by
  rw [memRegion_split p 8 16 (by decide),
    memRegion_split (p + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem sessLoadShim_adrp {b : BitVec 64} {H : String → Option (State → State)}
    (hb : (b &&& 0xfff#64) = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr sessLoadShimName + bv% (40)) &&&
      0xfffffffffffff000#64) =
      b + bv% (page% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session" + 0x28)) := by
  rw [Program.fnAddr_rebase, sessLoadShim_fnOff, BitVec.add_assoc,
    ProofLib.ObjectLoad.adrp_page_of_aligned hb]
  rfl

private theorem sessLoadShim_fixed_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadShimName)
      (sessLoadShimSpec A img sessLoadShimStack) := by
  unfold sessLoadShimSpec Spec.inImage
  simp only [sessLoadBoxAt, sessLoadFutVtOff, stackAt_sessLoadShim]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff sessLoadShimName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session") :=
    sessLoadShim_fnOff
  have hshim := shim_ok_at2_ext_x hC (name := sessLoadShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
  have halloc := alloc_ok_at_norm_ext_x hC (name := sessLoadShimName)
    (k := num% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"
      "__rustc::__rust_alloc"))
  have hpanic := panic_at_handle_alloc_error_ext img.base ext sessLoadShimName
    (num% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"
      "alloc::alloc::handle_alloc_error"))
  have hadrp := sessLoadShim_adrp (H := Rust.withPanics ext) hb
  code_fetches CryptoVerification.libsignalSessionCode cliLoadShimBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session")) 80
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn hC
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessLoadShimName = fnBase
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨self, addrA⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : LayoutOk 24 8 := ⟨by decide, hpow8, by decide⟩
  apply SepWPp.of_sepWP (mid := fnBase + bv% (36))
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"
      "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"
      "__rustc::__rust_alloc"))
    hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro _hinv2
  wp_call halloc (24, 8)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session"
        "alloc::alloc::handle_alloc_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_24_box, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem sessLoadShim_ok_main {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {stk : Nat}
    (hC : AllocContractsX img A ext)
    (hstk : 0x20 + extHookStack ≤ stk)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadShimName)
      (sessLoadShimSpec A img stk) := by
  have hInner := sessLoadShim_fixed_ok hC hb
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre halign hL => ?_
  have hstk64 : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ stackAt s0.sp stk ∗
        (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
          ⌜s0.readReg64 .x0 = x.self ∧ s0.readReg64 .x1 = x.addrA⌝ ∗ A.pool ∗ R) := by
      dsimp only [sessLoadShimSpec, Spec.inImage] at hpre
      convert hpre using 1
      ac_rfl
    exact stk_le_pow64_of_codeLoaded (prog := tripleRatchetProgAtExt img.base ext)
      libsignalSessionCode_nonempty hL hm_stk
  have hstk' : sessLoadShimStack ≤ stk := by
    dsimp [sessLoadShimStack]
    omega
  have hsplit : stackAt s0.sp stk =
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - sessLoadShimStack) ∗
        stackAt s0.sp sessLoadShimStack := by
    have h1 := ProofLib.stackAt_split_bottom s0.sp sessLoadShimStack
      (stk - sessLoadShimStack) (by omega)
    rwa [Nat.add_sub_of_le hstk'] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - sessLoadShimStack) ∗ R
  have hpre' : s0.mem ⊨ (sessLoadShimSpec A img sessLoadShimStack).pre x s0 ∗ R' := by
    dsimp only [sessLoadShimSpec, Spec.inImage, R'] at hpre ⊢
    rw [hsplit] at hpre
    convert hpre using 1
    ac_rfl
  refine hInner.mono_outcome x R' s0 hpc hrun hpre' halign fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessLoadShimSpec, Spec.inImage, R'] at hpost ⊢
    rw [hsplit]
    convert hpost using 1
    ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [sessLoadShimSpec, Spec.inImage, R'] at hpost ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hex).elim
  · dsimp only [sessLoadShimSpec, Spec.inImage] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.SignalSession.Cli.Store.LoadShim.Helpers
