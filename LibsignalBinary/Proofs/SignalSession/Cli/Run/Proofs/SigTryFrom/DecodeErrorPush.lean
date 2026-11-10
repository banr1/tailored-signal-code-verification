/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.PushCore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.PushGrowOne
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_x sp_setMem_setPC_pre_x
  readReg64_setPC_pre_x readReg64_setMem_setPC_pre_x
  readReg32_setPC_pre_x readReg32_setMem_setPC_pre_x
  readReg_setPC_pre_x readReg_setMem_setPC_pre_x

def pushStackPadX (sp : BitVec 64) : SepProp :=
  memRegion (sp - 32768#64) 16208

theorem stackAt_pushX (sp : BitVec 64) :
    stackAt sp (2 * extHookStack) =
      pushStackPadX sp ∗
      stackAt (sp - 176#64) extHookStack ∗
      cells (sp - 176#64) 4 ∗
      cells (sp - 144#64) 8 ∗
      cells (sp - 80#64) 2 ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
  have h1 := ProofLib.stackAt_split_bottom sp 16560 16208 (by decide)
  change stackAt sp (2 * extHookStack) = pushStackPadX sp ∗ stackAt sp 16560 at h1
  have h2 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells sp 16496 8 (by decide)
  change stackAt sp 16560 = stackAt (sp - 64#64) 16496 ∗ cells (sp - 64#64) 8 at h2
  have h3 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells (sp - 64#64) 16480 2 (by decide)
  have h3' : sp - 64#64 - BitVec.ofNat 64 (2 * 8) = sp - 80#64 := by bv_omega
  rw [h3'] at h3
  change stackAt (sp - 64#64) 16496 = stackAt (sp - 80#64) 16480 ∗ cells (sp - 80#64) 2 at h3
  have h4 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells (sp - 80#64) 16416 8 (by decide)
  have h4' : sp - 80#64 - BitVec.ofNat 64 (8 * 8) = sp - 144#64 := by bv_omega
  rw [h4'] at h4
  change stackAt (sp - 80#64) 16480 = stackAt (sp - 144#64) 16416 ∗ cells (sp - 144#64) 8 at h4
  have h5 := CryptoVerification.LibsignalTripleRatchet.stackAt_split_cells (sp - 144#64) 16384 4 (by decide)
  have h5' : sp - 144#64 - BitVec.ofNat 64 (4 * 8) = sp - 176#64 := by bv_omega
  rw [h5'] at h5
  change stackAt (sp - 144#64) 16416 =
    stackAt (sp - 176#64) extHookStack ∗ cells (sp - 176#64) 4 at h5
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ v0) ∗ ((sp - 56#64) ↦₆₄ v1) ∗ ((sp - 48#64) ↦₆₄ v2) ∗
        ((sp - 40#64) ↦₆₄ v3) ∗ ((sp - 32#64) ↦₆₄ v4) ∗ ((sp - 24#64) ↦₆₄ v5) ∗
        ((sp - 16#64) ↦₆₄ v6) ∗ ((sp - 8#64) ↦₆₄ v7)) := by
    cells_unfold
  rw [h1, h2, h3, h4, h5, hc8]
  ac_rfl

theorem decodeErrorPushSpecWithStack_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      ((decodeErrorPushSpecWithStack A (2 * extHookStack)).inImage img) := by
  unfold Spec.inImage decodeErrorPushSpecWithStack decodeErrorAtStackLen vecOf vecAt vecHeader vecBuf
  simp only [List.length_replicate, sepExists_sepConj_left, sepExists_sepConj_right]
  simp only [stackAt_pushX]
  have hfn := (ls_lemma% fnOff "<prost::error::DecodeError>::push")
  have hgrow := grow_one_str_pair_ok_ext_x hA
  rw [Program.fnAddr_rel (name := "<prost::error::DecodeError>::push")
    hfn (ls_lemma% fnOff "<alloc::raw_vec::RawVec<(&str, &str)>>::grow_one") (k := 128) (by decide)] at hgrow
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush.libsignalSessionBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<prost::error::DecodeError>::push")) 128
  dsimp only [tripleRatchetProgAtExt, decodeErrorPushName, growOneStrPairName] at hgrow ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr
    "<prost::error::DecodeError>::push" = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨d, e, n⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  have hn_lt32 : n < 2 ^ 32 := by assumption
  have hptr_ne0 : v_stk_2 ≠ 0#64 := by assumption
  obtain ⟨hkind1, hkind2⟩ : KindNoHeap v_stk := by assumption
  have hn_toNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  conv =>
    arg 4
    simp only [BitVec.ofNat_eq_ofNat,
      vecBuf_stackEntryAt_memRegion A n v_stk_1 v_stk_2 (by omega) (by omega)]
  by_cases heq : BitVec.ofNat 64 n = v_stk_1
  · subst v_stk_1
    have hcap_lt : (BitVec.ofNat 64 n).toNat < 2 ^ 32 := by rw [hn_toNat]; exact hn_lt32
    have hnew_toNat : (newCap (BitVec.ofNat 64 n)).toNat = max (2 * n) 4 := by
      rw [newCap_toNat hcap_lt, hn_toNat]
    have hn_lt_new : n < (newCap (BitVec.ofNat 64 n)).toNat := by omega
    have hn1_le_new : n + 1 ≤ (newCap (BitVec.ofNat 64 n)).toNat := by omega
    have hnew_bound : (newCap (BitVec.ofNat 64 n)).toNat * 32 < 2 ^ 63 := by omega
    have hnew_ne0 : newCap (BitVec.ofNat 64 n) ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      change (newCap (BitVec.ofNat 64 n)).toNat = 0 at ht
      omega
    apply SepWPp.of_sepWP_inImage (mid := entry + bv% (128)) hinv0
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    rintro ⟨hF1, hsym1⟩
    refine SepWPp.call_frame (ret_pc := entry + bv% (108)) (x := (e, BitVec.ofNat 64 n, v_stk_2, s0.sp - 64#64))
      hgrow (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal) pre_inImage_merge
      ⟨⟨hF1, hsym1⟩, by wp_norm_goal, by wp_norm_goal, hcap_lt, hptr_ne0⟩
      (by
        simp only [bv_sub_64_sub]
        sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sf _ hm => allowPanic_frame id hm)
      (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
    rcases hcs_sf with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hx29⟩
    simp only [wp_norm, arm64_norm] at hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hx29 hsp_sf
    conv => arg 4; simp only [sepExists_sepConj_left, sepConj_assoc, bv_sub_64_sub]
    apply SepWPp.exists_elim; intro p'
    refine SepWPp.pure_elim fun ⟨hp', htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [memRegion_split_entry p' n (newCap (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (newCap (BitVec.ofNat 64 n))
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists p'
    simp only [BitVec.ofNat_eq_ofNat, hnew_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion A (n + 1) (newCap (BitVec.ofNat 64 n)) p' hn1_le_new hnew_bound,
      memRegion_split_entry p' n (newCap (BitVec.ofNat 64 n)).toNat hn_lt_new hnew_bound]
    wp_done
  · have hbeq : (BitVec.ofNat 64 n == v_stk_1) = false := beq_eq_false_iff_ne.mpr heq
    have hne_nat : n ≠ v_stk_1.toNat := by
      intro hnat
      apply heq
      apply BitVec.eq_of_toNat_eq
      rw [hn_toNat, hnat]
    have hn_lt_cap : n < v_stk_1.toNat := by omega
    have hn1_le_cap : n + 1 ≤ v_stk_1.toNat := by omega
    have hcap_ne0 : v_stk_1 ≠ 0#64 := by
      intro h0
      subst h0
      change n < 0 at hn_lt_cap
      omega
    apply SepWPp.of_sepWP_ret
    wp_simp_pre [hcap_ne0, ite_false,
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega),
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro c0
    apply SepWP.exists_elim; intro c1
    apply SepWP.exists_elim; intro c2
    apply SepWP.exists_elim; intro c3
    wp_steps
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_1
    apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists v_stk_2
    simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ite_false,
      vecBuf_stackEntryAt_memRegion A (n + 1) v_stk_1 v_stk_2 hn1_le_cap (by omega),
      memRegion_split_entry v_stk_2 n v_stk_1.toNat hn_lt_cap (by omega)]
    wp_done

theorem decodeErrorPush_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeErrorPushName)
      ((decodeErrorPushExternSpecWithStack A (2 * extHookStack)).inImage img) := by
  refine subroutine_ok.of_codeLoaded fun ⟨d, e, n⟩ R s0 hpc hrun hpre hal _ => ?_
  simp only [Spec.inImage, decodeErrorPushExternSpecWithStack, sepConj_assoc,
    satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv, ⟨hx0, he_ne, hn⟩, hmem⟩
  have hpre' : s0.mem ⊨ ((decodeErrorPushSpecWithStack A (2 * extHookStack)).inImage img).pre
      (d, e, n) s0 ∗ R := by
    simp only [Spec.inImage, decodeErrorPushSpecWithStack, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hinv, ⟨hx0, hn⟩, hmem⟩
  refine (decodeErrorPushSpecWithStack_ok_ext_x hA).mono_outcome (d, e, n) R s0 hpc hrun hpre' hal
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [Spec.inImage, decodeErrorPushSpecWithStack, decodeErrorPushExternSpecWithStack,
      sepConj_assoc, sepExists_sepConj_left, satisfies_pure_sepConj, satisfies_sepExists] at hpost ⊢
    exact ⟨hpost.1, e, he_ne, hpost.2⟩
  · exact Or.inr hrest

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
