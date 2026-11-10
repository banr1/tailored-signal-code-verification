/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.AllocContracts4KExt
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.Core
import LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.Fetch
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# Stacked `spqr::send::<Coins>` on Empty State

Lifts `spqrSendEmpty_base_ext_trap` to `Stage2ContractsExt` and `AllocContracts4K` using the
`extHookStack` frame carved out by `stackAt_spqr`.
-/

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtSpqrSendEmpty

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty
open CryptoVerification.Cli.LibsignalSpqrV1.M4
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Slots

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem memcpyPcs_withStack_of_sessionMemcpyRegion {prog : Program} {entry : BitVec 64}
    {stk : Nat}
    (hmc : subroutine_ok prog entry (withStack sessionMemcpyRegionSpec stk)) :
    subroutine_ok prog entry (withStack memcpyPcsSpec stk) := by
  refine subroutine_ok_outcome_intro fun ⟨t, c, i⟩ R s0 hpc hrun hpre hsp => ?_
  let R' : SepProp := stackAt s0.sp stk ∗ R
  have hpre' : s0.mem ⊨ memcpyPcsSpec.pre (t, c, i) s0 ∗ R' := by
    dsimp only [withStack, R'] at hpre ⊢
    rwa [sepConj_assoc] at hpre
  simp only [memcpyPcsSpec] at hpre'
  rw [← pcs_src, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2⟩, hmem⟩ := hpre'
  have h2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (bytes_of_pcs _ c i))) hmem
  rw [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at h2
  obtain ⟨bs, h3⟩ := h2
  rw [sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at h3
  obtain ⟨⟨hlen, b1, b3, b5, h1, h3', h5, rfl⟩, h4⟩ := h3
  have hpre_mc' : s0.mem ⊨ sessionMemcpyRegionSpec.pre (t - 7984#64, t - 3328#64,
      b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R' := by
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, by rw [hx2, hlen]; rfl⟩, ?_⟩
    rw [hlen]
    exact h4
  have hpre_mc : s0.mem ⊨ (withStack sessionMemcpyRegionSpec stk).pre
      (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 ∗ R := by
    dsimp only [withStack, R'] at hpre_mc' ⊢
    rwa [← sepConj_assoc] at hpre_mc'
  refine hmc.mono_outcome
    (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5))))
    R s0 hpc hrun hpre_mc hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    have hpost' : sf.mem ⊨ sessionMemcpyRegionSpec.post
        (t - 7984#64, t - 3328#64, b1 ++ (unpack64 c ++ (b3 ++ (unpack64 i ++ b5)))) s0 sf ∗ R' := by
      dsimp only [withStack, R'] at hpost ⊢
      rwa [sepConj_assoc] at hpost
    dsimp only [sessionMemcpyRegionSpec] at hpost'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost'
    obtain ⟨⟨hx0_sf, htr⟩, hpost_mem⟩ := hpost'
    have hout' : sf.mem ⊨ memcpyPcsSpec.post (t, c, i) s0 sf ∗ R' := by
      dsimp only [memcpyPcsSpec]
      rw [← pcs_src, ← pcs_dst, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨htr, hx0_sf⟩, ?_⟩
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono
        (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5)
        (pcs_of_bytes _ c i b1 b3 b5 h1 h3' h5))) hpost_mem
    dsimp only [withStack, R'] at hout' ⊢
    rwa [← sepConj_assoc] at hout'
  · exact Or.inr (Or.inl ⟨hpan, hpost⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 1600000 in
theorem spqrSendEmpty_base_ext_4k (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (img : Obj.Image)
    (hDecEmpty : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decodeStateName)
      (decodeStateEmptySpec A))
    (hA4K : AllocContracts4K img.base A ext)
    (hE : S.SendEmptyOk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img) := by
  have hfn := (ls_lemma% fnOff "spqr::send::<libsignal_cli_ratchet::Coins>")
  have hdec := sub_ok_at_of_fnAddr hDecEmpty decodeStateName 0 (Nat.add_zero _)
  rw [← CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.spqrSend_add_decodeState_eq_fnAddr] at hdec
  have hmc_raw : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>")))
      (withStack sessionMemcpyRegionSpec extHookStack) :=
    AllocContracts4K.session_memcpy_region_ok_at hA4K
      CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName
      (num% (ls_off% "memcpy" - ls_off% "spqr::send::<libsignal_cli_ratchet::Coins>"))
      extHookStack (by decide) (by decide)
  have hmc := memcpyPcs_withStack_of_sessionMemcpyRegion hmc_raw
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 0 108
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 136 88
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 4608 12
  spqr_fetches_cli img.base (Rust.withPanics ext) hfn 4632 36
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec,
    CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendSpec, Spec.inImage, stackAt_spqr]
  simp (config := { maxSteps := 1000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨ret, ⟨v, cap, ptr, bs⟩, cur, rest⟩ := x
  dsimp only at *
  subst bs
  wp_steps
  wp_apply
  wp_simp_pre only [decodeEmpty_split, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d1
  wp_steps
  wp_apply
  wp_simp_pre only [ret_split ret, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  wp_steps
  refine SepWP.fold (dst_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
  refine SepWP.fold (decode_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone)
    (by sep_focus) ?_
  refine SepWP.fold (result_fold A ret) (by sep_focus) ?_
  refine SepWP.fold (CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty.tape_fold img.base cur rest)
    (by sep_focus) ?_
  simp only [hE.send, hE.draws, hE.noPanic]
  wp_done

theorem spqrSendEmpty_base_of_externsOk_on
    {P : E2E.PEParams} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {ext ext' : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext) (hAg : AgreeOnCliHooks ext ext')
    (hE : S.SendEmptyOk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext')
      ((tripleRatchetProgAtExt img.base ext').fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendName)
      (CryptoVerification.Cli.LibsignalTripleRatchet.spqrSendEmptySpec A ctl S img) :=
  spqrSendEmpty_base_ext_4k A ctl S ext' img
    (Stage2ContractsExt.of_externsOk_on hOk hAg img).decode_state_empty
    (AllocContracts4K.of_externsOk_on hOk hAg img.base)
    hE

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtSpqrSendEmpty
