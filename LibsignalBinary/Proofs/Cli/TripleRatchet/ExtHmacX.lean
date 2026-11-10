/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeys
public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacStepsA
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacStepsB
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt

/-!
# `crypto::hmac_sha256` Verification under `HkdfContractsExt`

Composes `seg0a` through `seg4b` with `nfs32_runsTo_ext_x` to prove `hmac_sha256_ok_of_hkdfContracts`
on `tripleRatchetProgAtExt img.base ext` at stack budget `2048 + extHookStack = 18432` bytes.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet hiding RW length_hmacWith
open CryptoVerification.SignalSession
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (session2MemsetExternSpec compress256ExternShaSpec)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

theorem trExt_fnAddr_hmac (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr "libsignal_protocol::crypto::hmac_sha256" =
      b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256") := by
  unfold tripleRatchetProgAtExt
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::crypto::hmac_sha256")]

theorem seg0b_runsTo_ext {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)} {key inp : List (BitVec 8)} {s₀ sc : State}
    (hNfs : NewFromSliceOkExt' img C ext)
    (hpre : HmacPreX img C.F key inp s₀)
    (hsc : StateH0X img s₀ sc) :
    RunsToE (tripleRatchetProgAtExt img.base ext) sc (StateH1X img C.F key s₀) := by
  rcases hsc with ⟨hpc_c, ⟨hfrz_c, hsym_c, hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
    hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_key_c : RW sc.mem (s₀.readReg64 .x1) 32 :=
    hframe_c.rw_of_rw _ _ hpre.rw_key
  have hkey_c : sc.mem.readBytes (s₀.readReg64 .x1) 32 = key := by
    rw [hframe_c.readBytes_eq hpre.rw_key (by simp [hpre.disj_key_stack.symm]) (by decide), hpre.key_eq]
  have hrw_stack_c : RW sc.mem (s₀.sp - 17408#64) 17408 :=
    hframe_c.rw_of_rw _ _ hpre.rw_stack
  have hsp_sub_eq : sc.sp - 16928#64 = s₀.sp - 17408#64 := by
    rw [hsp_c]; unfold hsp; clear * -; bv_omega
  have hrw_ret : RW sc.mem (hsp s₀ + 144#64) 0x98 :=
    hrw_stack_c.sub (by unfold hsp; clear * -; bv_omega)
  have hrw_stk_nfs : RW sc.mem (sc.sp - 16928#64) 16928 := by
    rw [hsp_sub_eq]
    exact hrw_stack_c.sub (by clear * -; bv_omega)
  have hd_ret_key : DisjointRegions (hsp s₀ + 144#64) 0x98 (s₀.readReg64 .x1) 32 :=
    (hpre.disj_key_stack.sub_right (hsp s₀ + 144#64) ⟨by decide, by unfold hsp; clear * -; bv_omega⟩).symm
  have hd_ret_stk : DisjointRegions (hsp s₀ + 144#64) 0x98 (sc.sp - 16928#64) 16928 := by
    rw [hsp_sub_eq]; unfold hsp DisjointRegions; clear * -; bv_omega
  have hd_key_stk : DisjointRegions (s₀.readReg64 .x1) 32 (sc.sp - 16928#64) 16928 := by
    rw [hsp_sub_eq]
    exact hpre.disj_key_stack.sub_right (s₀.sp - 17408#64) ⟨by decide, by clear * -; bv_omega⟩
  have hrun := nfs32_runsTo_ext_x hNfs hfrz_c hsym_c hpc_c hstat_c
    hx0_c hx1_c hx2_c hpre.key_len hkey_c hrw_ret hrw_key_c hrw_stk_nfs
    hd_ret_key hd_ret_stk hd_key_stk (by rw [hsp_c]; exact hal_hsp)
  refine runsToE_mono_with_inv hrun hfrz_c hsym_c fun s₁ hfrz₁ hsym₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc1, hstat1, hcc1, htag1, hhmac1, hframe1⟩
  rw [hlr_c] at hpc1
  have hhmac_addr : hsp s₀ + 144#64 + 8#64 = hsp s₀ + 152#64 := by clear * -; bv_omega
  rw [hhmac_addr] at hhmac1
  have hrw_saved : RW sc.mem (hsp s₀ + 384#64) 96 :=
    hrw_stack_c.sub (by unfold hsp; clear * -; bv_omega)
  refine {
    pc_eq := hpc1
    common := {
      frz := hfrz₁
      sym := hsym₁
      status := hstat1
      sp_eq := hcc1.1.trans hsp_c
      x29_eq := hcc1.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_c
      x27_eq := hcc1.2.2.2.2.2.2.2.2.2.1.trans hx27_c
      saved := hmacSaved_of_s2Frame hsaved_c hrw_saved hframe1 (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · unfold hsp DisjointRegions; clear * -; bv_omega
        · rw [hsp_sub_eq]; unfold hsp DisjointRegions; clear * -; bv_omega)
      frame := s2Frame_trans_pair_stk17408 hframe_c hframe1
        (by unfold hsp; clear * -; bv_omega)
        (by rw [hsp_sub_eq]; clear * -; bv_omega)
    }
    x19_eq := hcc1.2.1.trans hx19_c
    x20_eq := hcc1.2.2.1.trans hx20_c
    x21_eq := hcc1.2.2.2.1.trans hx21_c
    tag_eq := htag1
    hmac_st := hhmac1
  }

theorem hmac_runsTo_ext_x {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ : State}
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    (hMemset : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memset"))
      ((session2MemsetExternSpec extHookStack).inImage img))
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec C.F extHookStack).inImage img))
    (hNfs : NewFromSliceOkExt' img C ext)
    (hpre : HmacPreX img C.F key [byte] s₀) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀ (StateH5X C.F key byte s₀) :=
  (seg0a_runsTo_ext hpre).trans fun _ h0 =>
  (seg0b_runsTo_ext hNfs hpre h0).trans fun _ h1 =>
  (seg1a_runsTo_ext hpre h1).trans fun _ h1m =>
  (seg1b1_pre_runsTo_ext hMemcpy hpre h1m).trans fun _ h1c =>
  (seg1b1_post_runsTo_ext hpre h1c).trans fun _ h1p =>
  (seg1b2_runsTo_ext hMemset hpre h1p).trans fun _ h2 =>
  (seg2a_runsTo_ext hpre h2).trans fun _ h2c =>
  (seg2b_runsTo_ext hComp hpre h2c).trans fun _ h3 =>
  (seg3a_runsTo_ext hpre h3).trans fun _ h3c =>
  (seg3b_runsTo_ext hComp hpre h3c).trans fun _ h4 =>
  (seg4a_runsTo_ext hpre h4).trans fun _ h4b =>
  seg4b_runsTo_ext hpre h4b

theorem hmac_sha256_ok_of_nfs_x
    {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    (hMemset : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memset"))
      ((session2MemsetExternSpec extHookStack).inImage img))
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec C.F extHookStack).inImage img))
    (hNfs : NewFromSliceOkExt' img C ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "libsignal_protocol::crypto::hmac_sha256")
      ((hmacSpecWithStack C.F (2048 + extHookStack)).inImage img) := by
  refine subroutine_ok_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hpre hsp => ?_
  rw [trExt_fnAddr_hmac img.base ext] at hpc
  rw [Spec.inImage, hmacSpecWithStack, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hkey_len, hinp_len⟩, hsep⟩
  rcases inp with _ | ⟨byte, _ | _⟩ <;> try { simp at hinp_len }
  have hx2 : s0.readReg64 .x2 = 32#64 := by
    apply BitVec.eq_of_toNat_eq; simp [hx2_nat, hkey_len]
  have hx4 : s0.readReg64 .x4 = 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp at hx4_nat; simp [hx4_nat]
  have hsp_split : stackAt s0.sp (2048 + extHookStack) =
      memRegion (s0.sp - 18432#64) 1024 ∗ memRegion (s0.sp - 17408#64) 17408 :=
    stackAt_split_bottom s0.sp 17408 1024 (by decide)
  rw [hsp_split] at hsep
  have hb_out := IsBlock.memRegion out 32
  have hb_key := IsBlock.pointsToBytes_len (a := ka) hkey_len
  have hb_inp := IsBlock.pointsToBytes_len (a := ia) (rfl : [byte].length = 1)
  have hb_stk := IsBlock.memRegion (s0.sp - 17408#64) 17408
  have hsep_key : s0.mem ⊨ (ka ↦ₛ key) ∗ (memRegion (s0.sp - 17408#64) 17408 ∗
      (memRegion out 32 ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 18432#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_inp : s0.mem ⊨ (ia ↦ₛ [byte]) ∗ (memRegion (s0.sp - 17408#64) 17408 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ memRegion (s0.sp - 18432#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_out : s0.mem ⊨ memRegion out 32 ∗ (memRegion (s0.sp - 17408#64) 17408 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 18432#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 17408#64) 17408 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 18432#64) 1024 ∗ R) := by
    ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes ka 32 = key := by
    have h := (hb_key.read hsep_key).2
    rwa [hkey_len] at h
  have hinp_eq : s0.mem.readBytes ia 1 = [byte] :=
    (hb_inp.read hsep_inp).2
  have hrw_out : RW s0.mem out 32 :=
    fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : RW s0.mem (s0.sp - 17408#64) 17408 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hrw_key : RW s0.mem ka 32 :=
    fun a ha => hb_key.permNoLazy_rw hsep_key ha
  have hrw_inp : RW s0.mem ia 1 :=
    fun a ha => hb_inp.permNoLazy_rw hsep_inp ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV himg hF.roData
  have hread_iv : s0.mem.Readable (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hpre_hmac : HmacPreX img C.F key [byte] s0 := {
    frz := hF
    sym := hsym
    pc_eq := hpc
    status := hrun
    sp_aligned := by simpa [State.spAligned] using hsp
    base_aligned := ProofLib.base_aligned_of_loads himg
    x2_eq := hx2
    x4_eq := hx4
    key_len := hkey_len
    inp_len := rfl
    key_eq := by rw [hx1]; exact hkey_eq
    inp_eq := by rw [hx3]; exact hinp_eq
    iv_eq := hiv_eq
    read_iv := hread_iv
    rw_key := by rw [hx1]; exact hrw_key
    rw_inp := by rw [hx3]; exact hrw_inp
    rw_out := by rw [hx0]; exact hrw_out
    rw_stack := hrw_stk
    disj_iv_stack := disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
    disj_out_stack := by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
    disj_key_stack := by rw [hx1]; exact hb_key.disjoint hb_stk (by decide) (by decide) hsep_key
    disj_inp_stack := by rw [hx3]; exact hb_inp.disjoint hb_stk (by simp) (by decide) hsep_inp
  }
  refine (hmac_runsTo_ext_x hMemcpy hMemset hComp hNfs hpre_hmac).to_reaches_pc
    fun sf h5 _ _ htr => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  rw [Spec.inImage, hmacSpecWithStack]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  rw [hsp_split]
  have hb_out' := IsBlock.pointsToBytes_len (a := out) (length_hmacWith C.F key [byte])
  rw [hx0] at hout_sf hframe_sf
  have hpost_sep : sf.mem ⊨ (out ↦ₛ hmacWith C.F key [byte]) ∗ (memRegion (s0.sp - 17408#64) 17408 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 18432#64) 1024 ∗ R)) :=
    S2Frame.update_two_blocks hb_out hb_out' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial
  ac_nf at hpost_sep ⊢

theorem hmac_sha256_ok_of_hkdfContracts
    {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hHkdf : HkdfContractsExt img C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr "libsignal_protocol::crypto::hmac_sha256")
      ((hmacSpecWithStack C.F (2048 + extHookStack)).inImage img) :=
  hmac_sha256_ok_of_nfs_x himg hHkdf.memcpy hHkdf.memset hHkdf.compress256
    (new_from_slice_ok_ext' img C ext himg hHkdf)

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX
