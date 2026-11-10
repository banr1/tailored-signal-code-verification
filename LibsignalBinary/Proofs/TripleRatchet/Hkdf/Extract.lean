/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceExt

/-!
# Verification of `<GenericHkdf<Hmac<Sha256>>>::extract`

Assembles segment proofs for `GenericHkdf<Hmac<Sha256>>::extract` to establish
`extractSpec` on `tripleRatchetProgAt`, `tripleRatchetProgAtExt`, and under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Extract

private theorem extract_salt_props {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64} {R : SepProp}
    (hb_stk : IsBlock (memRegion (sp0 - 544#64) 976) (sp0 - 544#64) 976 (fun _ => True))
    (hsep : s0.mem ⊨
      (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
        memRegion (sp0 - 544#64) 976) ∗ R) :
    ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      RW s0.mem x.saltA 32 ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976 := by
  intro sv hsalt
  have hsep_salt : s0.mem ⊨ (⌜x.saltA ≠ 0#64⌝ ∗ (x.saltA ↦ₛ sv.toList)) ∗
      (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ (memRegion (sp0 - 544#64) 976 ∗ R))) := by
    have hsep' := hsep
    rw [hsalt] at hsep'
    dsimp only [optSaltAt] at hsep'
    ac_nf at hsep' ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsep_salt
  rcases hsep_salt with ⟨hne, hsep_sv⟩
  have hb_sv := IsBlock.pointsToBytes_len (a := x.saltA) sv.2
  have hsep_sv_stk : s0.mem ⊨ (x.saltA ↦ₛ sv.toList) ∗
      (memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ R))) := by
    ac_nf at hsep_sv ⊢
  have hsv_mem : s0.mem.readBytes x.saltA 32 = sv.toList := by
    have h := (hb_sv.read hsep_sv).2
    rwa [sv.2] at h
  have hrw_sv : RW s0.mem x.saltA 32 :=
    fun a ha => hb_sv.permNoLazy_rw hsep_sv ha
  have hd_sv_stk : DisjointRegions x.saltA 32 (sp0 - 544#64) 976 :=
    hb_sv.disjoint hb_stk (by decide) (by decide) hsep_sv_stk
  exact ⟨hne, hsv_mem, hrw_sv, hd_sv_stk⟩

theorem extract_ok_ext (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State)) [HkdfHooks C.F ext]
    (hNfs : NewFromSliceOkExt img C ext) :
    ExtractOkExt img C ext := by
  unfold ExtractOkExt
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr extractName = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") := by
    unfold tripleRatchetProgAtExt extractName
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")]
  rw [hfn]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, extractSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrz0, hsym0⟩, ⟨hx0, hx1, hx2, hsalt_none, hx3, hx4, hikm_len⟩, hsep⟩
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let R_rest : SepProp := optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗ R
  change s0.mem ⊨
    (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 976#64) 976) ∗ R at hsep
  rw [hsp_m976] at hsep
  have hb_ret := IsBlock.memRegion x.ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := x.ikmA) hikm_len
  have hb_stk := IsBlock.memRegion (sp0 - 544#64) 976
  have hsep_ret_stk : s0.mem ⊨ memRegion x.ret 0xb0 ∗ (memRegion (sp0 - 544#64) 976 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗
      (memRegion x.ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ (memRegion (sp0 - 544#64) 976 ∗ R))) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ R))) := by
    ac_nf at hsep ⊢
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA 32 :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm := by
    have h := (hb_ikm.read hsep_ikm_ret).2
    rwa [hikm_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stk_sub hRW_stk sp0 432 hsub_432
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsalt_props := extract_salt_props hb_stk hsep
  have hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact rw_stk_sub hRW_stk (sp0 + 144#64) 32 hsub_144
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact (hsalt_props sv hsalt).2.2.1
  have hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 - 544#64) 544 hsub_544
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 + 176#64) 0x98 hsub_176
  have h0 := RunsTo.toE (seg0_runsTo (img := img) (ext := ext)
    hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
    (fun sv hsv => ⟨(hsalt_props sv hsv).1, (hsalt_props sv hsv).2.1, (hsalt_props sv hsv).2.2.2⟩))
  have h1 := RunsToE.trans_full h0 fun s hs hkf hsym =>
    nfs1_runsTo hNfs hfrz0 hkf hsym0 hsym hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    RunsTo.toE (seg1a_runsTo hRW_stk hsp_al hs)
  have h3 := h2.trans fun s hs =>
    RunsTo.toE (seg1b_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h4 := h3.trans fun s hs =>
    RunsTo.toE (seg1c_runsTo hRW_stk hsp_al hs)
  have h5 := h4.trans fun s hs =>
    RunsTo.toE (fin_runsTo (fun hpre => FinalizeFixedProof.finalize_fixed_runsTo_ext hpre) hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    RunsTo.toE (seg2_runsTo hsp_al hs)
  have h7 := RunsToE.trans_full h6 fun s hs hkf hsym =>
    nfs2_runsTo hNfs hfrz0 hkf hsym0 hsym hRW_stk hsp_al hs
  have h8 := h7.trans fun s hs =>
    RunsTo.toE (seg3_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)
  refine h8.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [Spec.inImage, extractSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hb_prk := IsBlock.pointsToBytes_len (a := x.ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [])
      x.ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes x.ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (x.ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 544#64) 976 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  change sf.mem ⊨
    ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 976#64) 976) ∗ R
  rw [hsp_m976]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

theorem extract_ok_trap (img : Obj.Image) (C : Crypto)
    (abs : String → Option (State → State))
    (hNfs : NewFromSliceOk_trap img C abs) :
    ExtractOk_trap img C abs :=
  extract_ok_ext img C (trTrapExterns C abs) hNfs

theorem extract_ok (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hNfs : NewFromSliceOk img C ctl abs) :
    ExtractOk img C ctl abs :=
  extract_ok_ext img C (tripleRatchetExterns C ctl abs) hNfs

/-! ## Contract-Backed `ExtractOkExt'` at `extractStackExt` (`17360` B) -/

namespace HkdfExt.ExtractX

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

open Extract HkdfExt

abbrev ExtFrameX (s0 : State) (sp0 : BitVec 64) (m : Memory) : Prop :=
  S2Frame s0.mem m [(s0.readReg64 .x0, 0xb0), (sp0 - 16928#64, 17360)]

theorem rw_stkX_sub {m : Memory} {sp0 : BitVec 64}
    (hrw : RW m (sp0 - 16928#64) 17360) (addr : BitVec 64) (sz : ℕ)
    (hsub : (addr - (sp0 - 16928#64)).toNat + sz ≤ 17360) :
    RW m addr sz := by
  intro a ha
  apply hrw a
  simp only [InRegion] at ha ⊢
  bv_omega

theorem rw_sp0_sub {m : Memory} {sp0 : BitVec 64}
    (hrw : RW m sp0 432) (addr : BitVec 64) (sz : ℕ)
    (hsub : (addr - sp0).toNat + sz ≤ 432) :
    RW m addr sz := by
  intro a ha
  apply hrw a
  simp only [InRegion] at ha ⊢
  bv_omega

theorem disj_stkX_sub_right {a : BitVec 64} {n : ℕ} {sp0 : BitVec 64}
    (hd : DisjointRegions a n (sp0 - 16928#64) 17360) (addr : BitVec 64) (sz : ℕ)
    (hsub : 0 < sz ∧ (addr - (sp0 - 16928#64)).toNat + sz ≤ 17360) :
    DisjointRegions a n addr sz :=
  hd.sub_right addr hsub

theorem ExtSaved.changeSetMem {s0 : State} {sp0 : BitVec 64} {m1 m : Memory} :
    ExtSaved (s0.setMem m1) sp0 m ↔ ExtSaved s0 sp0 m := by
  constructor <;> intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ <;>
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem ExtFrameX.of_extFrame {s0 : State} {sp0 : BitVec 64} {m1 m2 : Memory}
    (hf1 : ExtFrameX s0 sp0 m1) (hf2 : ExtFrame (s0.setMem m1) sp0 m2) :
    ExtFrameX s0 sp0 m2 := by
  refine hf1.trans (hf2.mono fun a ha => ?_)
  have hout : OutsideRegion (s0.readReg64 .x0) 0xb0 a :=
    ha (s0.readReg64 .x0, 0xb0) (by simp)
  have hstk : OutsideRegion (sp0 - 16928#64) 17360 a :=
    ha (sp0 - 16928#64, 17360) (by simp)
  intro r hr
  simp only [State.readReg64_setMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout
  · simp only [OutsideRegion] at hstk ⊢
    bv_omega

theorem ExtFrameX.of_agreesOutside_sp0 {s0 : State} {sp0 : BitVec 64} {m m' : Memory} {n : ℕ}
    (hf : ExtFrameX s0 sp0 m) (hn : n ≤ 432) (hag : AgreesOutside m m' sp0 n) :
    ExtFrameX s0 sp0 m' := by
  refine hf.trans ((S2Frame.of_frame (frame_of_agreesOutside hag)).mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 16928#64) 17360 a :=
    ha (sp0 - 16928#64, 17360) (by simp)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [OutsideRegion] at hstk ⊢
  bv_omega

theorem ExtFrameX.trans_pair {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ}
    (hf₁ : ExtFrameX s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂)])
    (hsub₁ : (a₁ - (sp0 - 16928#64)).toNat + n₁ ≤ 17360)
    (hsub₂ : (a₂ - (sp0 - 16928#64)).toNat + n₂ ≤ 17360) :
    ExtFrameX s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 16928#64) 17360 a :=
    ha (sp0 - 16928#64, 17360) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  exact ⟨by bv_omega, by bv_omega⟩

theorem ExtFrameX.trans_triple {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ} {a₃ : BitVec 64} {n₃ : ℕ}
    (hf₁ : ExtFrameX s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂), (a₃, n₃)])
    (hsub₁ : (a₁ - (sp0 - 16928#64)).toNat + n₁ ≤ 17360)
    (hsub₂ : (a₂ - (sp0 - 16928#64)).toNat + n₂ ≤ 17360)
    (hsub₃ : (a₃ - (sp0 - 16928#64)).toNat + n₃ ≤ 17360) :
    ExtFrameX s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 16928#64) 17360 a :=
    ha (sp0 - 16928#64, 17360) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  exact ⟨by bv_omega, by bv_omega, by bv_omega⟩

theorem hmacSt_of_memcpy_32_write8_pos {m m1 : Memory} {sp0 : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key ikm : List (BitVec 8)}
    (hhm : HmacSt m sp0 F key [])
    (hrw : RW m sp0 432)
    (hikm_len : ikm.length = 32)
    (hdst1 : m1.readBytes sp0 32 = ikm)
    (hfr_mc : S2Frame m m1 [(sp0, 32), (sp0 - 16384#64, 16384)]) :
    HmacSt (m1.write8 (sp0 + 63#64) 32#8) sp0 F key ikm := by
  let m2 := m1.write8 (sp0 + 63#64) 32#8
  have hag2 : AgreesOutside m1 m2 (sp0 + 63#64) 1 :=
    (AgreesOutside.rfl' m1 (sp0 + 63#64) 1).write8 (by simp only [InRegion]; bv_omega)
  have hf2 : S2Frame m1 m2 [(sp0 + 63#64, 1)] :=
    S2Frame.of_frame (frame_of_agreesOutside hag2)
  have hfr64 : S2Frame m m2 [(sp0, 64), (sp0 - 16384#64, 16384)] := by
    refine (hfr_mc.mono fun a ha => ?_).trans (hf2.mono fun a ha => ?_)
    · have h64 : OutsideRegion sp0 64 a := ha (sp0, 64) (by simp)
      have hext : OutsideRegion (sp0 - 16384#64) 16384 a := ha (sp0 - 16384#64, 16384) (by simp)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [OutsideRegion] at h64 ⊢; bv_omega
      · exact hext
    · have h64 : OutsideRegion sp0 64 a := ha (sp0, 64) (by simp)
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [OutsideRegion] at h64 ⊢; bv_omega
  have hrw1_32 : RW m1 sp0 32 :=
    hfr_mc.rw_of_rw sp0 32 (rw_sp0_sub hrw sp0 32 (by rw [BitVec.sub_self]; decide))
  have hd64 (off : BitVec 64) (sz : ℕ)
      (h1 : 64 ≤ off.toNat ∧ sz ≤ (0#64 - off).toNat)
      (h2 : 16384 ≤ (off + 16384#64).toNat ∧ sz ≤ (0#64 - (off + 16384#64)).toNat) :
      ∀ r ∈ [(sp0, (64 : ℕ)), (sp0 - 16384#64, 16384)], DisjointRegions r.1 r.2 (sp0 + off) sz := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_zero_off sp0 64 off sz h1
    · exact disj_sp0_sub_off sp0 16384#64 16384 off sz h2
  have hsub_40 : ((sp0 + 0x40#64) - sp0).toNat + 32 ≤ 432 := by
    have h : (sp0 + 0x40#64) - sp0 = 0x40#64 := by bv_lin
    rw [h]; decide
  have hsub_60 : ((sp0 + 0x60#64) - sp0).toNat + 8 ≤ 432 := by
    have h : (sp0 + 0x60#64) - sp0 = 0x60#64 := by bv_lin
    rw [h]; decide
  have hsub_68 : ((sp0 + 0x68#64) - sp0).toNat + 32 ≤ 432 := by
    have h : (sp0 + 0x68#64) - sp0 = 0x68#64 := by bv_lin
    rw [h]; decide
  have hsub_88 : ((sp0 + 0x88#64) - sp0).toNat + 8 ≤ 432 := by
    have h : (sp0 + 0x88#64) - sp0 = 0x88#64 := by bv_lin
    rw [h]; decide
  rcases hhm with ⟨_, _, _, hin, hinB, hout, houtB⟩
  change HmacSt m2 sp0 F key ikm
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hikm_len, hf2.readBytes_eq hrw1_32 ?_ (by decide), hdst1]
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact (disj_sp0_zero_off sp0 32 63#64 1 (by decide)).symm
  · dsimp [m2]
    rw [Memory.read8_write8_same, hikm_len]
  · rw [hfr64.readBytes_eq (rw_sp0_sub hrw (sp0 + 0x40#64) 32 hsub_40)
      (hd64 0x40#64 32 (by decide) (by decide)) (by decide), hin]
  · rw [hfr64.read64_eq (rw_sp0_sub hrw (sp0 + 0x60#64) 8 hsub_60)
      (hd64 0x60#64 8 (by decide) (by decide)), hinB]
  · rw [hfr64.readBytes_eq (rw_sp0_sub hrw (sp0 + 0x68#64) 32 hsub_68)
      (hd64 0x68#64 32 (by decide) (by decide)) (by decide), hout]
  · rw [hfr64.read64_eq (rw_sp0_sub hrw (sp0 + 0x88#64) 8 hsub_88)
      (hd64 0x88#64 8 (by decide) (by decide)), houtB]

abbrev ExtCommonX (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  s.status = .Running ∧
  s.sp = sp0 ∧
  s.readReg64 .x19 = s0.readReg64 .x0 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x29 = sp0 + 336#64 ∧
  ExtSaved s0 sp0 s.mem ∧
  ExtFrameX s0 sp0 s.mem

def ENfs1X (b : BitVec 64) (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = saltRegOf sp0 x ∧
  s.readReg64 .x2 = BitVec.ofNat 64 (saltSliceOf x).length ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = 32#64 ∧
  (∀ sv, x.salt = some sv → x.saltA ≠ 0#64) ∧
  s.mem.readBytes (saltPtrOf sp0 x) (saltSliceOf x).length = saltSliceOf x

def ERet1X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = 32#64 ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  HmacSt s.mem (sp0 + 184#64) F (effectiveSalt x.salt) []

def EMemcpyX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "memcpy") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 192) ∧
  s.readReg64 .x0 = sp0 ∧
  s.readReg64 .x1 = x.ikmA ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x21 = 32#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.readReg64 .x25 = 0#64 ∧
  HmacSt s.mem sp0 F (effectiveSalt x.salt) []

def EC88X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 328) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacSt s.mem sp0 F (effectiveSalt x.salt) x.ikm

def EFinX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) ∧
  s.readReg64 .x0 = sp0 + 144#64 ∧
  s.readReg64 .x1 = sp0 + 176#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacSt s.mem (sp0 + 176#64) F (effectiveSalt x.salt) x.ikm

def ERetFinX (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F

def ENfs2X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") ∧
  s.readReg64 .lr = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 396) ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = sp0 + 144#64 ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F

def ERet2X (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  ExtCommonX s0 sp0 s ∧
  s.pc = b + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 396) ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  s.mem.readBytes (sp0 + 144#64) 32 = x.prk F ∧
  HmacSt s.mem (sp0 + 184#64) F (x.prk F) []

def EPostX (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = x.prk F ∧
  HmacSt s'.mem (s0.readReg64 .x0 + 0x20#64) F (x.prk F) [] ∧
  ExtFrameX s0 sp0 s'.mem

section SegmentsX

variable {img : Obj.Image} {C : Crypto} {ext : String → Option (State → State)}

theorem seg0_x_runsTo {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hpc : s0.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract"))
    (hstat : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hrw_sp0 : s0.mem.RW sp0 432)
    (hsalt_none : x.salt = none → x.saltA = 0#64 ∨ s0.readReg64 .x2 = 0#64)
    (hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 16928#64) 17360) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s0 (ENfs1X img.base x s0 sp0) := by
  have hsub_976 : 0 < 976 ∧ ((sp0 - 544#64) - (sp0 - 16928#64)).toNat + 976 ≤ 17360 := by
    have heq : (sp0 - 544#64) - (sp0 - 16928#64) = 16384#64 := by bv_lin
    rw [heq]; decide
  have hcx := seg0_runsTo_cx (img := img) (ext := ext)
    hpc hstat hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
    (fun sv hsv => ⟨(hsalt_some sv hsv).1, (hsalt_some sv hsv).2.1,
      disj_stkX_sub_right (hsalt_some sv hsv).2.2 (sp0 - 544#64) 976 hsub_976⟩)
  refine hcx.mono fun s' hs' => ?_
  rcases hs' with ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩, hrest⟩
  have hset0 : s0.setMem s0.mem = s0 := by cases s0; rfl
  refine ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved',
    ExtFrameX.of_extFrame (S2Frame.refl s0.mem _) (by rw [hset0]; exact hframe')⟩, hrest⟩

theorem nfs1_x_runsTo (hNfs : NewFromSliceOkExt' img C ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hfrz0 : img.FrozenLoaded s0)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hsym0 : s0.symtab = img.symtab)
    (hsym : s.symtab = s0.symtab)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32)
    (hd_salt_16928 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 16928#64) 16928)
    (hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs1X img.base x s0 sp0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (ERet1X img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_some_ne, hsalt_mem⟩
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x98 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsub_16928 : 0 < 16928 ∧ ((sp0 - 16928#64) - (sp0 - 16928#64)).toNat + 16928 ≤ 17360 := by
    have heq : (sp0 - 16928#64) - (sp0 - 16928#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hrun := nfs_runsTo_ext_x hNfs
    (hfrz0.of_keepsFrozen hkf)
    (hsym.trans hsym0)
    hpc hstat hx0 hx1 hx2
    (saltSliceOf_length_le x)
    (pointsToBytes_saltRegOf_eq sp0 x hsalt_some_ne)
    hsalt_mem
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_x0.2))
    (hframe.rw_of_rw _ _ hRW_salt)
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_16928.2))
    hd_salt_176.symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16928#64 16928 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_16928)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8, hmacSt_saltSliceOf] at hhm
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16928#64 16928 336#64 96 (by decide)
  have hframe' : ExtFrameX s0 sp0 s'.mem :=
    ExtFrameX.trans_pair hframe hfr' hsub_x0.2 hsub_16928.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x20 hcs).trans hx20,
    (CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

theorem seg1a_x_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet1X img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EMemcpyX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx20, hx21, hok, hhm⟩
  have hsub_976 : ((sp0 - 544#64) - (sp0 - 16928#64)).toNat + 976 ≤ 17360 := by
    have heq : (sp0 - 544#64) - (sp0 - 16928#64) = 16384#64 := by bv_lin
    rw [heq]; decide
  have hrw_976 : RW (s0.setMem s.mem).mem (sp0 - 544#64) 976 :=
    hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_976)
  have hs_cx : ERet1 img.base C.F x (s0.setMem s.mem) sp0 s :=
    ⟨⟨hstat, hsp, hx19, hx27, hx29, ExtSaved.changeSetMem.mpr hsaved, S2Frame.refl s.mem _⟩,
      hpc, hx20, hx21, hok, hhm⟩
  refine (seg1a_runsTo_cx (img := img) (C := C) (ext := ext) hrw_976 hsp_al hs_cx).mono fun s' hs' => ?_
  rcases hs' with ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩, hrest⟩
  exact ⟨⟨hstat', hsp', hx19', hx27', hx29',
    ExtSaved.changeSetMem.mp hsaved', ExtFrameX.of_extFrame hframe hframe'⟩, hrest⟩

theorem seg1b_x_runsTo
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hfrz0 : img.FrozenLoaded s0)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hsym0 : s0.symtab = img.symtab)
    (hsym : s.symtab = s0.symtab)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 16928#64) 17360)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyX img.base C.F x s0 sp0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (EC88X img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx21, hx22, hx25, hhm⟩
  have hikm_s : s.mem.readBytes x.ikmA 32 = x.ikm := by
    rw [hframe.readBytes_eq hRW_ikm ?_ (by decide)]
    · exact hikm_mem0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hd_ikm_out.symm
      · exact hd_ikm_stk.symm
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hsub_32 : 0 < 32 ∧ (sp0 - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hsub_ext : 0 < 16384 ∧ ((sp0 - 16384#64) - (sp0 - 16928#64)).toNat + 16384 ≤ 17360 := by
    have heq : (sp0 - 16384#64) - (sp0 - 16928#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0_s : s.mem.RW sp0 432 :=
    hframe.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  have hrw_sp0_32 : s.mem.RW sp0 32 :=
    rw_sp0_sub hrw_sp0_s sp0 32 (by rw [BitVec.sub_self]; decide)
  have hrw_ikm_s : s.mem.RW x.ikmA 32 :=
    hframe.rw_of_rw x.ikmA 32 hRW_ikm
  have hrw_ext_s : s.mem.RW (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    exact hframe.rw_of_rw (sp0 - 16384#64) 16384 (rw_stkX_sub hRW_stk (sp0 - 16384#64) 16384 hsub_ext.2)
  have hd_dst_src : DisjointRegions sp0 32 x.ikmA 32 :=
    (disj_stkX_sub_right hd_ikm_stk sp0 32 hsub_32).symm
  have hd_dst_ext : DisjointRegions sp0 32 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    simpa [BitVec.add_zero, extHookStack] using
      (disj_sp0_sub_off sp0 16384#64 16384 0#64 32 (by decide)).symm
  have hd_src_ext : DisjointRegions x.ikmA 32 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp]
    exact disj_stkX_sub_right hd_ikm_stk (sp0 - 16384#64) 16384 hsub_ext
  have hmc := memcpy_subroutine_runsTo hMemcpy
    (bs := x.ikm)
    (hfrz0.of_keepsFrozen hkf)
    (hsym.trans hsym0)
    hpc hstat hx0 hx1
    (by rw [hx2, hikm_len]; rfl)
    (by rw [hikm_len]; exact hikm_s)
    (by rw [hikm_len]; exact hrw_sp0_32)
    (by rw [hikm_len]; exact hrw_ikm_s)
    hrw_ext_s
    (by rw [hikm_len]; exact hd_dst_src)
    (by rw [hikm_len]; exact hd_dst_ext)
    (by rw [hikm_len]; exact hd_src_ext)
    (by rw [hsp]; exact hsp_al)
  refine hmc.trans fun s1 hs1 => ?_
  rcases hs1 with ⟨hpc1, hstat1, hcc1, _, hdst1, _, hfr_mc⟩
  rw [hsp, hikm_len] at hfr_mc
  rw [hikm_len] at hdst1
  have hpc1' : s1.pc = img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 192) :=
    hpc1.trans hlr
  have hsp1 : s1.sp = sp0 := (Extract.CallingConventionPreserved.sp_eq hcc1).trans hsp
  have hx19_1 : s1.readReg64 .x19 = s0.readReg64 .x0 := (CallingConventionPreserved.x19 hcc1).trans hx19
  have hx21_1 : s1.readReg64 .x21 = 32#64 := (CallingConventionPreserved.x21 hcc1).trans hx21
  have hx22_1 : s1.readReg64 .x22 = sp0 + 176#64 := (CallingConventionPreserved.x22 hcc1).trans hx22
  have hx25_1 : s1.readReg64 .x25 = 0#64 := hcc1.2.2.2.2.2.2.2.1.trans hx25
  have hx27_1 : s1.readReg64 .x27 = s0.readReg64 .x27 := (CallingConventionPreserved.x27 hcc1).trans hx27
  have hx29_1 : s1.readReg64 .x29 = sp0 + 336#64 := (CallingConventionPreserved.x29 hcc1).trans hx29
  have hsaved1 : ExtSaved s0 sp0 s1.mem := by
    refine hsaved.of_s2frame hfr_mc (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_zero_off sp0 32 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16384#64 16384 336#64 96 (by decide)
  have hframe1 : ExtFrameX s0 sp0 s1.mem :=
    ExtFrameX.trans_pair hframe hfr_mc hsub_32.2 hsub_ext.2
  have hrw_sp0 : s1.mem.RW sp0 432 :=
    hframe1.rw_of_rw sp0 432 (rw_stkX_sub hRW_stk sp0 432 hsub_432)
  have htail : RunsTo (tripleRatchetProgAtExt img.base ext) s1 (EC88X img.base C.F x s0 sp0) := by
    iterate 3 s2_step
    refine RunsTo.refl ?_
    have hag : AgreesOutside s1.mem (s1.mem.write8 (sp0 + 63#64) 32#8) sp0 328 :=
      agreesOutside_sp0_write8 (AgreesOutside.rfl' s1.mem sp0 328) (by decide)
    unfold EC88X ExtCommonX
    simp (config := { decide := true }) only [State.readReg64_setMem, State.readReg64_setPC,
      State.readReg64_advancePC, State.readReg64_writeReg64,
      Reg.x19, Reg.x27, Reg.x29, Reg.x22, ite_false]
    dsimp only [State.setMem, State.setPC, State.advancePC, State.writeReg64]
    exact ⟨⟨hstat1, hsp1, hx19_1, hx27_1, hx29_1,
      hsaved1.of_agreesOutside_328 hag,
      ExtFrameX.of_agreesOutside_sp0 hframe1 (by decide) hag⟩,
      rfl, hx22_1, hmacSt_of_memcpy_32_write8_pos hhm hrw_sp0_s hikm_len hdst1 hfr_mc⟩
  exact RunsTo.toE htail

theorem seg1c_x_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EC88X img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EFinX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hhm⟩
  have hsub_976 : ((sp0 - 544#64) - (sp0 - 16928#64)).toNat + 976 ≤ 17360 := by
    have heq : (sp0 - 544#64) - (sp0 - 16928#64) = 16384#64 := by bv_lin
    rw [heq]; decide
  have hrw_976 : RW (s0.setMem s.mem).mem (sp0 - 544#64) 976 :=
    hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_976)
  have hs_cx : EC88 img.base C.F x (s0.setMem s.mem) sp0 s :=
    ⟨⟨hstat, hsp, hx19, hx27, hx29, ExtSaved.changeSetMem.mpr hsaved, S2Frame.refl s.mem _⟩,
      hpc, hx22, hhm⟩
  refine (seg1c_runsTo_cx (img := img) (C := C) (ext := ext) hrw_976 hsp_al hs_cx).mono fun s' hs' => ?_
  rcases hs' with ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩, hrest⟩
  exact ⟨⟨hstat', hsp', hx19', hx27', hx29',
    ExtSaved.changeSetMem.mp hsaved', ExtFrameX.of_extFrame hframe hframe'⟩, hrest⟩

theorem fin_x_runsTo (hFin : FinalizeFixedOkExt' img C ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hfrz0 : img.FrozenLoaded s0)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hsym0 : s0.symtab = img.symtab)
    (hsym : s.symtab = s0.symtab)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinX img.base C.F x s0 sp0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (ERetFinX img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : (sp0 + 144#64) - (sp0 - 16928#64) = 17072#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x90 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsub_m16528 : 0 < 16528 ∧ ((sp0 - 16528#64) - (sp0 - 16928#64)).toNat + 16528 ≤ 17360 := by
    have heq : (sp0 - 16528#64) - (sp0 - 16928#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hfin := finalize_fixed_runsTo_ext_x hFin
    (hfrz0.of_keepsFrozen hkf)
    (hsym.trans hsym0)
    hpc hstat hx0 hx1
    (by rw [effectiveSalt_length]; decide)
    (by omega)
    hhm
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_144.2))
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_176.2))
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_m16528.2))
    (disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide))
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16528#64 16528 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16528#64 16528 176#64 0x90 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hfin.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcc, hout, hfr'⟩
  rw [hsp] at hfr'
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16528#64 16528 336#64 96 (by decide)
  have hframe' : ExtFrameX s0 sp0 s'.mem :=
    ExtFrameX.trans_triple hframe hfr' hsub_144.2 hsub_176.2 hsub_m16528.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcc).trans hsp,
    (CallingConventionPreserved.x19 hcc).trans hx19,
    (CallingConventionPreserved.x27 hcc).trans hx27,
    (CallingConventionPreserved.x29 hcc).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x22 hcc).trans hx22, hout⟩

theorem seg2_x_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERetFinX img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (ENfs2X img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hprk⟩
  have hs_cx : ERetFin img.base C.F x (s0.setMem s.mem) sp0 s :=
    ⟨⟨hstat, hsp, hx19, hx27, hx29, ExtSaved.changeSetMem.mpr hsaved, S2Frame.refl s.mem _⟩,
      hpc, hx22, hprk⟩
  refine (seg2_runsTo_cx (img := img) (C := C) (ext := ext) hsp_al hs_cx).mono fun s' hs' => ?_
  rcases hs' with ⟨⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩, hrest⟩
  exact ⟨⟨hstat', hsp', hx19', hx27', hx29',
    ExtSaved.changeSetMem.mp hsaved', ExtFrameX.of_extFrame hframe hframe'⟩, hrest⟩

theorem nfs2_x_runsTo (hNfs : NewFromSliceOkExt' img C ext)
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hfrz0 : img.FrozenLoaded s0)
    (hkf : s0.mem.KeepsFrozen s.mem)
    (hsym0 : s0.symtab = img.symtab)
    (hsym : s.symtab = s0.symtab)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs2X img.base C.F x s0 sp0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (ERet2X img.base C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hprk⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : (sp0 + 144#64) - (sp0 - 16928#64) = 17072#64 := by bv_lin
    rw [heq]; decide
  have hsub_x0 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x98 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsub_16928 : 0 < 16928 ∧ ((sp0 - 16928#64) - (sp0 - 16928#64)).toNat + 16928 ≤ 17360 := by
    have heq : (sp0 - 16928#64) - (sp0 - 16928#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 16928#64)).toNat + 96 ≤ 17360 := by
    have heq : (sp0 + 336#64) - (sp0 - 16928#64) = 17264#64 := by bv_lin
    rw [heq]; decide
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hrw_144_s : s.mem.RW (sp0 + 144#64) 32 :=
    hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_144.2)
  have hrun := nfs32_runsTo_ext_x hNfs
    (hfrz0.of_keepsFrozen hkf)
    (hsym.trans hsym0)
    hpc hstat hx0 hx1 hx2
    hprk_len
    hprk
    (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_x0.2))
    hrw_144_s
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_16928.2))
    (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16928#64 16928 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 16928#64 16928 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hprk' : s'.mem.readBytes (sp0 + 144#64) 32 = x.prk C.F := by
    rw [hfr'.readBytes_eq hrw_144_s ?_ (by decide)]
    · exact hprk
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
      · exact disj_sp0_sub_off sp0 16928#64 16928 144#64 32 (by decide)
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 16928#64 16928 336#64 96 (by decide)
  have hframe' : ExtFrameX s0 sp0 s'.mem :=
    ExtFrameX.trans_pair hframe hfr' hsub_x0.2 hsub_16928.2
  exact ⟨⟨hstat', (Extract.CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr, (CallingConventionPreserved.x22 hcs).trans hx22, hok, hprk', hhm⟩

theorem seg3_x_runsTo {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hsp0 : s0.sp = sp0 + 432#64)
    (hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : RW s0.mem (sp0 - 16928#64) 17360)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 16928#64) 17360)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ERet2X img.base C.F x s0 sp0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (EPostX C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hx22, hok, hprk, hhm⟩
  have hsub_976 : 0 < 976 ∧ ((sp0 - 544#64) - (sp0 - 16928#64)).toNat + 976 ≤ 17360 := by
    have heq : (sp0 - 544#64) - (sp0 - 16928#64) = 16384#64 := by bv_lin
    rw [heq]; decide
  have hrw_out_s : RW (s0.setMem s.mem).mem ((s0.setMem s.mem).readReg64 .x0) 0xb0 :=
    hframe.rw_of_rw (s0.readReg64 .x0) 0xb0 hRW_out
  have hrw_976_s : RW (s0.setMem s.mem).mem (sp0 - 544#64) 976 :=
    hframe.rw_of_rw _ _ (rw_stkX_sub hRW_stk _ _ hsub_976.2)
  have hd_out_976 : DisjointRegions ((s0.setMem s.mem).readReg64 .x0) 0xb0 (sp0 - 544#64) 976 :=
    disj_stkX_sub_right hd_out_stk (sp0 - 544#64) 976 hsub_976
  have hs_cx : ERet2 img.base C.F x (s0.setMem s.mem) sp0 s :=
    ⟨⟨hstat, hsp, hx19, hx27, hx29, ExtSaved.changeSetMem.mpr hsaved, S2Frame.refl s.mem _⟩,
      hpc, hx22, hok, hprk, hhm⟩
  refine (seg3_runsTo_cx (img := img) (C := C) (ext := ext) (s0 := s0.setMem s.mem)
    hsp0 hrw_out_s hrw_976_s hd_out_976 hsp_al hs_cx).mono
    fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcallee, hprk', hhm', hframe'⟩
  exact ⟨hpc', hstat', hcallee, hprk', hhm', ExtFrameX.of_extFrame hframe hframe'⟩

end SegmentsX

theorem extract_salt_props_x {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64} {R : SepProp}
    (hb_stk : IsBlock (memRegion (sp0 - 16928#64) 17360) (sp0 - 16928#64) 17360 (fun _ => True))
    (hsep : s0.mem ⊨
      (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
        memRegion (sp0 - 16928#64) 17360) ∗ R) :
    ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      RW s0.mem x.saltA 32 ∧
      DisjointRegions x.saltA 32 (sp0 - 16928#64) 17360 := by
  intro sv hsalt
  have hsep_salt : s0.mem ⊨ (⌜x.saltA ≠ 0#64⌝ ∗ (x.saltA ↦ₛ sv.toList)) ∗
      (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ (memRegion (sp0 - 16928#64) 17360 ∗ R))) := by
    have hsep' := hsep
    rw [hsalt] at hsep'
    dsimp only [optSaltAt] at hsep'
    ac_nf at hsep' ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsep_salt
  rcases hsep_salt with ⟨hne, hsep_sv⟩
  have hb_sv := IsBlock.pointsToBytes_len (a := x.saltA) sv.2
  have hsep_sv_stk : s0.mem ⊨ (x.saltA ↦ₛ sv.toList) ∗
      (memRegion (sp0 - 16928#64) 17360 ∗ (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ R))) := by
    ac_nf at hsep_sv ⊢
  have hsv_mem : s0.mem.readBytes x.saltA 32 = sv.toList := by
    have h := (hb_sv.read hsep_sv).2
    rwa [sv.2] at h
  have hrw_sv : RW s0.mem x.saltA 32 :=
    fun a ha => hb_sv.permNoLazy_rw hsep_sv ha
  have hd_sv_stk : DisjointRegions x.saltA 32 (sp0 - 16928#64) 17360 :=
    hb_sv.disjoint hb_stk (by decide) (by decide) hsep_sv_stk
  exact ⟨hne, hsv_mem, hrw_sv, hd_sv_stk⟩

end HkdfExt.ExtractX

open HkdfExt.ExtractX in
theorem extract_ok_ext'_of_memcpy {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    (hFin : FinalizeFixedOkExt' img C ext)
    (hNfs : NewFromSliceOkExt' img C ext) :
    ExtractOkExt' img C ext := by
  unfold ExtractOkExt'
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr extractName =
      img.base + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") := by
    unfold tripleRatchetProgAtExt extractName
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract")]
  rw [hfn]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, extractSpecExt] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrz0, hsym0⟩, ⟨hx0, hx1, hx2, hsalt_none, hx3, hx4, hikm_len⟩, hsep⟩
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m17360 : s0.sp - 17360#64 = sp0 - 16928#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let R_rest : SepProp := optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗ R
  change s0.mem ⊨
    (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 17360#64) 17360) ∗ R at hsep
  rw [hsp_m17360] at hsep
  have hb_ret := IsBlock.memRegion x.ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := x.ikmA) hikm_len
  have hb_stk := IsBlock.memRegion (sp0 - 16928#64) 17360
  have hsep_ret_stk : s0.mem ⊨ memRegion x.ret 0xb0 ∗ (memRegion (sp0 - 16928#64) 17360 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 16928#64) 17360 ∗
      (memRegion x.ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ (memRegion (sp0 - 16928#64) 17360 ∗ R))) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion (sp0 - 16928#64) 17360 ∗ (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ R))) := by
    ac_nf at hsep ⊢
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 16928#64) 17360 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA 32 :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 16928#64) 17360 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm := by
    have h := (hb_ikm.read hsep_ikm_ret).2
    rwa [hikm_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 16928#64) 17360 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsub_432 : (sp0 - (sp0 - 16928#64)).toNat + 432 ≤ 17360 := by
    have heq : sp0 - (sp0 - 16928#64) = 16928#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stkX_sub hRW_stk sp0 432 hsub_432
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 16928#64)).toNat + 32 ≤ 17360 := by
    have heq : (sp0 + 144#64) - (sp0 - 16928#64) = 17072#64 := by bv_lin
    rw [heq]; decide
  have hsub_16928 : 0 < 16928 ∧ ((sp0 - 16928#64) - (sp0 - 16928#64)).toNat + 16928 ≤ 17360 := by
    have heq : (sp0 - 16928#64) - (sp0 - 16928#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 16928#64)).toNat + 0x98 ≤ 17360 := by
    have heq : (sp0 + 176#64) - (sp0 - 16928#64) = 17104#64 := by bv_lin
    rw [heq]; decide
  have hsalt_props := extract_salt_props_x hb_stk hsep
  have hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact rw_stkX_sub hRW_stk (sp0 + 144#64) 32 hsub_144
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact (hsalt_props sv hsalt).2.2.1
  have hd_salt_16928 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 16928#64) 16928 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact (disj_sp0_sub_off sp0 16928#64 16928 144#64 32 (by decide)).symm
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stkX_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 - 16928#64) 16928 hsub_16928
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stkX_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 + 176#64) 0x98 hsub_176
  have h0 := RunsTo.toE (seg0_x_runsTo (img := img) (ext := ext)
    hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
    (fun sv hsv => ⟨(hsalt_props sv hsv).1, (hsalt_props sv hsv).2.1, (hsalt_props sv hsv).2.2.2⟩))
  have h1 := RunsToE.trans_full h0 fun s hs hkf hsym =>
    nfs1_x_runsTo hNfs hfrz0 hkf hsym0 hsym hRW_stk hRW_salt hd_salt_16928 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    RunsTo.toE (seg1a_x_runsTo hRW_stk hsp_al hs)
  have h3 := RunsToE.trans_full h2 fun s hs hkf hsym =>
    seg1b_x_runsTo hMemcpy hfrz0 hkf hsym0 hsym hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs
  have h4 := h3.trans fun s hs =>
    RunsTo.toE (seg1c_x_runsTo hRW_stk hsp_al hs)
  have h5 := RunsToE.trans_full h4 fun s hs hkf hsym =>
    fin_x_runsTo hFin hfrz0 hkf hsym0 hsym hRW_stk hikm_len hsp_al hs
  have h6 := h5.trans fun s hs =>
    RunsTo.toE (seg2_x_runsTo hsp_al hs)
  have h7 := RunsToE.trans_full h6 fun s hs hkf hsym =>
    nfs2_x_runsTo hNfs hfrz0 hkf hsym0 hsym hRW_stk hsp_al hs
  have h8 := h7.trans fun s hs =>
    RunsTo.toE (seg3_x_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)
  refine h8.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [Spec.inImage, extractSpecExt]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrameX at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hb_prk := IsBlock.pointsToBytes_len (a := x.ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [])
      x.ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes x.ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (x.ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 16928#64) 17360 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  change sf.mem ⊨
    ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 17360#64) 17360) ∗ R
  rw [hsp_m17360]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

theorem extract_ok_ext'_of_nfs (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State))
    (hHkdf : HkdfContractsExt img C.F ext)
    (hNfs : NewFromSliceOkExt' img C ext) :
    ExtractOkExt' img C ext :=
  extract_ok_ext'_of_memcpy hHkdf.memcpy (finalize_fixed_ok_ext' img C ext hHkdf) hNfs

theorem extract_ok_ext' (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hHkdf : HkdfContractsExt img C.F ext) :
    ExtractOkExt' img C ext :=
  extract_ok_ext'_of_nfs img C ext hHkdf (new_from_slice_ok_ext' img C ext himg hHkdf)

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

/-- Relocatable `[LibsignalPlacement]` contract predicate for `extract`. -/
abbrev ExtractPlacedOk [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
    (withLsCodeLoaded lsmpl (extractSpec C.F))

/-- Relocatable `subroutine_ok` for `extract` parameterized by any frozen-preserved
memory invariant `Inv` implying `LibsignalCodeLoaded lsmpl`. -/
theorem extract_placed_ok_of_inv [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H]
    {Inv : Memory → Prop}
    (hInv_kf : ∀ {m1 m2 : Memory}, Inv m1 → m1.KeepsFrozen m2 → Inv m2)
    (hInv_cl : ∀ {m : Memory}, Inv m → LibsignalCodeLoaded lsmpl m)
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with pre := fun x s0 => (newFromSliceSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ }) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
      { extractSpec C.F with pre := fun x s0 => (extractSpec C.F).pre x s0 ∗ ⌜Inv s0.mem⌝ } := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [extractSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hInv0, ⟨hx0, hx1, hx2, hsalt_none, hx3, hx4, hikm_len⟩, hsep⟩
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hInv_cl hInv0
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let R_rest : SepProp := optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗ R
  change s0.mem ⊨
    (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 976#64) 976) ∗ R at hsep
  rw [hsp_m976] at hsep
  have hb_ret := IsBlock.memRegion x.ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := x.ikmA) hikm_len
  have hb_stk := IsBlock.memRegion (sp0 - 544#64) 976
  have hsep_ret_stk : s0.mem ⊨ memRegion x.ret 0xb0 ∗ (memRegion (sp0 - 544#64) 976 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗
      (memRegion x.ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ (memRegion (sp0 - 544#64) 976 ∗ R))) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ R))) := by
    ac_nf at hsep ⊢
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA 32 :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm := by
    have h := (hb_ikm.read hsep_ikm_ret).2
    rwa [hikm_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stk_sub hRW_stk sp0 432 hsub_432
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsalt_props := extract_salt_props hb_stk hsep
  have hRW_salt : RW s0.mem (saltPtrOf sp0 x) 32 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact rw_stk_sub hRW_stk (sp0 + 144#64) 32 hsub_144
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact (hsalt_props sv hsalt).2.2.1
  have hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 - 544#64) 544 hsub_544
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 + 176#64) 0x98 hsub_176
  have h0 := RunsTo.toE (seg0_placed_runsTo (H := H)
    hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
    (fun sv hsv => ⟨(hsalt_props sv hsv).1, (hsalt_props sv hsv).2.1, (hsalt_props sv hsv).2.2.2⟩))
  have h1 := RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_placed_runsTo hNfs (hInv_kf hInv0 hkf) hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    RunsTo.toE (seg1a_placed_runsTo hRW_stk hsp_al hs)
  have h3 := h2.trans fun s hs =>
    RunsTo.toE (seg1b_placed_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h4 := h3.trans fun s hs =>
    RunsTo.toE (seg1c_placed_runsTo hRW_stk hsp_al hs)
  have h5 := RunsToE.trans_full h4 fun s hs hkf _ =>
    RunsTo.toE (fin_placed_runsTo
      (fun hpre => FinalizeFixedProof.finalize_fixed_placed_runsTo_of_other_block
        (fun i hi hunmut ext panics svc => (hcl0 i hi hunmut ext panics svc).of_keepsFrozen hkf) hpre)
      hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    RunsTo.toE (seg2_placed_runsTo hsp_al hs)
  have h7 := RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_placed_runsTo hNfs (hInv_kf hInv0 hkf) hRW_stk hsp_al hs
  have h8 := h7.trans fun s hs =>
    RunsTo.toE (seg3_placed_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)
  refine h8.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [extractSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hb_prk := IsBlock.pointsToBytes_len (a := x.ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [])
      x.ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes x.ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (x.ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 544#64) 976 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  change sf.mem ⊨
    ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 976#64) 976) ∗ R
  rw [hsp_m976]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

theorem extract_placed_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F))) :
    ExtractPlacedOk C H :=
  extract_placed_ok_of_inv C H
    (fun hcl hkf i hi hunmut ext panics svc => (hcl i hi hunmut ext panics svc).of_keepsFrozen hkf)
    (fun hcl => hcl)
    hNfs

theorem extract_placed_ok_of_plain [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (newFromSliceSpec C.F)) :
    ExtractPlacedOk C H :=
  extract_placed_ok C H (subroutine_ok_withLsCodeLoaded_of_plain hNfs)

end CryptoVerification.LibsignalTripleRatchet
