/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegsExact

/-!
# `HookSat` Relocatable Verification of `extract`

Establishes `ExtractPlacedOk` for `GenericHkdf<Hmac<Sha256>>::extract` under
`[HkdfPlacedHooksSat C.F H]`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSat

open Arm64 ProofLib
open CryptoGames.HKDF (hkdfExtract)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved ExtractGhost ExtractPlacedOk HmacSt RW
   RunsTo TraceEq blkPC_54 blkPl_54 effectiveSalt extPlacedFakeB extPlacedFakeB_off_328
   extPlacedFakeB_off_380 extractSpec finPlacedFakeB finPlacedFakeB_off_0 hmacCoreAt
   isBlock_hmacCoreAt length_hmacWith newFromSliceSpec optSaltAt rw_of_perm_eq)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (EC88 EFinPlaced EMemcpyPlaced ERetFin ExtCommon ExtFrame ExtSaved
   ExtSaved_and_Frame_of_agreesOutside_328 RunsTo.toE RunsToE S2Frame agreesOutside_sp0_write8
   disj_sp0_off disj_sp0_sub_off disj_stk_sub_right effectiveSalt_length
   HmacSt.of_writeBytes_32_write8_pos nfs1_placed_runsTo nfs2_placed_runsTo rw_stk_sub saltPtrOf
   seg0_placed_runsTo seg1a_placed_runsTo seg1c_placed_runsTo seg2_placed_runsTo seg3_placed_runsTo
   sp0_aligned sp0_aligned_0b1111)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegsExact
  (seg1b_placed_runsTo_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat
  (FinPostSat finalize_fixed_placed_runsTo_of_other_block_sat)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

section SegmentsPlacedSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}

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

private theorem extFrame_trans_triple_s2 {s0 : State} {sp0 : BitVec 64} {m m' : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ} {a₃ : BitVec 64} {n₃ : ℕ}
    (hf₁ : ExtFrame s0 sp0 m) (hf₂ : S2Frame m m' [(a₁, n₁), (a₂, n₂), (a₃, n₃)])
    (hsub₁ : (a₁ - (sp0 - 544#64)).toNat + n₁ ≤ 976)
    (hsub₂ : (a₂ - (sp0 - 544#64)).toNat + n₂ ≤ 976)
    (hsub₃ : (a₃ - (sp0 - 544#64)).toNat + n₃ ≤ 976) :
    ExtFrame s0 sp0 m' := by
  refine hf₁.trans (hf₂.mono fun a ha => ?_)
  have hstk : OutsideRegion (sp0 - 544#64) 976 a :=
    ha (sp0 - 544#64, 976) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  simp only [OutsideRegion] at hstk ⊢
  exact ⟨by bv_omega, by bv_omega, by bv_omega⟩

theorem seg1b_placed_runsTo_sat [hH : HkdfPlacedHooksExactSat C.F H]
    {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : RW s0.mem x.ikmA 32)
    (hikm_len : x.ikm.length = 32)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EMemcpyPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (EC88 extPlacedFakeB C.F x s0 sp0) :=
  seg1b_placed_runsTo_exact hH.memcpy
    hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs

theorem fin_placed_runsTo_sat {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hFin :
      FinPre finPlacedFakeB C.F (effectiveSalt x.salt) x.ikm s →
      RunsTo ((blkPC_54).rebase (blkPl_54).base H) s
        (FinPostSat C.F (effectiveSalt x.salt) x.ikm s))
    (hRW_stk : RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s (ERetFin extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x90 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_m144 : 0 < 144 ∧ ((sp0 - 144#64) - (sp0 - 544#64)).toNat + 144 ≤ 976 := by
    have heq : (sp0 - 144#64) - (sp0 - 544#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrw_336 : RW s.mem (sp0 + 336#64) 96 :=
    hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)
  have hpre : FinPre finPlacedFakeB C.F (effectiveSalt x.salt) x.ikm s :=
    { pc_eq := hpc.trans finPlacedFakeB_off_0.symm
      status := hstat
      key_le := by rw [effectiveSalt_length]; decide
      msg_lt := by omega
      hmac_st := by rw [hx1]; exact hhm
      rw_out := by rw [hx0]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144.2)
      rw_hm := by rw [hx1]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_176.2)
      rw_fsp := by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_m144.2)
      disj_out_hm := by rw [hx0, hx1]; exact disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide)
      disj_out_fsp := by rw [hx0, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by rw [hx1, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact sp0_aligned_0b1111 hsp_al }
  refine (hFin hpre).mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0] at hout
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' hrw_336 ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 144#64 144 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    extFrame_trans_triple_s2 hframe hfr' hsub_144.2 hsub_176.2 hsub_m144.2
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) := by
    rw [hlr, extPlacedFakeB_off_380]
  exact ⟨⟨hstat', hcs.sp_eq.trans hsp, (CalleeSaved.x19 hcs).trans hx19,
    (CalleeSaved.x27 hcs).trans hx27,
    (CalleeSaved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CalleeSaved.x22 hcs).trans hx22, hout⟩

end SegmentsPlacedSat

theorem extract_placed_ok_of_inv_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H]
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
    RunsTo.toE (seg1b_placed_runsTo_sat (C := C) hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h4 := h3.trans fun s hs =>
    RunsTo.toE (seg1c_placed_runsTo hRW_stk hsp_al hs)
  have h5 := RunsToE.trans_full h4 fun s hs hkf _ =>
    RunsTo.toE (fin_placed_runsTo_sat
      (fun hpre => finalize_fixed_placed_runsTo_of_other_block_sat (C := C) (H := H)
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

theorem extract_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl (newFromSliceSpec C.F))) :
    ExtractPlacedOk C H :=
  extract_placed_ok_of_inv_sat C H
    (fun hcl hkf i hi hunmut ext panics svc => (hcl i hi hunmut ext panics svc).of_keepsFrozen hkf)
    (fun hcl => hcl)
    hNfs

theorem extract_placed_ok_of_plain_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H]
    (hNfs : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (newFromSliceSpec C.F)) :
    ExtractPlacedOk C H :=
  extract_placed_ok_sat C H (subroutine_ok_withLsCodeLoaded_of_plain hNfs)

end LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSat
