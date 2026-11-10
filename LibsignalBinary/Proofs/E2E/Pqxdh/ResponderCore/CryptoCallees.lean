/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import all Init.Data.String.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLong
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain

/-!
# Unconditional In-Image Crypto Callees and PQXDH Responder Entry Points

Discharges `PqxdhHkdfExpandMultiInfoOk` (`0x1a874`, `64` / `80` / `96` B) and `PqxdhHkdfExtractOk`
(`0x1ad38`, `salt = None` and `salt = Some`), and derives unconditional `subroutine_ok` contracts
for `<HandshakeKeys>::derive` (`0x1ceb8`) and `Pqxdh::accept` (`0x23920`) on `trTrapProgAt`,
`tripleRatchetProgAt`, and `tripleRatchetProgAtExt`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalHmac
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-! ## 1. `expand_multi_info` (`0x1a874`) for `k = 12` (`96` B, `info = INFO_PQXDH`) and
  `PqxdhHkdfExpandMultiInfoOk` -/

/-- `Spec` for `expand_multi_info` (`b + 0x1a874`) when `okmLen = 96` and `info.length = 46`. -/
def expandMultiInfo96_46Spec (F : ShaState → List (BitVec 8) → ShaState) :
    Spec ExpandMultiInfoGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hkdfA ∧
      s.readReg64 .x1 = x.infoHdrA ∧
      s.readReg64 .x2 = x.okmA ∧
      s.readReg64 .x3 = 96#64 ∧
      x.prk.length ≤ 64 ∧
      x.info.length = 46 ∧
      x.okmLen = 96⌝ ∗
    hmacCoreAt F x.hkdfA x.prk [] ∗
    (x.infoHdrA ↦₆₄ x.infoA) ∗
    ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
    (x.infoA ↦ᵣ x.info) ∗
    memRegion x.okmA 96 ∗
    stackAt s.sp expandMultiInfoStack
  post := fun x s₀ sf =>
    ⌜sf.trace = s₀.trace⌝ ∗
    hmacCoreAt F x.hkdfA x.prk [] ∗
    (x.infoHdrA ↦₆₄ x.infoA) ∗
    ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
    (x.infoA ↦ᵣ x.info) ∗
    (x.okmA ↦ₛ hkdfExpand F x.prk x.info 96) ∗
    stackAt s₀.sp expandMultiInfoStack

private theorem ro_outside_rw {P Q R : SepProp} {b_ro b_rw : BitVec 64} {n_ro n_rw : ℕ}
    {Φ_ro Φ_rw : Memory → Prop} {m : Memory}
    (hro : IsBlockRO P b_ro n_ro Φ_ro)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ P ∗ (Q ∗ R)) :
    ∀ a, InRegion b_ro n_ro a → OutsideRegion b_rw n_rw a := by
  intro a ha_ro
  rw [outsideRegion_iff_not_inRegion]
  intro ha_rw
  have hsep' : m ⊨ Q ∗ (P ∗ R) := by simpa [sepConj_left_comm] using hsep
  have hm_reg : m ⊨ memRegion b_rw n_rw ∗ (P ∗ R) :=
    Satisfies.mono (Arm64.sepConj_mono_left (ProofLib.IsBlock.entails_memRegion hrw)) hsep'
  have hm_pn0 := Satisfies.setPermProtNone_of_memRegion hm_reg
  have hperm_pn := (IsBlockProtNone.memRegionProtNone b_rw n_rw).perm_protNone hm_pn0 ha_rw
  have hm_pn : m.setPermNonFrozen b_rw n_rw Perm.protNone ⊨ P ∗ (memRegionProtNone b_rw n_rw ∗ R) := by
    simpa [sepConj_left_comm] using hm_pn0
  have hpr := hro.perm_r hm_pn ha_ro
  rw [hperm_pn] at hpr
  cases hpr

/-- `subroutine_ok` for `expand_multi_info` (`b + 0x1a874`) at `okmLen = 96`, `info.length = 46`. -/
theorem expand_multi_info_96_46_ok_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr expandMultiInfoName)
      (expandMultiInfo96_46Spec C.F) := by
  have hfn : (trTrapProgAt b C abs).fnAddr expandMultiInfoName = b + 0x1a874#64 := by
    unfold trTrapProgAt expandMultiInfoName
    rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x1a874]
  rw [hfn]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [expandMultiInfo96_46Spec, stackAt, expandMultiInfoStack, finalizeFixedStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_len, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA 96 ∗
      memRegion (s0.sp - 640#64) 640) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) 46#64
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = 46#64) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA 96
  have hb_stk := IsBlock.memRegion (s0.sp - 640#64) 640
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (x.infoA ↦ᵣ x.info) ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA 96 ∗ (memRegion (s0.sp - 640#64) 640 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 640#64) 640 ∗ (memRegion x.okmA 96 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA 96 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (memRegion x.okmA 96 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
            (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA 96 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
            (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have h_exp_pre : ExpandPre96_46 b C.F x.prk x.info x.infoA s0 :=
    { pc_eq := hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_len_eq := hinfo_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := by rw [← hinfo_len]; exact hro_info.read hsep_info_stk
      read_x0 := by rw [hx0]; exact Memory.RW.readable (fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha)
      read_x1 := by rw [hx1]; exact Memory.RW.readable (fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha)
      rw_x2 := by rw [hx2]; exact fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
      rw_stack := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
      disj_x2_stack := by
        rw [hx2]; exact hb_okm.disjoint hb_stk (by decide) (by decide) hsep_okm_stk
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by
        rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) (by decide) hsep_hm_okm
      disj_x1_stack := by
        rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by
        rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) (by decide) hsep_hdr_okm
      out_info_stk := by rw [← hinfo_len]; exact ro_outside_rw hro_info hb_stk hsep_info_stk
      out_info_x2 := by rw [hx2, ← hinfo_len]; exact ro_outside_rw hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine (expand_multi_info_96_46_runsTo_trap h_exp_pre).to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [expandMultiInfo96_46Spec, stackAt, expandMultiInfoStack, finalizeFixedStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrame at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info 96).length = 96 := by
    rw [hkdfExpand_96_eq]
    simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info 96) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; decide, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info 96) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- `subroutine_ok` for `expand_multi_info` (`b + 0x1a874`) at `okmLen = 96`, `info.length = 46`. -/
theorem expand_multi_info_96_46_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr expandMultiInfoName)
      (expandMultiInfo96_46Spec C.F) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (expand_multi_info_96_46_ok_trap b C abs)

/-- `pqxdhHkdfExpandCellsSpec P img 12` (`96` B, `info = INFO_PQXDH`) from
`expand_multi_info_96_46_ok_trap`. -/
theorem pqxdhHkdfExpand_12_ok_trap {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img 12) := by
  have hexp := expand_multi_info_96_46_ok_trap img.base C absHooks
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsSpec] at hpre
  rw [Keys.stackAt_alloc_expand sp, ← memRegion_cells okmA 12 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_PQXDH := by
    rcases hcases with ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hinfo, _⟩
    · omega
    · omega
    · exact hinfo
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 46 := by subst hinfo; rfl_kernel
  have hinfo_len_bv : BitVec.ofNat 64 info.length = 46#64 := by rw [hinfo_len]
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega), hinfo_len_bv] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 96⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · dsimp only [expandMultiInfo96_46Spec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_len, trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [expandMultiInfo96_46Spec, pqxdhHkdfExpandCellsSpec] at hpost ⊢
    rw [Keys.stackAt_alloc_expand sp, hinfo_len_bv]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 12 = 96 from rfl, bytesToBv8_hkdfExpandRef_96 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ 46#64) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 96) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

/-- `pqxdhHkdfExpandCellsSpec P img 12` (`96` B, `info = INFO_PQXDH`) from
`expand_multi_info_96_46_ok`. -/
theorem pqxdhHkdfExpand_12_ok {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img 12) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdhHkdfExpand_12_ok_trap hP)

/-- Discharges `PqxdhHkdfExpandMultiInfoOk_trap` on `trTrapProgAt img.base C absHooks`
for all `k`. -/
theorem pqxdhHkdfExpandMultiInfo_ok_trap {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C) :
    PqxdhHkdfExpandMultiInfoOk_trap P img C absHooks := by
  intro k
  by_cases hk8 : k = 8
  · subst hk8; exact pqxdhHkdfExpand_8_ok_trap hP
  · by_cases hk10 : k = 10
    · subst hk10; exact pqxdhHkdfExpand_10_ok_trap hP
    · by_cases hk12 : k = 12
      · subst hk12; exact pqxdhHkdfExpand_12_ok_trap hP
      · exact pqxdhHkdfExpand_other_ok_trap P C img absHooks k hk8 hk10 hk12

/-! ## 2. `GenericHkdf::extract` (`0x1ad38`) and `PqxdhHkdfExtractOk_trap` -/

/-- Discharges `PqxdhHkdfExpandMultiInfoOk` on `tripleRatchetProgAt img.base C ctl absHooks`
for all `k`. -/
theorem pqxdhHkdfExpandMultiInfo_ok {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C) :
    PqxdhHkdfExpandMultiInfoOk P img C ctl absHooks := fun k => subroutine_ok_kit_of_trTrap (pqxdhHkdfExpandMultiInfo_ok_trap hP k)

private theorem sep_some_1 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      A ∗ (G ∗ (B ∗ C ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_2 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      G ∗ (A ∗ (B ∗ C ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_3 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      C ∗ (A ∗ (B ∗ S1 ∗ S2 ∗ S3 ∗ G ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_4 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      C ∗ (G ∗ (A ∗ B ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_5 (A B C S1 S2 S3 G S4 R : SepProp) :
    (A ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R =
      B ∗ (G ∗ (A ∗ C ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) := by ac_rfl

private theorem sep_some_post (P1 P2 B C S1 S2 S3 G S4 R : SepProp) :
    (P1 ∗ P2) ∗ (G ∗ (B ∗ C ∗ S1 ∗ S2 ∗ S3 ∗ S4 ∗ R)) =
      (P1 ∗ P2 ∗ B ∗ C ∗ S1 ∗ S2 ∗ (S3 ∗ G) ∗ S4) ∗ R := by ac_rfl

/-- `subroutine_ok` for `pqxdhHkdfExtractSomeSpec` (`0x1ad38`, `salt = Some`, `32`-B `ikm`). -/
theorem pqxdhHkdfExtractSome_ok_trap {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractSomeSpec P img) := by
  have hfn : (trTrapProgAt img.base C absHooks).fnAddr hkdfExtractSym =
      img.base + 0x1ad38#64 := by
    unfold trTrapProgAt hkdfExtractSym
    rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x1ad38]
  rw [hfn]
  refine subroutine_ok_intro fun ⟨ret, saltA, salt, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhHkdfExtractSomeSpec] at hpre
  rw [Keys.stackAt_alloc_extract sp] at hpre
  dsimp only [stackAt, extractStack, newFromSliceStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hx0, hx1, hx2, hx3, hx4, hsp_eq, hsalt_ne, hsalt_len, hikm_len⟩, hsep⟩
  subst hsp_eq
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let x : ExtractGhost := ⟨ret, saltA, some (u8Vec 32 salt), ikmA, bytesToBv8 ikm⟩
  have hsalt_list : (u8Vec 32 salt).toList = bytesToBv8 salt := u8Vec_toList_of_length hsalt_len
  have hikm_bv_len : x.ikm.length = 32 := by dsimp [x]; rw [bytesToBv8_length, hikm_len]
  rw [hsp_m976] at hsep
  change s0.mem ⊨
    (memRegion ret 0xb0 ∗
      (saltA ↦ₛ bytesToBv8 salt) ∗
      (ikmA ↦ₛ bytesToBv8 ikm) ∗
      memRegion (s0.sp - 8192#64) 3936 ∗
      memRegion (s0.sp - 4256#64) 160 ∗
      (memRegion (s0.sp - 4096#64) 3120 ∗ memRegion (sp0 - 544#64) 976) ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)) ∗ R at hsep
  let R_rest : SepProp :=
    (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
    memRegion (s0.sp - 4096#64) 3120 ∗
    ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE) ∗ R
  have hb_ret := IsBlock.memRegion ret 0xb0
  have hb_salt := IsBlock.pointsToBytes_len (a := saltA)
    (by rw [bytesToBv8_length, hsalt_len] : (bytesToBv8 salt).length = 32)
  have hb_ikm := IsBlock.pointsToBytes_len (a := ikmA) hikm_bv_len
  have hb_stk := IsBlock.memRegion (sp0 - 544#64) 976
  have hsep_ret_stk : s0.mem ⊨ memRegion ret 0xb0 ∗ (memRegion (sp0 - 544#64) 976 ∗ R_rest) := by
    dsimp only [R_rest]; rw [← sep_some_1]; exact hsep
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗ (memRegion ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; rw [← sep_some_2]; exact hsep
  have hsep_ikm_ret : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion ret 0xb0 ∗
        ((saltA ↦ₛ bytesToBv8 salt) ∗ memRegion (s0.sp - 8192#64) 3936 ∗
          memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗
          memRegion (sp0 - 544#64) 976 ∗ ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE) ∗ R)) := by
    rw [← sep_some_3]; exact hsep
  have hsep_ikm_stk : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗
        (memRegion ret 0xb0 ∗ (saltA ↦ₛ bytesToBv8 salt) ∗
          memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
          memRegion (s0.sp - 4096#64) 3120 ∗
            ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE) ∗ R)) := by
    rw [← sep_some_4]; exact hsep
  have hsep_salt_stk : s0.mem ⊨ (saltA ↦ₛ bytesToBv8 salt) ∗
      (memRegion (sp0 - 544#64) 976 ∗
        (memRegion ret 0xb0 ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
          memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
          memRegion (s0.sp - 4096#64) 3120 ∗
            ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE) ∗ R)) := by
    rw [← sep_some_5]; exact hsep
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
    rwa [hikm_bv_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsalt_some : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976 := by
    intro sv hsv
    injection hsv with hsv_eq
    subst hsv_eq
    refine ⟨hsalt_ne, ?_,
      hb_salt.disjoint hb_stk (by decide) (by decide) hsep_salt_stk⟩
    have h := (hb_salt.read hsep_salt_stk).2
    rw [bytesToBv8_length, hsalt_len] at h
    exact h.trans hsalt_list.symm
  have hruns := extract_32_ro_runsToE_trap (C := C) (abs := absHooks)
    himg (x := x) hpc hrun hF0.roData hsp0 hx1 (fun _ => hx2) hx3 hx4 hikm_bv_len hsp_al
    hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk
    (fun h => by nomatch h) hsalt_some
  refine hruns.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [pqxdhHkdfExtractSomeSpec]
  rw [Keys.stackAt_alloc_extract s0.sp]
  dsimp only [stackAt, extractStack, newFromSliceStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P (some salt) ikm) := by
    dsimp [x, ExtractGhost.prk]
    exact (bytesToBv8_hkdfExtractRef_some hP hsalt_len ikm).symm
  have hprk_ref_len : (hkdfExtractRef P (some salt) ikm).length = 32 := by
    have h := congrArg List.length hprk_eq.symm
    rw [bytesToBv8_length] at h
    exact h.trans (length_hmacWith C.F _ _)
  have hprk_len : (x.prk C.F).length = 32 := by
    rw [hprk_eq, bytesToBv8_length, hprk_ref_len]
  have hb_prk := IsBlock.pointsToBytes_len (a := ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [])
      ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 544#64) 976 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  rw [hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 0x20#64) (by omega)] at hpost_sep
  rw [hsp_m976]
  change sf.mem ⊨
    ((ret ↦ₛ bytesToBv8 (hkdfExtractRef P (some salt) ikm)) ∗
      pqxdhHmacStateAt P (ret + 0x20#64) (hkdfExtractRef P (some salt) ikm) ∗
      (saltA ↦ₛ bytesToBv8 salt) ∗
      (ikmA ↦ₛ bytesToBv8 ikm) ∗
      memRegion (s0.sp - 8192#64) 3936 ∗
      memRegion (s0.sp - 4256#64) 160 ∗
      (memRegion (s0.sp - 4096#64) 3120 ∗ memRegion (sp0 - 544#64) 976) ∗
      ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE)) ∗ R
  dsimp only [R_rest] at hpost_sep
  rw [← sep_some_post]
  exact hpost_sep

/-- `subroutine_ok` for `pqxdhHkdfExtractSomeSpec` (`0x1ad38`, `salt = Some`, `32`-B `ikm`). -/
theorem pqxdhHkdfExtractSome_ok {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractSomeSpec P img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdhHkdfExtractSome_ok_trap hP himg)

/-- `subroutine_ok` for `pqxdhHkdfExtractNoneSpec` (`0x1ad38`, `salt = None`,
`160` / `192` / `224`-B `ikm`). -/
theorem pqxdhHkdfExtractNone_ok_trap {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractNoneSpec P img) := by
  have hfn : (trTrapProgAt img.base C absHooks).fnAddr hkdfExtractSym =
      img.base + 0x1ad38#64 := by
    unfold trTrapProgAt hkdfExtractSym
    rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x1ad38]
  rw [hfn]
  refine subroutine_ok_intro fun ⟨ret, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhHkdfExtractNoneSpec] at hpre
  rw [Keys.stackAt_alloc_extract sp] at hpre
  dsimp only [stackAt, extractStack, newFromSliceStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hx0, hx1, hx3, hx4, hsp_eq, hikm_len⟩, hsep⟩
  subst hsp_eq
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let x : ExtractGhost := ⟨ret, 0#64, none, ikmA, bytesToBv8 ikm⟩
  have hikm_bv_len : x.ikm.length = ikm.length := by dsimp [x]; exact bytesToBv8_length ikm
  have hikm_cases : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224 := by
    rwa [hikm_bv_len]
  have hikm_pos : 0 < x.ikm.length := by omega
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by omega
  have hx4' : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length := by
    rw [hikm_bv_len]; exact hx4
  let R_rest : SepProp :=
    (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
    memRegion (s0.sp - 4096#64) 3120 ∗
    ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE) ∗ R
  rw [hsp_m976] at hsep
  have hb_ret := IsBlock.memRegion ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := ikmA) (rfl : x.ikm.length = x.ikm.length)
  have hb_stk := IsBlock.memRegion (sp0 - 544#64) 976
  have hsep_ret_stk : s0.mem ⊨ memRegion ret 0xb0 ∗ (memRegion (sp0 - 544#64) 976 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗ (memRegion ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion ret 0xb0 ∗
        (memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
          memRegion (s0.sp - 4096#64) 3120 ∗ memRegion (sp0 - 544#64) 976 ∗
          ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE) ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗
        (memRegion ret 0xb0 ∗ memRegion (s0.sp - 8192#64) 3936 ∗
          memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗
          ((img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) ↦ᵣ sha256IVBytesLE) ∗ R)) := by
    ac_nf at hsep ⊢
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA x.ikm.length :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm :=
    (hb_ikm.read hsep_ikm_ret).2
  have hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret hikm_pos (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk hikm_pos (by decide) hsep_ikm_stk
  have hruns := extract_none_long_ro_runsToE_trap (C := C) (abs := absHooks)
    himg (x := x) hpc hrun hF0.roData hsp0 hx1 hx3 hx4' rfl rfl hikm_cases hsp_al
    hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk
  refine hruns.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [pqxdhHkdfExtractNoneSpec]
  rw [Keys.stackAt_alloc_extract s0.sp]
  dsimp only [stackAt, extractStack, newFromSliceStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P none ikm) := by
    dsimp [x, ExtractGhost.prk]
    exact (bytesToBv8_hkdfExtractRef_none hP ikm).symm
  have hprk_ref_len : (hkdfExtractRef P none ikm).length = 32 := by
    have h := congrArg List.length hprk_eq.symm
    rw [bytesToBv8_length] at h
    exact h.trans (length_hmacWith C.F _ _)
  have hprk_len : (x.prk C.F).length = 32 := by
    rw [hprk_eq, bytesToBv8_length, hprk_ref_len]
  have hb_prk := IsBlock.pointsToBytes_len (a := ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [])
      ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 544#64) 976 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  rw [hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 0x20#64) (by omega)] at hpost_sep
  rw [hsp_m976]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- `subroutine_ok` for `pqxdhHkdfExtractNoneSpec` (`0x1ad38`, `salt = None`,
`160` / `192` / `224`-B `ikm`). -/
theorem pqxdhHkdfExtractNone_ok {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractNoneSpec P img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdhHkdfExtractNone_ok_trap hP himg)

/-- Discharges `PqxdhHkdfExtractOk_trap` on `trTrapProgAt img.base C absHooks`. -/
theorem pqxdhHkdfExtract_ok_trap {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqxdhHkdfExtractOk_trap P img C absHooks :=
  ⟨pqxdhHkdfExtractNone_ok_trap hP himg, pqxdhHkdfExtractSome_ok_trap hP himg⟩

/-! ## 3. Unconditional Responder Entry Points (`0x1ceb8`, `0x23920`, `0x21c80`) -/

/-- Discharges `PqxdhHkdfExtractOk` on `tripleRatchetProgAt img.base C ctl absHooks`. -/
theorem pqxdhHkdfExtract_ok {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img) :
    PqxdhHkdfExtractOk P img C ctl absHooks := ⟨subroutine_ok_kit_of_trTrap (pqxdhHkdfExtractNone_ok_trap hP himg), subroutine_ok_kit_of_trTrap (pqxdhHkdfExtractSome_ok_trap hP himg)⟩

/-- Unconditional `subroutine_ok` for `HandshakeKeys::derive` (`0x1ceb8`). -/
theorem handshakeKeysDerive_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpec P A img) :=
  handshakeKeysDerive_base_ok_trap himg hWF
    (pqxdhHkdfExtract_ok_trap hP himg)
    (pqxdhHkdfExpandMultiInfo_ok_trap hP)

/-- Unconditional `subroutine_ok` for `HandshakeKeys::derive` (`0x1ceb8`). -/
theorem handshakeKeysDerive_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpec P A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (handshakeKeysDerive_ok_trap himg hWF hP)

/-- Unconditional `subroutine_ok` for `Pqxdh::accept` (`0x23920`, field-expanded layout). -/
theorem pqxdhAccept_opt_fields_ok_trap {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpec P A img) :=
  pqxdhAccept_opt_fields_base_ok_trap himg hWF hH
    (pqxdhHkdfExtract_ok_trap hP himg)
    (pqxdhHkdfExpandMultiInfo_ok_trap hP)
    (pqxdhCalculateAgreement_ok_trap hP himg hH.alloc)

/-- Unconditional `subroutine_ok` for `Pqxdh::accept` (`0x23920`, field-expanded layout). -/
theorem pqxdhAccept_opt_fields_ok {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P) (hH : PqxdhHookContracts P A img absHooks)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpec P A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdhAccept_opt_fields_ok_trap himg hWF hH hP)

/-! ## 4. Contract-Backed `tripleRatchetProgAtExt` Entry Points -/

section Ext

/-- `Spec` for `expand_multi_info` (`b + 0x1a874`) at `okmLen = 96`, `info.length = 46`, with
`expandMultiInfoStackExt` (`17024` B) stack budget. -/
def expandMultiInfo96_46SpecExt (F : ShaState → List (BitVec 8) → ShaState) :
    Spec ExpandMultiInfoGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.hkdfA ∧
      s.readReg64 .x1 = x.infoHdrA ∧
      s.readReg64 .x2 = x.okmA ∧
      s.readReg64 .x3 = 96#64 ∧
      x.prk.length ≤ 64 ∧
      x.info.length = 46 ∧
      x.okmLen = 96⌝ ∗
    hmacCoreAt F x.hkdfA x.prk [] ∗
    (x.infoHdrA ↦₆₄ x.infoA) ∗
    ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
    (x.infoA ↦ᵣ x.info) ∗
    memRegion x.okmA 96 ∗
    stackAt s.sp expandMultiInfoStackExt
  post := fun x s₀ sf =>
    ⌜sf.trace = s₀.trace⌝ ∗
    hmacCoreAt F x.hkdfA x.prk [] ∗
    (x.infoHdrA ↦₆₄ x.infoA) ∗
    ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
    (x.infoA ↦ᵣ x.info) ∗
    (x.okmA ↦ₛ hkdfExpand F x.prk x.info 96) ∗
    stackAt s₀.sp expandMultiInfoStackExt

private theorem stackAt_pqxdhHkdfExt_expand96 (sp : BitVec 64) :
    stackAt sp pqxdhHkdfStackExt =
      memRegion (sp - 24576#64) 7552 ∗ stackAt sp expandMultiInfoStackExt := by
  change memRegion (sp - 24576#64) 24576 =
    memRegion (sp - 24576#64) 7552 ∗ memRegion (sp - 17024#64) 17024
  exact ProofLib.memRegion_split' (b := sp - 24576#64) (n := 7552) (k := 17024)
    (b' := sp - 17024#64) rfl (by bv_omega) (by decide)

/-- `pqxdhHkdfExpandCellsSpecExt P img 12` (`96` B, `info = INFO_PQXDH`) on
`tripleRatchetProgAtExt img.base ext` from `expandMultiInfo96_46SpecExt C.F`. -/
theorem pqxdhHkdfExpand_12_ok_ext {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (hexp96 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (expandMultiInfo96_46SpecExt C.F)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpecExt P img 12) := by
  refine subroutine_ok_map hexp96 ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsSpecExt, pqxdhHkdfExpandCellsSpecAt] at hpre
  rw [stackAt_pqxdhHkdfExt_expand96 sp, ← memRegion_cells okmA 12 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_PQXDH := by
    rcases hcases with ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hinfo, _⟩
    · omega
    · omega
    · exact hinfo
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 46 := by subst hinfo; rfl_kernel
  have hinfo_len_bv : BitVec.ofNat 64 info.length = 46#64 := by rw [hinfo_len]
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega), hinfo_len_bv] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 96⟩,
    memRegion (sp - 24576#64) 7552 ∗ R, ?_, ?_⟩
  · dsimp only [expandMultiInfo96_46SpecExt]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_len, trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [expandMultiInfo96_46SpecExt, pqxdhHkdfExpandCellsSpecExt,
      pqxdhHkdfExpandCellsSpecAt] at hpost ⊢
    rw [stackAt_pqxdhHkdfExt_expand96 sp, hinfo_len_bv]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 12 = 96 from rfl, bytesToBv8_hkdfExpandRef_96 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ 46#64) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 96) ∗
        stackAt s0.sp expandMultiInfoStackExt ∗
        memRegion (s0.sp - 24576#64) 7552) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

/-- Assembles `PqxdhHkdfExpandMultiInfoOk_ext` on `tripleRatchetProgAtExt img.base ext` from
`expandMultiInfoSpecExt C.F` (`64` / `80` B) and `expandMultiInfo96_46SpecExt C.F` (`96` B). -/
theorem pqxdhHkdfExpandMultiInfo_ok_ext {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (hexp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (expandMultiInfoSpecExt C.F))
    (hexp96 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (expandMultiInfo96_46SpecExt C.F)) :
    PqxdhHkdfExpandMultiInfoOk_ext P img ext := by
  intro k
  by_cases hk8 : k = 8
  · subst hk8; exact pqxdhHkdfExpand_8_ok_ext hP hexp
  · by_cases hk10 : k = 10
    · subst hk10; exact pqxdhHkdfExpand_10_ok_ext hP hexp
    · by_cases hk12 : k = 12
      · subst hk12; exact pqxdhHkdfExpand_12_ok_ext hP hexp96
      · exact pqxdhHkdfExpand_other_ok_ext P img ext k hk8 hk10 hk12

/-- Assembles `PqxdhHkdfExtractOk_ext` on `tripleRatchetProgAtExt img.base ext` from its `none`
(`160`/`192`/`224`-B IKM) and `some` (`32`-B salt, `32`-B IKM) branches. -/
theorem pqxdhHkdfExtract_ok_ext {P : Primitives} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hnone : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractNoneSpecExt P img))
    (hsome : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExtractSym)
      (pqxdhHkdfExtractSomeSpecExt P img)) :
    PqxdhHkdfExtractOk_ext P img ext :=
  ⟨hnone, hsome⟩

/-- Contract-backed `subroutine_ok` for `HandshakeKeys::derive` (`0x1ceb8`) on
`tripleRatchetProgAtExt img.base ext`. -/
theorem handshakeKeysDerive_ok_ext {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hext : PqxdhHkdfExtractOk_ext P img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext P img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr handshakeKeysDeriveSym)
      (handshakeKeysDeriveSpecExt P A img) :=
  handshakeKeysDerive_base_ok_ext himg hWF hext hexp

/-- Contract-backed `subroutine_ok` for `Pqxdh::accept` (`0x23920`, optional-fields layout) on
`tripleRatchetProgAtExt img.base ext`. -/
theorem pqxdhAccept_opt_fields_ok_ext {P : Primitives} {C : Crypto} {A : RustAlloc}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContractsExt P A img ext)
    (hP : PrimitivesMatchCrypto P C)
    (hbb : HookSat ext "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec)
    (hdh : HookSat ext dhName (SignalSession.CliExt.dhSpec C))
    (hsh : HookSat ext sharedDropName SignalSession.CliExt.zeroizeSpec)
    (hst : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec)
    (hext : PqxdhHkdfExtractOk_ext P img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext P img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt P A img) :=
  pqxdhAccept_opt_fields_base_ok_ext himg hWF hH hext hexp
    (pqxdhCalculateAgreement_ok_ext hP himg hH.alloc hbb hdh hsh hH.shim hst)

/-- Contract-backed `subroutine_ok` for `Pqxdh::accept` (`0x23920`, fields layout) on
`tripleRatchetProgAtExt img.base ext`. -/
theorem pqxdhAccept_ok_ext {P : Primitives} {C : Crypto} {A : RustAlloc}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContractsExt P A img ext)
    (hP : PrimitivesMatchCrypto P C)
    (hbb : HookSat ext "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec)
    (hdh : HookSat ext dhName (SignalSession.CliExt.dhSpec C))
    (hsh : HookSat ext sharedDropName SignalSession.CliExt.zeroizeSpec)
    (hst : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec)
    (hext : PqxdhHkdfExtractOk_ext P img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext P img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptFieldsSpecExt P A img) :=
  pqxdhAccept_fields_base_ok_ext himg hWF hH hext hexp
    (pqxdhCalculateAgreement_ok_ext hP himg hH.alloc hbb hdh hsh hH.shim hst)

theorem accept_ok_ext {P : Primitives} {C : Crypto} {A : RustAlloc}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : PqxdhHookContractsExt P A img ext)
    (hP : PrimitivesMatchCrypto P C)
    (hbb : HookSat ext "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec)
    (hdh : HookSat ext dhName (SignalSession.CliExt.dhSpec C))
    (hsh : HookSat ext sharedDropName SignalSession.CliExt.zeroizeSpec)
    (hst : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec)
    (hext : PqxdhHkdfExtractOk_ext P img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext P img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt P A img) :=
  pqxdhAccept_opt_fields_ok_ext himg hWF hH hP hbb hdh hsh hst hext hexp

/-- Direct `CliExternsOk P0 A ext` specialization of `pqxdhAccept_opt_fields_ok_ext` on raw `ext`. -/
theorem pqxdhAccept_opt_fields_ok_of_externsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext)
    (hext : PqxdhHkdfExtractOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_opt_fields_base_ok_ext himg hWF
    (PqxdhHookContractsExt.of_externsOk X hOk) hext hexp
    (pqxdhCalculateAgreement_ok_of_externsOk X himg hOk)

/-- Direct `CliExternsOk P0 A ext` specialization of `pqxdhAccept_opt_fields_ok_ext` on
`SignalSession.cliExternsWith ext`. -/
theorem pqxdhAccept_opt_fields_ok_of_cliExternsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext)
    (hext : PqxdhHkdfExtractOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img
      (SignalSession.cliExternsWith ext))
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img
      (SignalSession.cliExternsWith ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_opt_fields_base_ok_ext himg hWF
    (PqxdhHookContractsExt.of_cliExternsOk X hOk) hext hexp
    (pqxdhCalculateAgreement_ok_of_cliExternsOk X himg hOk)

theorem accept_ok_of_externsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext)
    (hext : PqxdhHkdfExtractOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_opt_fields_ok_of_externsOk X himg hWF hOk hext hexp

theorem accept_ok_of_cliExternsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext)
    (hext : PqxdhHkdfExtractOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img
      (SignalSession.cliExternsWith ext))
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img
      (SignalSession.cliExternsWith ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptOptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_opt_fields_ok_of_cliExternsOk X himg hWF hOk hext hexp

/-- Direct `CliExternsOk P0 A ext` specialization of `pqxdhAccept_ok_ext` on raw `ext`. -/
theorem pqxdhAccept_ok_of_externsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext)
    (hext : PqxdhHkdfExtractOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img ext)
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_fields_base_ok_ext himg hWF
    (PqxdhHookContractsExt.of_externsOk X hOk) hext hexp
    (pqxdhCalculateAgreement_ok_of_externsOk X himg hOk)

/-- Direct `CliExternsOk P0 A ext` specialization of `pqxdhAccept_ok_ext` on
`SignalSession.cliExternsWith ext`. -/
theorem pqxdhAccept_ok_of_cliExternsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)))
    (hOk : SignalSession.CliExternsOk P0 A ext)
    (hext : PqxdhHkdfExtractOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img
      (SignalSession.cliExternsWith ext))
    (hexp : PqxdhHkdfExpandMultiInfoOk_ext
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) img
      (SignalSession.cliExternsWith ext)) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr pqxdhAcceptSym)
      (pqxdhAcceptFieldsSpecExt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img) :=
  pqxdhAccept_fields_base_ok_ext himg hWF
    (PqxdhHookContractsExt.of_cliExternsOk X hOk) hext hexp
    (pqxdhCalculateAgreement_ok_of_cliExternsOk X himg hOk)

end Ext

end CryptoVerification.E2E.Pqxdh.ResponderCore
