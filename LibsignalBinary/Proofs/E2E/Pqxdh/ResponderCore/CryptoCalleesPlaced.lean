/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlaced
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.SepLogic.WPFrozen

/-!
# Relocatable Unconditional Crypto Callees and Hook Bundle (`[LibsignalPlacement]`)

Proves relocatable `[LibsignalPlacement]` contracts for `expand_multi_info` (`96` B on Block `53`),
`GenericHkdf::extract` (Block `54`), and unconditional `<HandshakeKeys>::derive` (Block `59`), and
packages the responder external-hook hypotheses into `PqxdhPlacedHookContracts`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalHmac
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Expand
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator

private theorem ro_outside_rw_placed {P Q R : SepProp} {b_ro b_rw : BitVec 64} {n_ro n_rw : ℕ}
    {Φ_ro Φ_rw : Memory → Prop} {m : Memory}
    (hro : IsBlockRO P b_ro n_ro Φ_ro)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ P ∗ (Q ∗ R)) :
    ∀ a, InRegion b_ro n_ro a → OutsideRegion b_rw n_rw a := by
  intro a ha_ro
  rw [outsideRegion_iff_not_inRegion]
  intro ha_rw
  rw [← sepConj_assoc] at hsep
  obtain ⟨h₁, h₂, hd1, hP, hQ, -⟩ :=
    Satisfies.sepConj_elim (ProofLib.Satisfies.of_sep_left hsep)
  obtain ⟨m₀, -, rfl⟩ := (hro.iff _).mp hP
  obtain ⟨m₁, -, rfl⟩ := (hrw.iff _).mp hQ
  have h_in1 : (regionHeapRO b_ro n_ro m₀).phys a = some (.ro (m₀.read8 a)) := by
    simp [regionHeapRO, ha_ro]
  have h_in2 : (regionHeap b_rw n_rw m₁).phys a = some (.rw (m₁.read8 a)) := by
    simp [regionHeap, ha_rw]
  unfold Heap.Disjoint at hd1
  rcases hd1.1 a with h | h | ⟨_, _, h⟩
  · rw [h_in1] at h; contradiction
  · rw [h_in2] at h; contradiction
  · rw [h_in2] at h; cases h

private theorem satisfies_withLsCodeLoaded_intro' {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  have hcomm : (spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by ac_rfl
  rw [hcomm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

/-- Transfer `subroutine_ok calleeProg entry spec` from an unmutated block `j` to any block `i`'s
program `callerProg` whenever `spec.pre x s0 ∗ R` implies `LibsignalCodeLoaded lsmpl s0.mem`. -/
private theorem subroutine_ok_of_block_of_cl [LibsignalPlacement]
    {α : Type} {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hcl_pre : ∀ (x : α) (R : SepProp) (s0 : State),
      (s0.mem ⊨ spec.pre x s0 ∗ R) → LibsignalCodeLoaded lsmpl s0.mem)
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry spec := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hcl_pre x R s0 hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-! ## 1. `expand_multi_info` (Block `53`) for `k = 12` (`96` B) & `PqxdhHkdfExpandMultiInfoPlacedOk` -/

/-- Relocatable `subroutine_ok` for `expand_multi_info` (Block `53`) at `okmLen = 96`,
`info.length = 46`. -/
theorem expand_multi_info_96_46_placed_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (blkPl_53).base
      (withLsCodeLoaded lsmpl (expandMultiInfo96_46Spec C.F)) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre_cl
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
  have h_exp_pre : ExpandPre96_46 expPlacedFakeB C.F x.prk x.info x.infoA s0 :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; exact hpc
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
      out_info_stk := by rw [← hinfo_len]; exact ro_outside_rw_placed hro_info hb_stk hsep_info_stk
      out_info_x2 := by
        rw [hx2, ← hinfo_len]; exact ro_outside_rw_placed hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine (expand_multi_info_96_46_placed_runsTo (C := C) (H := H) hcl h_exp_pre).to_reaches_pc
    fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [withLsCodeLoaded, expandMultiInfo96_46Spec, stackAt, expandMultiInfoStack,
    finalizeFixedStack]
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

/-- `pqxdhHkdfExpandCellsPlacedSpec P lsmpl 12` (`96` B, `info = INFO_PQXDH`) on Block `53`
from `expand_multi_info_96_46_placed_ok`. -/
theorem pqxdhHkdfExpand_12_placed_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 12) := by
  have hexp := expand_multi_info_96_46_placed_ok C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [Keys.stackAt_alloc_expand sp, ← memRegion_cells okmA 12 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
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
  · apply satisfies_withLsCodeLoaded_intro' hF.code
    dsimp only [expandMultiInfo96_46Spec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_len, trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, expandMultiInfo96_46Spec,
      pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
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

/-- Discharges `PqxdhHkdfExpandMultiInfoPlacedOk` on Block `53` for all `k`. -/
theorem pqxdhHkdfExpandMultiInfo_placed_ok_block53 [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    PqxdhHkdfExpandMultiInfoPlacedOk P ((blkPC_53).rebase (blkPl_53).base H) := by
  intro k
  by_cases hk8 : k = 8
  · subst hk8; exact pqxdhHkdfExpand_8_placed_ok hP
  · by_cases hk10 : k = 10
    · subst hk10; exact pqxdhHkdfExpand_10_placed_ok hP
    · by_cases hk12 : k = 12
      · subst hk12; exact pqxdhHkdfExpand_12_placed_ok hP
      · exact pqxdhHkdfExpand_other_placed_ok P _ k hk8 hk10 hk12

/-- Cross-block `PqxdhHkdfExpandMultiInfoPlacedOk P callerProg` on any caller block `i < 619`
(including mutated caller blocks such as Block `79`). -/
theorem pqxdhHkdfExpandMultiInfo_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  intro k
  refine subroutine_ok_of_block_of_cl (pqxdhHkdfExpandMultiInfo_placed_ok_block53 hP k)
    (fun ⟨_, _, _, _, _, _, _⟩ R s0 hpre => ?_) hi (by decide) (by decide)
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1.1.code

/-! ## 2. `GenericHkdf::extract` (Block `54`) & `PqxdhHkdfExtractPlacedOk` -/

/-- Cross-block `Hmac::new_from_slice` (Block `114` -> Block `54`) packaged with
`LibsignalCodeRoLoaded lsmpl` for `Extract.extract_placed_ok_of_inv` and
`extract_none_long_placed_runsToE_of_inv`. -/
private theorem new_from_slice_block54_cro_ok [LibsignalPlacement]
    (C : Crypto) (H : LibsignalHooks) [hH : HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with
        pre := fun x s0 =>
          (newFromSliceSpec C.F).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ } := by
  have h114 := ConsumeMessageKeyTransfer.new_from_slice_placed_ok_withLsCodeLoaded_ro C.F
    hH.memcpy hH.compress256
  have h54 : subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      (withLsCodeLoaded lsmpl
        { newFromSliceSpec C.F with
          pre := fun x s0 =>
            (newFromSliceSpec C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }) :=
    ls_subroutine_ok_of_block h114
  refine subroutine_ok_mono h54 ?_ (fun _ _ _ _ hq => hq)
  intro x R s0 hp
  dsimp only [withLsCodeLoaded] at hp ⊢
  have hcomm1 : ((newFromSliceSpec C.F).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ ((newFromSliceSpec C.F).pre x s0 ∗ R) := by ac_rfl
  have hcomm2 :
      (((newFromSliceSpec C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗
        ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
        (⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((newFromSliceSpec C.F).pre x s0 ∗ R)) := by ac_rfl
  rw [hcomm1, satisfies_pure_sepConj] at hp
  rw [hcomm2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

/-- `subroutine_ok` for `pqxdhHkdfExtractSomePlacedSpec` on Block `54` (`salt = Some`, `32`-B `ikm`),
derived from `Extract.extract_placed_ok_of_inv`. -/
theorem pqxdhHkdfExtractSome_placed_ok_block54 [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 54)
      (pqxdhHkdfExtractSomePlacedSpec P lsmpl) := by
  have hext := extract_placed_ok_of_inv C H
    (Inv := LibsignalCodeRoLoaded lsmpl)
    LibsignalCodeRoLoaded.of_keepsFrozen (fun h => h.1)
    (new_from_slice_block54_cro_ok C H)
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, saltA, salt, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExtractSomePlacedSpec] at hpre
  rw [Keys.stackAt_alloc_extract sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp_eq, hsalt_ne, hsalt_len, hikm_len⟩, hpre⟩
  let x : ExtractGhost := ⟨ret, saltA, some (u8Vec 32 salt), ikmA, bytesToBv8 ikm⟩
  have hsalt_list : (u8Vec 32 salt).toList = bytesToBv8 salt := u8Vec_toList_of_length hsalt_len
  have hikm_bv_len : x.ikm.length = 32 := by dsimp [x]; rw [bytesToBv8_length, hikm_len]
  refine ⟨x,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3120 ∗ R, ?_, ?_⟩
  · have hcomm :
        ((extractSpec C.F).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗
          (memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
            memRegion (sp - 4096#64) 3120 ∗ R) =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          ((extractSpec C.F).pre x s0 ∗
            (memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
              memRegion (sp - 4096#64) 3120 ∗ R)) := by ac_rfl
    rw [hcomm, satisfies_pure_sepConj]
    refine ⟨⟨hF.code, hF.ro⟩, ?_⟩
    dsimp only [extractSpec, optSaltAt, x]
    subst hsp_eq
    rw [hsalt_list]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, fun _ => hx2, (fun h => nomatch h), hx3, hx4, hikm_bv_len⟩, ?_⟩
    have hcomm_salt :
        memRegion ret 176 ∗ ⌜saltA ≠ 0#64⌝ ∗ (saltA ↦ₛ bytesToBv8 salt) ∗
          (ikmA ↦ₛ bytesToBv8 ikm) ∗ stackAt s0.sp extractStack ∗
          memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
          memRegion (s0.sp - 4096#64) 3120 ∗ R =
        ⌜saltA ≠ 0#64⌝ ∗
          (memRegion ret 176 ∗ (saltA ↦ₛ bytesToBv8 salt) ∗
            (ikmA ↦ₛ bytesToBv8 ikm) ∗ stackAt s0.sp extractStack ∗
            memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
            memRegion (s0.sp - 4096#64) 3120 ∗ R) := by ac_rfl
    rw [hcomm_salt, satisfies_pure_sepConj]
    exact ⟨hsalt_ne, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [extractSpec, optSaltAt, pqxdhHkdfExtractSomePlacedSpec] at hpost ⊢
    rw [Keys.stackAt_alloc_extract sp]
    subst hsp_eq
    have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P (some salt) ikm) := by
      dsimp [x, ExtractGhost.prk]
      exact (bytesToBv8_hkdfExtractRef_some hP hsalt_len ikm).symm
    change sf.mem ⊨
      (⌜sf.trace = s0.trace⌝ ∗
        (ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [] ∗
        (⌜saltA ≠ 0#64⌝ ∗ (saltA ↦ₛ (u8Vec 32 salt).toList)) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
        stackAt s0.sp extractStack) ∗
      (memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3120 ∗ R) at hpost
    have hprk_ref_len : (hkdfExtractRef P (some salt) ikm).length = 32 :=
      hkdfExtractRef_length P (some salt) ikm
    rw [hsalt_list, hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 0x20#64) (by omega)] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    have hcomm_post :
        (ret ↦ₛ bytesToBv8 (hkdfExtractRef P (some salt) ikm)) ∗
          pqxdhHmacStateAt P (ret + 0x20#64) (hkdfExtractRef P (some salt) ikm) ∗
          ⌜saltA ≠ 0#64⌝ ∗ (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
          stackAt s0.sp extractStack ∗ memRegion (s0.sp - 8192#64) 3936 ∗
          memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗ R =
        ⌜saltA ≠ 0#64⌝ ∗
          ((ret ↦ₛ bytesToBv8 (hkdfExtractRef P (some salt) ikm)) ∗
            pqxdhHmacStateAt P (ret + 0x20#64) (hkdfExtractRef P (some salt) ikm) ∗
            (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
            stackAt s0.sp extractStack ∗ memRegion (s0.sp - 8192#64) 3936 ∗
            memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗ R) := by ac_rfl
    rw [hcomm_post, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨_, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

/-- `subroutine_ok` for `pqxdhHkdfExtractNonePlacedSpec` on Block `54` (`salt = None`,
`160` / `192` / `224`-B `ikm`), derived from `extract_none_long_placed_runsToE_of_inv`. -/
theorem pqxdhHkdfExtractNone_placed_ok_block54 [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 54)
      (pqxdhHkdfExtractNonePlacedSpec P lsmpl) := by
  refine subroutine_ok_intro fun ⟨ret, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhHkdfExtractNonePlacedSpec] at hpre
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
  have hx4' : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length := by
    rw [hikm_bv_len]; exact hx4
  let R_rest : SepProp :=
    (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
    memRegion (s0.sp - 4096#64) 3120 ∗ R
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
          memRegion (s0.sp - 4096#64) 3120 ∗ memRegion (sp0 - 544#64) 976 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗
        (memRegion ret 0xb0 ∗ memRegion (s0.sp - 8192#64) 3936 ∗
          memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗ R)) := by
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
  have hruns := extract_none_long_placed_runsToE_of_inv (C := C) (H := H)
    (Inv := LibsignalCodeRoLoaded lsmpl)
    LibsignalCodeRoLoaded.of_keepsFrozen (fun h => h.1)
    (new_from_slice_block54_cro_ok C H)
    (x := x) ⟨hF0.code, hF0.ro⟩ hpc hrun hsp0 hx1 hx3 hx4' rfl rfl hikm_cases hsp_al
    hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk
  refine hruns.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [pqxdhHkdfExtractNonePlacedSpec]
  rw [Keys.stackAt_alloc_extract s0.sp]
  dsimp only [stackAt, extractStack, newFromSliceStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P none ikm) := by
    dsimp [x, ExtractGhost.prk]
    exact (bytesToBv8_hkdfExtractRef_none hP ikm).symm
  have hprk_ref_len : (hkdfExtractRef P none ikm).length = 32 :=
    hkdfExtractRef_length P none ikm
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

/-- Discharges `PqxdhHkdfExtractPlacedOk` on Block `54`. -/
theorem pqxdhHkdfExtract_placed_ok_block54 [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    PqxdhHkdfExtractPlacedOk P ((blkPC_54).rebase (blkPl_54).base H) :=
  ⟨pqxdhHkdfExtractNone_placed_ok_block54 hP, pqxdhHkdfExtractSome_placed_ok_block54 hP⟩

/-- Cross-block `PqxdhHkdfExtractPlacedOk P callerProg` on any caller block `i < 619`
(including Block `59` and mutated caller blocks such as Block `79`). -/
theorem pqxdhHkdfExtract_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  refine ⟨?_, ?_⟩
  · refine subroutine_ok_of_block_of_cl (pqxdhHkdfExtractNone_placed_ok_block54 hP)
      (fun ⟨_, _, _, _⟩ R s0 hpre => ?_) hi (by decide) (by decide)
    dsimp only [pqxdhHkdfExtractNonePlacedSpec] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.1.code
  · refine subroutine_ok_of_block_of_cl (pqxdhHkdfExtractSome_placed_ok_block54 hP)
      (fun ⟨_, _, _, _, _, _⟩ R s0 hpre => ?_) hi (by decide) (by decide)
    dsimp only [pqxdhHkdfExtractSomePlacedSpec] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.1.code

/-! ## 3. Unconditional `<HandshakeKeys>::derive` (Block `59`) -/

/-- Unconditional relocatable `subroutine_ok` for `<HandshakeKeys>::derive` (Block `59`),
instantiating `Initiator.handshakeKeysDerive_placed_ok` with `pqxdhHkdfExtract_placed_ok` and
`pqxdhHkdfExpandMultiInfo_placed_ok`. -/
theorem handshakeKeysDerive_placed_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_59).rebase (blkPl_59).base H) (blkPl_59).base
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec P A)) :=
  Initiator.handshakeKeysDerive_placed_ok hWF
    (pqxdhHkdfExtract_placed_ok hP)
    (pqxdhHkdfExpandMultiInfo_placed_ok hP)

/-- Cross-block transfer of unconditional `handshakeKeysDerive_placed_ok` to any caller block
`i < 619` (such as Block `70` `initialize_bob_session`). -/
theorem handshakeKeysDerive_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec P A)) :=
  keys_ls_subroutine_ok_of_block_cro (handshakeKeysDerive_placed_ok hWF hP) hi (by decide) (by decide)

/-! ## 4. Placed External Hook Symbols & Contracts for `ResponderCore` (`AcceptPlaced` / `InitBobPlaced`) -/

abbrev lsKyberDecapsSym : String :=
  "_RNvNtNtCs1mK0QScfTrZ_14libcrux_ml_kem9mlkem10245kyber11decapsulate"

abbrev lsDalekMontToEdSym : String :=
  "_RNvMs5_NtCs2wR8L9wiBdT_16curve25519_dalek10montgomeryNtB5_15MontgomeryPoint10to_edwards"

abbrev lsDalekTorsionFreeSym : String :=
  "_RNvMsx_NtCs2wR8L9wiBdT_16curve25519_dalek7edwardsNtB5_12EdwardsPoint15is_torsion_free"

abbrev lsHandleErrorSym : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

/-- Look up the external hook at `lsρ sym` on ANY block `i`'s program `prog` (including mutated
blocks such as Block `79`), by transferring from Block `53` via `externs_eq`. -/
theorem pqxdh_placed_externAt?_of_mem [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} (hmem : sym ∈ libsignalSessionExterns := by decide) :
    prog.externAt? (lsρ sym) = H sym := by
  let p53 := (blkPC_53).rebase (blkPl_53).base H
  have h53_inst : IsLsBlockProg p53 53 H := inferInstance
  have h53 : p53.externAt? (lsρ sym) = H sym :=
    keys_ls_externAt?_of_mem (prog := p53) (i := 53) hmem (by decide) (by decide)
  have heq : prog.externAt? (lsρ sym) = p53.externAt? (lsρ sym) := by
    rw [hprog.eq_blockProgram, h53_inst.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hprog.externs_eq.trans h53_inst.externs_eq.symm)]
  exact heq.trans h53

/-- `subroutine_ok prog (lsρ sym) spec` on ANY block `i`'s program `prog` (including mutated
blocks such as Block `79`) from `HookSat H sym spec`. -/
theorem pqxdh_placed_hook_ok_of_mem [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H]
    {sym : String} {spec : Spec α} (hsat : HookSat H sym spec)
    (hmem : sym ∈ libsignalSessionExterns := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨f, hf, hok⟩ := hsat
  exact subroutine_ok_of_hookOk ((pqxdh_placed_externAt?_of_mem hmem).trans hf) hok

/-- Combined external-hook contract bundle for `ResponderCore` (`AcceptPlaced` / `InitBobPlaced`)
under `[LibsignalPlacement]`. -/
structure PqxdhPlacedHookContracts (P : Primitives) (C : Crypto) (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooks C.F H
  dh               : HookSat H Keys.lsDhSym (diffieHellmanSpec C.X)
  sharedDrop       : HookSat H Keys.lsSharedDropSym zeroizeSecretSpec
  staticDrop       : HookSat H Keys.lsStaticDropSym zeroizeSecretSpec
  blackBox         : H lsBlackBoxU8Sym = some blackBoxHook
  noAllocShim      : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec
  alloc            : HookSat H Keys.lsRustAllocSym (rustAllocSpec A)
  dealloc          : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  handleAllocError : H Keys.lsHandleAllocErrorSym = some Rust.panicked
  handleError      : H lsHandleErrorSym = some Rust.panicked
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)

theorem kyberDecaps_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsKyberDecapsSym (kyberDecapsStubSpec P)) :
    subroutine_ok prog (lsρ lsKyberDecapsSym) (kyberDecapsStubSpec P) :=
  pqxdh_placed_hook_ok_of_mem h

theorem dalekMontToEd_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsDalekMontToEdSym (dalekMontToEdStubSpec P)) :
    subroutine_ok prog (lsρ lsDalekMontToEdSym) (dalekMontToEdStubSpec P) :=
  pqxdh_placed_hook_ok_of_mem h

theorem dalekTorsionFree_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)) :
    subroutine_ok prog (lsρ lsDalekTorsionFreeSym) (cryptoBoolRegStubSpec P.isTorsionFree 160) :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_shim_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H Keys.lsRustNoAllocShimSym noAllocShimSpec) :
    subroutine_ok prog (lsρ Keys.lsRustNoAllocShimSym) noAllocShimSpec :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_alloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H Keys.lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok prog (lsρ Keys.lsRustAllocSym) (rustAllocSpec A) :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_dealloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustDeallocSpec A) :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_memcpy_region_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : H lsMemcpySym = some ProofLib.hookMemcpy) :
    subroutine_ok prog (lsρ lsMemcpySym) pqxdhMemcpyRegionSpec :=
  pqxdh_placed_hook_ok_of_mem ⟨ProofLib.hookMemcpy, h, Initiator.hookMemcpy_region_trace_ok⟩

theorem pqxdh_panic_at_raw_vec_handle_error_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : H lsHandleErrorSym = some Rust.panicked) :
    prog.externAt? (lsρ lsHandleErrorSym) = some Rust.panicked :=
  (pqxdh_placed_externAt?_of_mem (sym := lsHandleErrorSym)).trans h

theorem pqxdh_panic_at_handle_alloc_error_placed [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : H Keys.lsHandleAllocErrorSym = some Rust.panicked) :
    prog.externAt? (lsρ Keys.lsHandleAllocErrorSym) = some Rust.panicked :=
  (pqxdh_placed_externAt?_of_mem (sym := Keys.lsHandleAllocErrorSym)).trans h

theorem PqxdhPlacedHookContracts.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk P A callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContracts.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk P A callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContracts.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok hP hi

theorem PqxdhPlacedHookContracts.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok hP hi

end CryptoVerification.E2E.Pqxdh.ResponderCore
