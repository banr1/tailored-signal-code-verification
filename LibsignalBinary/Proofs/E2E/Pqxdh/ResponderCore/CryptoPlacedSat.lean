/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSat -- proof-setup: allow-public-import
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `[HkdfPlacedHooksSat]` Placed Crypto Callees and Contract Bundle

Replaces `[HkdfPlacedHooks C.F H]` with `[HkdfPlacedHooksExactSat C.F H]` across all PQXDH
relocatable crypto callees (`pqxdhHkdfExpand_*_placed_ok_sat`, `expand_multi_info_96_46_placed_ok_sat`,
`pqxdhHkdfExtract*_placed_ok*_sat`, `handshakeKeysDerive_placed_ok*_sat`) and provides
`PqxdhPlacedHookContracts{,Exact}Sat` bundles, coercions, and projections.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open scoped CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Expand CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (blkPC_59 blkPl_59 libsignalSessionLib lsBlackBoxU8Sym lsRustDeallocSym)
open CryptoVerification.E2E.Pqxdh.Initiator (INFO_MSG_KEYS INFO_PQXDH INFO_RATCHET PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk Primitives StructuralPrims bytesToBv8 cryptoBoolRegStubSpec handshakeKeysDerivePlacedBaseSpec handshakeKeysDerive_placed_ok hkdfExtractRef hkdfExtractRef_length kyberDecapsStubSpec pqxdhHkdfExpandCellsPlacedSpec pqxdhHkdfExtractNonePlacedSpec pqxdhHkdfExtractSomePlacedSpec pqxdhHmacStateAt)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ExpandPre96_46 PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk PqxdhPlacedHookContracts PrimitivesMatchCrypto bytesToBv8_hkdfExpandRef_64 bytesToBv8_hkdfExpandRef_80 bytesToBv8_hkdfExpandRef_96 bytesToBv8_hkdfExtractRef_none bytesToBv8_hkdfExtractRef_some bytesToBv8_length expandMultiInfo96_46Spec hkdfExpand_96_eq lsDalekMontToEdSym lsDalekTorsionFreeSym lsKyberDecapsSym pqxdhCalculateAgreement_placed_frozen_ok_of_block pqxdhCalculateAgreement_placed_ok_of_block pqxdhHkdfExpand_other_placed_ok pqxdhHmacStateAt_eq u8Vec_toList_of_length)
open CryptoVerification.LibsignalTripleRatchet (CallingConventionPreserved_of_calleeSaved ExtractGhost HmacSt LibsignalCodeRoLoaded RW blkPC_53 blkPC_54 blkPl_53 blkPl_54 diffieHellmanSpec expPlacedFakeB expandMultiInfoSpec expandMultiInfoStack extractSpec extractStack finalizeFixedStack hmacCoreAt isBlock_hmacCoreAt keys_ls_subroutine_ok_of_block_cro newFromSliceSpec newFromSliceStack noAllocShimSpec optSaltAt ro_outside_rw_shared_lb withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Expand (t1_length t2_length t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract (ExtFrame sp0_aligned)
open CryptoVerification.RustHeap (RustAlloc rustAllocSpec rustDeallocSpec)
open LibsignalBinary.Proofs.Placed.Bridge (LibsignalHooks LibsignalPlacement LibsignalRoLoaded libsignalMutatedBlocks lsmpl)
open LibsignalBinary.Proofs.Placed.PlacedCallSym (IsLsBlockProg LibsignalCodeLoaded extract_withLsCodeLoaded ls_externAt?_blockProgram_eq_of_externs_eq ls_subroutine_ok_of_block withLsCodeLoaded)

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.E2E (u8Vec)
open CryptoVerification.LibsignalSession (blackBoxHook)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedSat
  (extract_none_long_placed_runsToE_of_inv_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedSat
  (ExpandPre96_46Base expand_multi_info_96_46_placed_runsToE_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooks.toExactSat HkdfPlacedHooks.toSat HkdfPlacedHooksExactSat HkdfPlacedHooksSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSat
  (ExpandFrameS2 expand_multi_info_placed_ok_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSat
  (extract_placed_ok_of_inv_sat)

private theorem satisfies_withLsCodeLoaded_intro' {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  have hcomm : (spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by sep_ac_rfl
  rw [hcomm, satisfies_pure_sepConj]
  exact ⟨hcl, hpre⟩

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

/-! ## 1. `expand_multi_info` (Block `53`) for `k ∈ {8, 10, 12}` & `PqxdhHkdfExpandMultiInfoPlacedOk` -/

private theorem byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hi' : i < xs.length := hi
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi']
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem toUTF8_toList_eq (s : String) :
    s.toUTF8.toList = s.toList.flatMap String.utf8EncodeChar := by
  rw [byteArray_toList_eq_data]
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [List.utf8Encode]

private theorem INFO_RATCHET_length : INFO_RATCHET.length = 14 := by
  unfold INFO_RATCHET; rw [toUTF8_toList_eq]; decide

private theorem INFO_MSG_KEYS_length : INFO_MSG_KEYS.length = 18 := by
  unfold INFO_MSG_KEYS; rw [toUTF8_toList_eq]; decide

private theorem INFO_PQXDH_length : INFO_PQXDH.length = 46 := by
  unfold INFO_PQXDH; rw [toUTF8_toList_eq]; decide

theorem pqxdhHkdfExpand_8_placed_ok_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 8) := by
  have hexp := expand_multi_info_placed_ok_sat C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_expand sp, ← ProofLib.memRegion_cells okmA 8 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_RATCHET := by
    rcases hcases with ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
    · exact hinfo
    · omega
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 14 := hinfo ▸ INFO_RATCHET_length
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 64⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · apply satisfies_withLsCodeLoaded_intro' hF.code
    dsimp only [expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inl trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, expandMultiInfoSpec, pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 8 = 64 from rfl, bytesToBv8_hkdfExpandRef_64 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 64) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (CryptoVerification.LibsignalTripleRatchet.Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

theorem pqxdhHkdfExpand_10_placed_ok_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 10) := by
  have hexp := expand_multi_info_placed_ok_sat C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_expand sp, ← ProofLib.memRegion_cells okmA 10 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_MSG_KEYS := by
    rcases hcases with ⟨_, _, hk⟩ | ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩
    · omega
    · exact hinfo
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 18 := hinfo ▸ INFO_MSG_KEYS_length
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 80⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · apply satisfies_withLsCodeLoaded_intro' hF.code
    dsimp only [expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inr trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, expandMultiInfoSpec, pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 10 = 80 from rfl, bytesToBv8_hkdfExpandRef_80 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 80) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (CryptoVerification.LibsignalTripleRatchet.Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

theorem expand_multi_info_96_46_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactSat C.F H] :
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
    { pc_eq := by rw [CryptoVerification.LibsignalTripleRatchet.expPlacedFakeB_off_0]; exact hpc
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
      out_info_stk := by
        rw [← hinfo_len]; exact ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by
        rw [hx2, ← hinfo_len]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  have hb_base : ExpandPre96_46Base C.F x.prk x.info x.infoA s0 :=
    { pre := h_exp_pre
      read_info := by
        rw [← hinfo_len]
        exact fun a ha => ⟨hro_info.perm_r hsep_info_stk ha, hro_info.isLazyFree_false hsep_info_stk ha⟩ }
  refine (expand_multi_info_96_46_placed_runsToE_sat (C := C) (H := H) hcl hb_base).to_reaches_pc
    fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [withLsCodeLoaded, expandMultiInfo96_46Spec, stackAt, expandMultiInfoStack,
    finalizeFixedStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrameS2 at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info 96).length = 96 := by
    rw [hkdfExpand_96_eq]
    simp [t1_length, t2_length, t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info 96) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    CryptoVerification.LibsignalTripleRatchet.Extract.S2Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; decide, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info 96) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

theorem pqxdhHkdfExpand_12_placed_ok_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 12) := by
  have hexp := expand_multi_info_96_46_placed_ok_sat C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_expand sp, ← ProofLib.memRegion_cells okmA 12 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_PQXDH := by
    rcases hcases with ⟨_, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hinfo, _⟩
    · omega
    · omega
    · exact hinfo
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 46 := hinfo ▸ INFO_PQXDH_length
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
    rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_expand sp, hinfo_len_bv]
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
      (CryptoVerification.LibsignalTripleRatchet.Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

theorem pqxdhHkdfExpandMultiInfo_placed_ok_block53_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    PqxdhHkdfExpandMultiInfoPlacedOk P ((blkPC_53).rebase (blkPl_53).base H) := by
  intro k
  by_cases hk8 : k = 8
  · subst hk8; exact pqxdhHkdfExpand_8_placed_ok_sat hP
  · by_cases hk10 : k = 10
    · subst hk10; exact pqxdhHkdfExpand_10_placed_ok_sat hP
    · by_cases hk12 : k = 12
      · subst hk12; exact pqxdhHkdfExpand_12_placed_ok_sat hP
      · exact pqxdhHkdfExpand_other_placed_ok P _ k hk8 hk10 hk12

theorem pqxdhHkdfExpandMultiInfo_placed_ok_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  intro k
  refine subroutine_ok_of_block_of_cl (pqxdhHkdfExpandMultiInfo_placed_ok_block53_sat hP k)
    (fun ⟨_, _, _, _, _, _, _⟩ R s0 hpre => ?_) hi (by decide) (by decide)
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1.1.code

/-! ## 2. `GenericHkdf::extract` (Block `54`) & `PqxdhHkdfExtractPlacedOk` -/

section ExactNewFromSliceLocal

open scoped CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoGames.HMAC (sha256IV)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (blkPC_114 blkPl_114 lsProg_114 subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (AgreesOutside.write64_self Frame Frame.of_agreesOutside_stack
   Frame.refl Frame.update_two_blocks Layout.readBytes_writeBytes_eq NfsMemInv NfsRegInv RunsTo
   RunsTo.lsProg_svc RunsTo.pairStep_114_0x28 TraceEq agreesOutside_nfsPrologueMem
   agreesOutside_toFrame disjointRegions_of_ro_rw keyBlock keyBlock_length lsCompress256Sym
   lsMemcpySym lsSha256IVAddr nfsPlacedFakeB nfsPlacedFakeB_add_iv nfsPrologueMem
   nfsSavedStack_prologue_432 nfsSp nfs_chunk1_placed nfs_chunk2_placed nfs_chunk3_placed
   nfs_chunk4_placed nfs_second_half_placed nfs_sp_add_464_align nfs_sp_add_544_align nfs_sp_align
   nfs_sp_eq_add nfs_ule_65_false readBytes_writeBytes_16_other readBytes_writeBytes_16_self slice16
   slice16_length write64_oct_zero_eq_writeBytes_64 write64_quad_288_eq_writeBytes_slice16
   writeBytes_key_over_zero64)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
  (isBlock_nfsResult rodata_placed_sha256IV)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat (placed_memcpy_step_sat_exact)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)

attribute [local arm64_norm]
  MemWidth.bytes SimdMemSize.bytes Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero Memory.read8_write64_base_off_inbounds

set_option maxHeartbeats 3200000 in
private theorem nfs_seg0_placed_exact [LibsignalPlacement] {H : LibsignalHooks}
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym) {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base) (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : CryptoVerification.LibsignalSession.CryptoHmacSha256.RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : CryptoVerification.LibsignalSession.CryptoHmacSha256.RW s₀.mem (s₀.sp - 544#64) 544)
    (hread_key_in : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      s'.pc = (blkPl_114).base + 476#64 ∧ s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧ NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧ s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧ s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key
  generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  refine RunsTo.pairStep_114_0x28 (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  have hreadable_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).Readable
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key_in)
  have hdisj_memcpy : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat
        (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · exact Or.inl h0
    · refine Or.inr ?_
      clear * - hdisj_key_stack hlen
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
  refine placed_memcpy_step_sat_exact h_memcpy
    (hrun := by simp only [arm64_norm, hstat])
    (hpc := by simp only [arm64_norm, lsMemcpySym])
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hsp_al := by simp only [arm64_norm]; exact hal_nfs)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key)
    (hrw := hrw_memcpy)
    (hreadable := hreadable_memcpy)
    (hdisj := hdisj_memcpy)
    fun c => ?_
  rw [writeBytes_key_over_zero64]
  dsimp only [applyMemcpyClobber]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key)
    rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
    simpa using h
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h
    exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64)
      [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv nfsPlacedFakeB s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack
    rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := by
      rw [nfsPlacedFakeB_add_iv]
      exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      rw [nfsPlacedFakeB_add_iv]
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := by rw [nfsPlacedFakeB_add_iv]; exact hdisj_iv_stack
    disj_out_stack := hdisj_out_stack
    saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0
    frame := hf_k0
  }
  have hM_final : NfsMemInv nfsPlacedFakeB s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes (nfsSp s₀ + 144#64) 32 =
      (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  refine ⟨by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

private theorem new_from_slice_placed_ro_ok_exact [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      { newFromSliceSpec F with
        pre := fun x s0 => (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ } := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [newFromSliceSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, ⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hrw_key : s0.mem.RW keyA key.length := fun a ha => hb_key.permNoLazy_rw hsep_key ha
  have hread_key : s0.mem.Readable keyA key.length := Memory.RW.readable hrw_key
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hx2_len : (s0.readReg64 .x2).toNat = key.length := hx2_nat
  have hal : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hkey_len' : (s0.mem.readBytes (s0.readReg64 .x1) (s0.readReg64 .x2).toNat).length ≤ 64 := by
    rw [Memory.readBytes_length, hx2_len]; exact hkey_len
  have hseg0 := nfs_seg0_placed_exact h_memcpy hpc hrun
    (by rw [hx2_len]; exact hkey_len) hiv_eq hread_iv
    (disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
    (by rw [hx0]; exact hrw_out) hrw_stk
    (by rw [hx1, hx2_len]; exact hread_key)
    (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
    (by rw [hx1, hx2_len]; exact hdisj_key) hal
  have hrunsTo :=
    hseg0.trans fun s1 ⟨hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1, hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩ =>
    (nfs_chunk1_placed hkey_len' hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans
      fun s2 ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩ =>
    (nfs_chunk2_placed hkey_len' hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
      (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans
      fun s3 ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩ =>
    (nfs_chunk3_placed hkey_len' hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
      hs0_3 hs16_3 hs32_3 hs48_3).trans
      fun s4 ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩ =>
    (nfs_chunk4_placed hkey_len' hal hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
      hs0_4 hs16_4 hs32_4 hs48_4).trans
      fun s5 ⟨hpc5, hstat5, hR5, hM5, hx0_5, hx1_5, hx2_5, hist5, hblk5, hivsw5⟩ =>
    nfs_second_half_placed h_compress hkey_len' hal hpc5 hstat5 hR5 hM5 hx0_5 hx1_5 hx2_5 hist5 hblk5 hivsw5
  rw [hx1, hx2_len, hkey_eq] at hrunsTo
  refine hrunsTo.to_reaches_pc fun sf h5 _ _ htr hvregs => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    CryptoVerification.LibsignalSession.CryptoHmacSha256.CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  dsimp only [newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  ac_nf at hpost ⊢

private theorem new_from_slice_block54_cro_ok_sat [LibsignalPlacement]
    (C : Crypto) (H : LibsignalHooks) [hH : HkdfPlacedHooksExactSat C.F H] :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with
        pre := fun x s0 =>
          (newFromSliceSpec C.F).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ } := by
  have h114 :=
    subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (new_from_slice_placed_ro_ok_exact C.F hH.memcpy hH.compress256)
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
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ ((newFromSliceSpec C.F).pre x s0 ∗ R) := by sep_ac_rfl
  have hcomm2 :
      (((newFromSliceSpec C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗
        ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗
        (⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((newFromSliceSpec C.F).pre x s0 ∗ R)) := by sep_ac_rfl
  rw [hcomm1, satisfies_pure_sepConj] at hp
  rw [hcomm2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

end ExactNewFromSliceLocal

theorem pqxdhHkdfExtractSome_placed_ok_block54_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 54)
      (pqxdhHkdfExtractSomePlacedSpec P lsmpl) := by
  have hext := extract_placed_ok_of_inv_sat C H
    (Inv := LibsignalCodeRoLoaded lsmpl)
    CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded.of_keepsFrozen (fun h => h.1)
    (new_from_slice_block54_cro_ok_sat C H)
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, saltA, salt, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExtractSomePlacedSpec] at hpre
  rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_extract sp] at hpre
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
              memRegion (sp - 4096#64) 3120 ∗ R)) := by sep_ac_rfl
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
            memRegion (s0.sp - 4096#64) 3120 ∗ R) := by sep_ac_rfl
    rw [hcomm_salt, satisfies_pure_sepConj]
    exact ⟨hsalt_ne, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [extractSpec, optSaltAt, pqxdhHkdfExtractSomePlacedSpec] at hpost ⊢
    rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_extract sp]
    subst hsp_eq
    have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P (some salt) ikm) := by
      dsimp [x, CryptoVerification.LibsignalTripleRatchet.ExtractGhost.prk]
      exact (bytesToBv8_hkdfExtractRef_some hP hsalt_len ikm).symm
    change sf.mem ⊨
      (⌜sf.trace = s0.trace⌝ ∗
        (ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 32#64) (x.prk C.F) [] ∗
        (⌜saltA ≠ 0#64⌝ ∗ (saltA ↦ₛ (u8Vec 32 salt).toList)) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
        stackAt s0.sp extractStack) ∗
      (memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3120 ∗ R) at hpost
    have hprk_ref_len : (hkdfExtractRef P (some salt) ikm).length = 32 :=
      hkdfExtractRef_length P (some salt) ikm
    rw [hsalt_list, hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 32#64) (by omega)] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    have hcomm_post :
        (ret ↦ₛ bytesToBv8 (hkdfExtractRef P (some salt) ikm)) ∗
          pqxdhHmacStateAt P (ret + 32#64) (hkdfExtractRef P (some salt) ikm) ∗
          ⌜saltA ≠ 0#64⌝ ∗ (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
          stackAt s0.sp extractStack ∗ memRegion (s0.sp - 8192#64) 3936 ∗
          memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗ R =
        ⌜saltA ≠ 0#64⌝ ∗
          ((ret ↦ₛ bytesToBv8 (hkdfExtractRef P (some salt) ikm)) ∗
            pqxdhHmacStateAt P (ret + 32#64) (hkdfExtractRef P (some salt) ikm) ∗
            (saltA ↦ₛ bytesToBv8 salt) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
            stackAt s0.sp extractStack ∗ memRegion (s0.sp - 8192#64) 3936 ∗
            memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗ R) := by sep_ac_rfl
    rw [hcomm_post, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨_, hpost⟩
    exact ⟨htr, by arm64_sep_close⟩

theorem pqxdhHkdfExtractNone_placed_ok_block54_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 54)
      (pqxdhHkdfExtractNonePlacedSpec P lsmpl) := by
  refine subroutine_ok_intro fun ⟨ret, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhHkdfExtractNonePlacedSpec] at hpre
  rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_extract sp] at hpre
  dsimp only [stackAt, extractStack, newFromSliceStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hx0, hx1, hx3, hx4, hsp_eq, hikm_len⟩, hsep⟩
  subst hsp_eq
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 15#64) = 0#64 := by simpa [State.spAligned] using hsp
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
  have hb_ret := IsBlock.memRegion ret 176
  have hb_ikm := IsBlock.pointsToBytes_len (a := ikmA) (rfl : x.ikm.length = x.ikm.length)
  have hb_stk := IsBlock.memRegion (sp0 - 544#64) 976
  have hsep_ret_stk : s0.mem ⊨ memRegion ret 176 ∗ (memRegion (sp0 - 544#64) 976 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗ (memRegion ret 176 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion ret 176 ∗
        (memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
          memRegion (s0.sp - 4096#64) 3120 ∗ memRegion (sp0 - 544#64) 976 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗
        (memRegion ret 176 ∗ memRegion (s0.sp - 8192#64) 3936 ∗
          memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗ R)) := by
    ac_nf at hsep ⊢
  have hRW_out : RW s0.mem (s0.readReg64 .x0) 176 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : RW s0.mem x.ikmA x.ikm.length :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 176 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm :=
    (hb_ikm.read hsep_ikm_ret).2
  have hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 176 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret hikm_pos (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk hikm_pos (by decide) hsep_ikm_stk
  have hruns := extract_none_long_placed_runsToE_of_inv_sat (C := C) (H := H)
    (Inv := LibsignalCodeRoLoaded lsmpl)
    CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded.of_keepsFrozen (fun h => h.1)
    (new_from_slice_block54_cro_ok_sat C H)
    (x := x) ⟨hF0.code, hF0.ro⟩ hpc hrun hsp0 hx1 hx3 hx4' rfl rfl hikm_cases hsp_al
    hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk
  refine hruns.to_reaches_pc fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [pqxdhHkdfExtractNonePlacedSpec]
  rw [CryptoVerification.LibsignalTripleRatchet.Keys.stackAt_alloc_extract s0.sp]
  dsimp only [stackAt, extractStack, newFromSliceStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P none ikm) := by
    dsimp [x, CryptoVerification.LibsignalTripleRatchet.ExtractGhost.prk]
    exact (bytesToBv8_hkdfExtractRef_none hP ikm).symm
  have hprk_ref_len : (hkdfExtractRef P none ikm).length = 32 :=
    hkdfExtractRef_length P none ikm
  have hprk_len : (x.prk C.F).length = 32 := by
    rw [hprk_eq, bytesToBv8_length, hprk_ref_len]
  have hb_prk := IsBlock.pointsToBytes_len (a := ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (ret + 32#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 32#64) (x.prk C.F) [])
      ret 176
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (ret + 32#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 32#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 544#64) 976 ∗ R_rest) :=
    CryptoVerification.LibsignalTripleRatchet.Extract.S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  rw [hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 32#64) (by omega)] at hpost_sep
  rw [hsp_m976]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

theorem pqxdhHkdfExtract_placed_ok_block54_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    PqxdhHkdfExtractPlacedOk P ((blkPC_54).rebase (blkPl_54).base H) :=
  ⟨pqxdhHkdfExtractNone_placed_ok_block54_sat hP, pqxdhHkdfExtractSome_placed_ok_block54_sat hP⟩

theorem pqxdhHkdfExtract_placed_ok_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  refine ⟨?_, ?_⟩
  · refine subroutine_ok_of_block_of_cl (pqxdhHkdfExtractNone_placed_ok_block54_sat hP)
      (fun ⟨_, _, _, _⟩ R s0 hpre => ?_) hi (by decide) (by decide)
    dsimp only [pqxdhHkdfExtractNonePlacedSpec] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.1.code
  · refine subroutine_ok_of_block_of_cl (pqxdhHkdfExtractSome_placed_ok_block54_sat hP)
      (fun ⟨_, _, _, _, _, _⟩ R s0 hpre => ?_) hi (by decide) (by decide)
    dsimp only [pqxdhHkdfExtractSomePlacedSpec] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.1.code

/-! ## 3. Unconditional `<HandshakeKeys>::derive` (Block `59`) under `[HkdfPlacedHooksSat]` -/

theorem handshakeKeysDerive_placed_ok_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [HkdfPlacedHooksExactSat C.F H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_59).rebase (blkPl_59).base H) (blkPl_59).base
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec P A)) :=
  handshakeKeysDerive_placed_ok hWF
    (pqxdhHkdfExtract_placed_ok_sat hP)
    (pqxdhHkdfExpandMultiInfo_placed_ok_sat hP)

theorem handshakeKeysDerive_placed_ok_of_block_sat [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec P A)) :=
  keys_ls_subroutine_ok_of_block_cro (handshakeKeysDerive_placed_ok_sat hWF hP) hi
    (by decide) (by decide)

/-! ## 4. `PqxdhPlacedHookContractsSat` Bundle and Coercion -/

/-- External-hook contract bundle replacing `HkdfPlacedHooks C.F H` with
`HkdfPlacedHooksSat C.F H`. -/
structure PqxdhPlacedHookContractsSat (P : Primitives) (C : Crypto) (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooksSat C.F H
  dh               : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsDhSym (diffieHellmanSpec C.X)
  sharedDrop       : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsSharedDropSym zeroizeSecretSpec
  staticDrop       : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsStaticDropSym zeroizeSecretSpec
  blackBox         : H lsBlackBoxU8Sym = some blackBoxHook
  noAllocShim      : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsRustNoAllocShimSym noAllocShimSpec
  alloc            : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsRustAllocSym (rustAllocSpec A)
  dealloc          : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  handleAllocError : H CryptoVerification.LibsignalTripleRatchet.Keys.lsHandleAllocErrorSym = some Rust.panicked
  handleError      : H CryptoVerification.E2E.Pqxdh.ResponderCore.lsHandleErrorSym = some Rust.panicked
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym
    (CryptoVerification.E2E.Pqxdh.ResponderCore.dalekMontToEdStubSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)

/-- Coercion `PqxdhPlacedHookContracts → PqxdhPlacedHookContractsSat` via `HkdfPlacedHooks.toSat`. -/
theorem PqxdhPlacedHookContracts.toSat {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} (h : PqxdhPlacedHookContracts P C A H) :
    PqxdhPlacedHookContractsSat P C A H :=
  { hkdf             := LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooks.toSat h.hkdf
    dh               := h.dh
    sharedDrop       := h.sharedDrop
    staticDrop       := h.staticDrop
    blackBox         := h.blackBox
    noAllocShim      := h.noAllocShim
    alloc            := h.alloc
    dealloc          := h.dealloc
    handleAllocError := h.handleAllocError
    handleError      := h.handleError
    kyberDecaps      := h.kyberDecaps
    dalekMontToEd    := h.dalekMontToEd
    dalekTorsionFree := h.dalekTorsionFree }

theorem PqxdhPlacedHookContractsSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk P A callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContractsSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk P A callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContractsSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooksSat C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok_sat hP hi

theorem PqxdhPlacedHookContractsSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooksSat C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok_sat hP hi

/-! ## 5. `PqxdhPlacedHookContractsExactSat` Bundle (`HookSatExactMemcpy`) & Projections -/

/-- `HookSatExactMemcpy` sibling of `PqxdhPlacedHookContractsSat`, replacing
`hkdf : HkdfPlacedHooksSat C.F H` with `hkdf : HkdfPlacedHooksExactSat C.F H` so no field
requires `H lsMemcpySym = some memcpyHook`. -/
structure PqxdhPlacedHookContractsExactSat (P : Primitives) (C : Crypto) (A : RustAlloc)
    (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooksExactSat C.F H
  dh               : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsDhSym (diffieHellmanSpec C.X)
  sharedDrop       : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsSharedDropSym zeroizeSecretSpec
  staticDrop       : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsStaticDropSym zeroizeSecretSpec
  blackBox         : H lsBlackBoxU8Sym = some blackBoxHook
  noAllocShim      : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsRustNoAllocShimSym noAllocShimSpec
  alloc            : HookSat H CryptoVerification.LibsignalTripleRatchet.Keys.lsRustAllocSym (rustAllocSpec A)
  dealloc          : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  handleAllocError : H CryptoVerification.LibsignalTripleRatchet.Keys.lsHandleAllocErrorSym = some Rust.panicked
  handleError      : H CryptoVerification.E2E.Pqxdh.ResponderCore.lsHandleErrorSym = some Rust.panicked
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym
    (CryptoVerification.E2E.Pqxdh.ResponderCore.dalekMontToEdStubSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubSpec P.isTorsionFree 160)

/-- Coercion `PqxdhPlacedHookContractsSat → PqxdhPlacedHookContractsExactSat` via
`HkdfPlacedHooksSat.toExactSat`. -/
theorem PqxdhPlacedHookContractsSat.toExactSat {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} (h : PqxdhPlacedHookContractsSat P C A H) :
    PqxdhPlacedHookContractsExactSat P C A H :=
  { hkdf := @LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat.HkdfPlacedHooksSat.toExactSat
              C.F H h.hkdf
    dh := h.dh, sharedDrop := h.sharedDrop, staticDrop := h.staticDrop, blackBox := h.blackBox
    noAllocShim := h.noAllocShim, alloc := h.alloc, dealloc := h.dealloc
    handleAllocError := h.handleAllocError, handleError := h.handleError
    kyberDecaps := h.kyberDecaps, dalekMontToEd := h.dalekMontToEd
    dalekTorsionFree := h.dalekTorsionFree }

/-- Coercion `PqxdhPlacedHookContracts → PqxdhPlacedHookContractsExactSat` via
`HkdfPlacedHooks.toExactSat`. -/
theorem PqxdhPlacedHookContracts.toExactSat {P : Primitives} {C : Crypto} {A : RustAlloc}
    {H : LibsignalHooks} (h : PqxdhPlacedHookContracts P C A H) :
    PqxdhPlacedHookContractsExactSat P C A H :=
  { hkdf := HkdfPlacedHooks.toExactSat h.hkdf, dh := h.dh, sharedDrop := h.sharedDrop
    staticDrop := h.staticDrop, blackBox := h.blackBox, noAllocShim := h.noAllocShim
    alloc := h.alloc, dealloc := h.dealloc, handleAllocError := h.handleAllocError
    handleError := h.handleError, kyberDecaps := h.kyberDecaps
    dalekMontToEd := h.dalekMontToEd, dalekTorsionFree := h.dalekTorsionFree }

theorem PqxdhPlacedHookContractsExactSat.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsExactSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk P A callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContractsExactSat.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsExactSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk P A callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.handleAllocError hi

theorem PqxdhPlacedHookContractsExactSat.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsExactSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok_sat hP hi

theorem PqxdhPlacedHookContractsExactSat.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContractsExactSat P C A H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooksExactSat C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok_sat hP hi

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoPlacedSat
