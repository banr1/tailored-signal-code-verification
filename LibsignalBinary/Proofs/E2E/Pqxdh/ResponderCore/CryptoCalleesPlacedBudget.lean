/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.ProgramReflection
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Unconditional Crypto Callees and Hook Bundle

Proves `VmPreserved` and `RustCliAllocBudget M` relocatable contracts under `[LibsignalPlacement]`
for `expand_multi_info` (`96` B on Block `53`), `GenericHkdf::extract` (Block `54`),
`<HandshakeKeys>::derive` (Block `59`), and `<RootKey>::create_chain` (Block `40`), and packages
the budget-threaded external-hook hypotheses into `PqxdhPlacedHookContracts`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open CryptoGames.HMAC (ShaState)
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkPC_40 blkPC_59 blkPl_40 blkPl_59
   libsignalMutatedBlocks libsignalSessionExterns libsignalSessionLib
   lsBlackBoxU8Sym lsMemcpySym lsRustDeallocSym
   ls_externAt?_blockProgram_eq_of_externs_eq lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet
  (ExpandMultiInfoGhost ExtractGhost HkdfPlacedHooks LibsignalCodeRoLoaded
   blkPC_53 blkPC_54 blkPl_53 blkPl_54
   diffieHellmanSpec expandMultiInfoStack extractSpec extractStack
   hmacCoreAt keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro
   optSaltAt subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded zeroizeSecretSpec)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (hmacCore_entails_cells lsDhSym lsRustAllocSym lsRustNoAllocShimSym
   lsSharedDropSym lsStaticDropSym stackAt_alloc_expand stackAt_alloc_extract)
open CryptoVerification.E2E (u8Vec)
open CryptoVerification.E2E.Pqxdh.Initiator
  (Bytes HandshakeKeysDeriveGhost INFO_PQXDH KyberDecapsCall Primitives StructuralPrims
   bytesToBv8 cryptoBoolRegStubSpec dalekMontToEdStubSpec hkdfExtractRef hkdfExtractRef_length
   kyberDecapsStubSpec pqxdhHmacStateAt pqxdhMemcpyRegionSpec)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto bytesToBv8_hkdfExpandRef_96 bytesToBv8_hkdfExtractRef_some
   bytesToBv8_length expandMultiInfo96_46Spec
   lsDalekMontToEdSym lsDalekTorsionFreeSym lsHandleErrorSym lsKyberDecapsSym
   pqxdhHmacStateAt_eq pqxdh_placed_externAt?_of_mem pqxdh_placed_hook_ok_of_mem
   u8Vec_toList_of_length)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec rustCliAllocNoOomSpec rustCliDeallocBudgetSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (PqxdhHkdfExpandMultiInfoPlacedOk PqxdhHkdfExtractPlacedOk
   handshakeKeysDerivePlacedBaseSpec handshakeKeysDerivePlacedVmSpec
   pqxdhHkdfExpandCellsPlacedSpec pqxdhHkdfExtractNonePlacedSpec pqxdhHkdfExtractSomePlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec framelessMemcpySpec noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
  (createChain_placed_ok_of_contracts
   extractBudgetSpec subroutine_ok_createChainSpecX_of_createChainSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget
  (createChainSpec createChainSpecX)
export CryptoVerification.E2E.Pqxdh.ResponderCore
  (lsDalekMontToEdSym lsDalekTorsionFreeSym lsHandleErrorSym lsKyberDecapsSym
   pqxdh_placed_externAt?_of_mem pqxdh_placed_hook_ok_of_mem)
export LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget
  (PqxdhCalculateAgreementPlacedFrozenOk PqxdhCalculateAgreementPlacedOk
   calculateAgreementEvents_eq calculateAgreement_placed_ok_unconditional
   calculateAgreement_placed_ok_x_unconditional
   ct_eq_ro_placed_vm_ok ct_eq_ro_placed_vm_ok_of_block ct_eq_ro_placed_vm_ok_withLsCodeLoaded
   expand_multi_info_placed_vm_ok expand_multi_info_placed_vm_ok_of_other_block
   pqxdhCalculateAgreementPlacedBaseSpec pqxdhCalculateAgreementPlacedFrozenSpec
   pqxdhCalculateAgreement_placed_frozen_of_cro pqxdhCalculateAgreement_placed_frozen_ok_of_block
   pqxdhCalculateAgreement_placed_ok pqxdhCalculateAgreement_placed_ok_of_block
   pqxdhHkdfExpand_10_placed_ok pqxdhHkdfExpand_8_placed_ok pqxdhHkdfExpand_other_placed_ok)
export LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAux
  (expand_multi_info_96_46_placed_vm_ok extract_placed_vm_ok_cro
   pqxdhHkdfExtractNone_placed_ok_block54)

private theorem satisfies_withLsCodeLoaded_intro {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hcl : LibsignalCodeLoaded pl s0.mem)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) :
    s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R := by
  dsimp only [withLsCodeLoaded]
  have hcomm : (spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by sep_ac_rfl
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
    hcallee_prog.eq_blockProgram ▸
      hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ)
    (reaches_outcome.of_outcome hout)

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

private theorem INFO_PQXDH_length : INFO_PQXDH.length = 46 := by
  unfold INFO_PQXDH
  rw [toUTF8_toList_eq]
  decide

/-! ## 1. `expand_multi_info` (Block `53`) for `k = 12` (`96` B) & `PqxdhHkdfExpandMultiInfoPlacedOk` -/

/-- `VmPreserved`-strengthened `Spec` for `expand_multi_info` (Block `53`) at `okmLen = 96`,
`info.length = 46`. -/
def expandMultiInfo96_46BudgetSpec (F : ShaState → List (BitVec 8) → ShaState) :
    Spec ExpandMultiInfoGhost :=
  withVmPreserved (expandMultiInfo96_46Spec F)

/-- Cross-block transfer of `expand_multi_info_96_46_placed_vm_ok` to any caller block `i < 619`. -/
theorem expand_multi_info_96_46_placed_vm_ok_of_other_block [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} (H : LibsignalHooks)
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (expandMultiInfo96_46BudgetSpec C.F)) :=
  keys_ls_subroutine_ok_of_block_cro
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (expand_multi_info_96_46_placed_vm_ok C H))
    hi (by decide) (by decide)

/-- `HandshakeDeriveBudget.pqxdhHkdfExpandCellsPlacedSpec P lsmpl 12` (`96` B, `info = INFO_PQXDH`)
on Block `53` from `expand_multi_info_96_46_placed_vm_ok`. -/
theorem pqxdhHkdfExpand_12_placed_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 12) := by
  have hexp := expand_multi_info_96_46_placed_vm_ok C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [stackAt_alloc_expand sp, ← memRegion_cells okmA 12 (by decide)] at hpre
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
  · apply satisfies_withLsCodeLoaded_intro hF.code
    dsimp only [withVmPreserved, expandMultiInfo96_46Spec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_len, trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfo96_46Spec,
      pqxdhHkdfExpandCellsPlacedSpec,
      CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [stackAt_alloc_expand sp, hinfo_len_bv]
    subst hsp
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    rw [show 8 * 12 = 96 from rfl, bytesToBv8_hkdfExpandRef_96 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ 46#64) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 96) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨hvm, htr, by arm64_sep_close⟩

/-- Discharges `HandshakeDeriveBudget.PqxdhHkdfExpandMultiInfoPlacedOk` on Block `53` for all `k`. -/
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

/-- Cross-block `HandshakeDeriveBudget.PqxdhHkdfExpandMultiInfoPlacedOk P callerProg` on any caller
block `i < 619` (including mutated caller blocks such as Block `79`). -/
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
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.1.1.code

/-! ## 2. `GenericHkdf::extract` (Block `54`) & `PqxdhHkdfExtractPlacedOk` -/

/-- Cross-block transfer of `extract_placed_vm_ok_cro` to any caller block `i < 619`. -/
theorem extract_placed_vm_ok_of_other_block [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} (H : LibsignalHooks)
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 54)
      (withLsCodeRoLoaded lsmpl (extractBudgetSpec C.F)) :=
  keys_ls_subroutine_ok_of_block_cro (extract_placed_vm_ok_cro C H)
    hi (by decide) (by decide)

/-- `subroutine_ok` for `HandshakeDeriveBudget.pqxdhHkdfExtractSomePlacedSpec` on Block `54`
(`salt = Some`, `32`-B `ikm`), derived from `extract_placed_vm_ok_cro`. -/
theorem pqxdhHkdfExtractSome_placed_ok_block54 [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 54)
      (pqxdhHkdfExtractSomePlacedSpec P lsmpl) := by
  have hext := extract_placed_vm_ok_cro C H
  refine subroutine_ok_map hext ?_
  rintro ⟨ret, saltA, salt, ikmA, ikm, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExtractSomePlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractSomePlacedSpec] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp_eq, hsalt_ne, hsalt_len, hikm_len⟩, hpre⟩
  let x : ExtractGhost := ⟨ret, saltA, some (u8Vec 32 salt), ikmA, bytesToBv8 ikm⟩
  have hsalt_list : (u8Vec 32 salt).toList = bytesToBv8 salt := u8Vec_toList_of_length hsalt_len
  have hikm_bv_len : x.ikm.length = 32 := by dsimp [x]; rw [bytesToBv8_length, hikm_len]
  refine ⟨x,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3120 ∗ R, ?_, ?_⟩
  · dsimp only [withLsCodeRoLoaded]
    have hcomm :
        ((extractBudgetSpec C.F).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗
          (memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
            memRegion (sp - 4096#64) 3120 ∗ R) =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          ((extractBudgetSpec C.F).pre x s0 ∗
            (memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
              memRegion (sp - 4096#64) 3120 ∗ R)) := by sep_ac_rfl
    rw [hcomm, satisfies_pure_sepConj]
    refine ⟨⟨hF.code, hF.ro⟩, ?_⟩
    dsimp only [extractBudgetSpec, withVmPreserved, extractSpec, optSaltAt, x]
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
    dsimp only [withLsCodeRoLoaded, extractBudgetSpec, withVmPreserved, extractSpec, optSaltAt,
      pqxdhHkdfExtractSomePlacedSpec,
      CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractSomePlacedSpec] at hpost ⊢
    rw [stackAt_alloc_extract sp]
    subst hsp_eq
    have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P (some salt) ikm) := by
      dsimp [x, ExtractGhost.prk]
      exact (bytesToBv8_hkdfExtractRef_some hP hsalt_len ikm).symm
    change sf.mem ⊨
      (⌜VmPreserved s0 sf⌝ ∗
        (⌜sf.trace = s0.trace⌝ ∗
          (ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [] ∗
          (⌜saltA ≠ 0#64⌝ ∗ (saltA ↦ₛ (u8Vec 32 salt).toList)) ∗ (ikmA ↦ₛ bytesToBv8 ikm) ∗
          stackAt s0.sp extractStack)) ∗
      (memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3120 ∗ R) at hpost
    have hprk_ref_len : (hkdfExtractRef P (some salt) ikm).length = 32 :=
      hkdfExtractRef_length P (some salt) ikm
    rw [hsalt_list, hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 0x20#64) (by omega)] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
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
            memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗ R) := by
      sep_ac_rfl
    rw [hcomm_post, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨_, hpost⟩
    exact ⟨hvm, htr, by arm64_sep_close⟩

/-- Discharges `HandshakeDeriveBudget.PqxdhHkdfExtractPlacedOk` on Block `54`. -/
theorem pqxdhHkdfExtract_placed_ok_block54 [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    PqxdhHkdfExtractPlacedOk P ((blkPC_54).rebase (blkPl_54).base H) :=
  ⟨pqxdhHkdfExtractNone_placed_ok_block54 hP, pqxdhHkdfExtractSome_placed_ok_block54 hP⟩

/-- Cross-block `HandshakeDeriveBudget.PqxdhHkdfExtractPlacedOk P callerProg` on any caller block
`i < 619` (including Block `59` and mutated caller blocks such as Block `79`). -/
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
    dsimp only [pqxdhHkdfExtractNonePlacedSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractNonePlacedSpec] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.1.code
  · refine subroutine_ok_of_block_of_cl (pqxdhHkdfExtractSome_placed_ok_block54 hP)
      (fun ⟨_, _, _, _, _, _⟩ R s0 hpre => ?_) hi (by decide) (by decide)
    dsimp only [pqxdhHkdfExtractSomePlacedSpec, withVmPreserved,
      CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractSomePlacedSpec] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact hpre.1.1.code

/-! ## 3. Unconditional `<HandshakeKeys>::derive` (Block `59`) & `<RootKey>::create_chain` (Block `40`) -/

/-- Unconditional relocatable `VmPreserved` `subroutine_ok` for `<HandshakeKeys>::derive`
(Block `59`), instantiating `HandshakeDeriveBudget.handshakeKeysDerive_placed_vm_ok`. -/
theorem handshakeKeysDerive_placed_vm_ok [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_59).rebase (blkPl_59).base H) (blkPl_59).base
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) :=
  LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget.handshakeKeysDerive_placed_vm_ok hWF
    (pqxdhHkdfExtract_placed_ok hP)
    (pqxdhHkdfExpandMultiInfo_placed_ok hP)

/-- Cross-block transfer of unconditional `handshakeKeysDerive_placed_vm_ok` to any caller block
`i < 619` (such as Block `75` `initialize_bob_session`). -/
theorem handshakeKeysDerive_placed_vm_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {P : Primitives} {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) :=
  keys_ls_subroutine_ok_of_block_cro (handshakeKeysDerive_placed_vm_ok hWF hP)
    hi (by decide) (by decide)

/-- Unconditional relocatable budget `subroutine_ok` for `<HandshakeKeys>::derive` (Block `59`),
instantiating `HandshakeDeriveBudget.handshakeKeysDerive_placed_ok`. -/
theorem handshakeKeysDerive_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_59).rebase (blkPl_59).base H) (blkPl_59).base
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) :=
  LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget.handshakeKeysDerive_placed_ok hWF
    (pqxdhHkdfExtract_placed_ok hP)
    (pqxdhHkdfExpandMultiInfo_placed_ok hP)

/-- Cross-block transfer of unconditional `handshakeKeysDerive_placed_ok` to any caller block
`i < 619` (such as Block `75` `initialize_bob_session`). -/
theorem handshakeKeysDerive_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (handshakeKeysDerive_placed_ok hWF hP)
    hi (by decide) (by decide)

/-- Unconditional relocatable budget `subroutine_ok` for `<RootKey>::create_chain` (Block `40`),
discharging Blocks `213`, `207`, `54`, and `53` internally from external hook contracts. -/
theorem createChain_placed_ok_unconditional [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H]
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) :=
  createChain_placed_ok_of_contracts
    (keys_ls_subroutine_ok_of_block_cro
      (calculateAgreement_placed_ok_unconditional h_dh h_shdrop h_bb h_shim h_alloc h_stdrop))
    (extract_placed_vm_ok_of_other_block C H)
    (expand_multi_info_placed_vm_ok_of_other_block C H)
    (keys_ls_hook_ok_of_mem h_dealloc)

/-- Cross-block transfer of `createChain_placed_ok_unconditional` to any caller block `i < 619`. -/
theorem createChain_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) :=
  keys_ls_subroutine_ok_of_block_cro
    (createChain_placed_ok_unconditional h_dh h_shdrop h_bb h_shim h_alloc h_stdrop h_dealloc)
    hi (by decide) (by decide)

/-- Unconditional relocatable budget `subroutine_ok` for `<RootKey>::create_chain` (Block `40`)
at `createChainStackX`. -/
theorem createChain_placed_ok_x_unconditional [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H]
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_40).rebase (blkPl_40).base H) (blkPl_40).base
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) :=
  subroutine_ok_createChainSpecX_of_createChainSpec
    (createChain_placed_ok_unconditional h_dh h_shdrop h_bb h_shim h_alloc h_stdrop h_dealloc)

/-- Cross-block transfer of `createChain_placed_ok_x_unconditional` to any caller block `i < 619`. -/
theorem createChain_placed_ok_x_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {C : Crypto} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooks C.F H]
    (h_dh : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X)))
    (h_shdrop : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (h_stdrop : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) :=
  keys_ls_subroutine_ok_of_block_cro
    (createChain_placed_ok_x_unconditional h_dh h_shdrop h_bb h_shim h_alloc h_stdrop h_dealloc)
    hi (by decide) (by decide)

/-! ## 4. Placed Budget External Hook Contracts for `ResponderCore` -/

/-- `VmPreserved`-strengthened contract for `libcrux_ml_kem::mlkem1024::kyber::decapsulate`. -/
def kyberDecapsStubBudgetSpec (P : Primitives) : Spec KyberDecapsCall :=
  withVmPreserved (kyberDecapsStubSpec P)

/-- `VmPreserved`-strengthened contract for `MontgomeryPoint::to_edwards`. -/
def dalekMontToEdStubBudgetSpec (P : Primitives) :=
  withVmPreserved (dalekMontToEdStubSpec P)

/-- `VmPreserved`-strengthened contract for boolean-returning Dalek helpers
(such as `EdwardsPoint::is_torsion_free`). -/
def cryptoBoolRegStubBudgetSpec (f : Bytes → Bool) (stk : Nat) :=
  withVmPreserved (cryptoBoolRegStubSpec f stk)

/-- `VmPreserved`-strengthened contract for `pqxdhMemcpyRegionSpec`. -/
def pqxdhMemcpyRegionBudgetSpec :=
  withVmPreserved pqxdhMemcpyRegionSpec

/-- Combined budget-threaded external-hook contract bundle for `ResponderCore`
(`AcceptPlaced` / `InitBobPlaced`) under `[LibsignalPlacement]`. -/
structure PqxdhPlacedHookContracts [LibsignalPlacement] (M : AllocCostModel) (P : Primitives) (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  hkdf             : HkdfPlacedHooks C.F H
  dh               : HookSat H lsDhSym (withVmPreserved (diffieHellmanSpec C.X))
  sharedDrop       : HookSat H lsSharedDropSym (withVmPreserved zeroizeSecretSpec)
  staticDrop       : HookSat H lsStaticDropSym (withVmPreserved zeroizeSecretSpec)
  blackBox         : H lsBlackBoxU8Sym = some blackBoxHook
  noAllocShim      : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec
  alloc            : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc          : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  kyberDecaps      : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)
  dalekMontToEd    : HookSat H lsDalekMontToEdSym (dalekMontToEdStubBudgetSpec P)
  dalekTorsionFree : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubBudgetSpec P.isTorsionFree 160)

theorem hookSat_noAllocShimBudget_of_rustAllocShimVm {H : LibsignalHooks}
    (h : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec) :
    HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec := by
  refine HookSat.mono h fun u R s0 hp => ?_
  dsimp only [noAllocShimBudgetSpec, withVmPreserved,
    CryptoVerification.LibsignalTripleRatchet.noAllocShimSpec, rustAllocShimVmSpec] at hp ⊢
  refine ⟨u, R, hp, fun sf hq => ?_⟩
  rw [satisfies_pure_sepConj] at hq
  rw [satisfies_pure_sepConj]
  exact ⟨⟨hq.1.1.2.1, hq.1.2⟩, hq.2⟩

theorem hookSat_pqxdhMemcpyRegionBudget_of_allocMemcpyVm {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    HookSat H lsMemcpySym pqxdhMemcpyRegionBudgetSpec := by
  refine HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hp => ?_
  dsimp only [pqxdhMemcpyRegionBudgetSpec, withVmPreserved, pqxdhMemcpyRegionSpec,
    memcpyRegionSpec, allocMemcpyVmSpec] at hp ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
  have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
  have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
    rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨(dst, src, bs), R, ?_, fun sf hq => ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0f, hacp, hvm⟩, hm'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0f, hacp.2.1⟩, hm'⟩

theorem hookSat_framelessMemcpy_of_allocMemcpyVm {H : LibsignalHooks}
    (h : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    HookSat H lsMemcpySym framelessMemcpySpec := by
  refine HookSat.mono (hookSat_pqxdhMemcpyRegionBudget_of_allocMemcpyVm h)
    fun ⟨dst, src, bs⟩ R s0 hp => ?_
  dsimp only [framelessMemcpySpec, framelessMemcpyBudgetSpec,
    pqxdhMemcpyRegionBudgetSpec, withVmPreserved, pqxdhMemcpyRegionSpec,
    memcpyRegionSpec] at hp ⊢
  refine ⟨(dst, src, bs), R, hp, fun sf hq => ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  rcases hq with ⟨hvm, hq'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
  rcases hq' with ⟨⟨hx0f, htr⟩, hmem⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨hx0f, htr, hvm⟩, hmem⟩

theorem kyberDecaps_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsKyberDecapsSym (kyberDecapsStubBudgetSpec P)) :
    subroutine_ok prog (lsρ lsKyberDecapsSym) (kyberDecapsStubBudgetSpec P) :=
  pqxdh_placed_hook_ok_of_mem h

theorem dalekMontToEd_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsDalekMontToEdSym (dalekMontToEdStubBudgetSpec P)) :
    subroutine_ok prog (lsρ lsDalekMontToEdSym) (dalekMontToEdStubBudgetSpec P) :=
  pqxdh_placed_hook_ok_of_mem h

theorem dalekTorsionFree_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {P : Primitives} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsDalekTorsionFreeSym (cryptoBoolRegStubBudgetSpec P.isTorsionFree 160)) :
    subroutine_ok prog (lsρ lsDalekTorsionFreeSym)
      (cryptoBoolRegStubBudgetSpec P.isTorsionFree 160) :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_shim_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_shim_vm_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSym) noAllocShimBudgetSpec :=
  pqxdh_shim_placed_ok (hookSat_noAllocShimBudget_of_rustAllocShimVm h)

theorem pqxdh_alloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok prog (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_allocNoOom_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok prog (lsρ lsRustAllocSym) (rustCliAllocNoOomSpec M A lim false) :=
  subroutine_ok_allocNoOom_of_budget (pqxdh_alloc_placed_ok h)

theorem pqxdh_dealloc_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_memcpy_region_raw_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsMemcpySym pqxdhMemcpyRegionBudgetSpec) :
    subroutine_ok prog (lsρ lsMemcpySym) pqxdhMemcpyRegionBudgetSpec :=
  pqxdh_placed_hook_ok_of_mem h

theorem pqxdh_memcpy_region_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok prog (lsρ lsMemcpySym) pqxdhMemcpyRegionBudgetSpec :=
  pqxdh_memcpy_region_raw_placed_ok (hookSat_pqxdhMemcpyRegionBudget_of_allocMemcpyVm h)

theorem PqxdhPlacedHookContracts.calculateAgreement_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

theorem PqxdhPlacedHookContracts.calculateAgreement_frozen_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhCalculateAgreementPlacedFrozenOk M P A lim callerProg :=
  pqxdhCalculateAgreement_placed_frozen_ok_of_block hP hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hi

theorem PqxdhPlacedHookContracts.hkdfExtract_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExtractPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExtract_placed_ok hP hi

theorem PqxdhPlacedHookContracts.hkdfExpandMultiInfo_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    PqxdhHkdfExpandMultiInfoPlacedOk P callerProg := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact pqxdhHkdfExpandMultiInfo_placed_ok hP hi

theorem PqxdhPlacedHookContracts.handshakeKeysDerive_vm_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedVmSpec P)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact handshakeKeysDerive_placed_vm_ok_of_block hWF hP hi

theorem PqxdhPlacedHookContracts.handshakeKeysDerive_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hWF : StructuralPrims P)
    (hP : PrimitivesMatchCrypto P C)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 59)
      (withLsCodeRoLoaded lsmpl (handshakeKeysDerivePlacedBaseSpec M P A lim)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact handshakeKeysDerive_placed_ok_of_block hWF hP hi

theorem PqxdhPlacedHookContracts.createChain_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpec M A lim C)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact createChain_placed_ok_of_block hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

theorem PqxdhPlacedHookContracts.createChain_x_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    {M : AllocCostModel} {P : Primitives} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hH : PqxdhPlacedHookContracts M P C A lim H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 40)
      (withLsCodeRoLoaded lsmpl (createChainSpecX M A lim C)) := by
  have _ : HkdfPlacedHooks C.F H := hH.hkdf
  exact createChain_placed_ok_x_of_block hH.dh hH.sharedDrop hH.blackBox
    hH.noAllocShim hH.alloc hH.staticDrop hH.dealloc hi

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudget
