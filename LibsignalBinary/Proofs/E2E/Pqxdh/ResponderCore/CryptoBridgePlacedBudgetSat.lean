/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget

/-!
# `HookSat` Sibling of `CryptoBridgePlacedBudget` (`CryptoBridgePlacedBudgetSat`)

Re-types the `[HkdfPlacedHooks C.F H]` contracts in `CryptoBridgePlacedBudget`:
- `expand_multi_info_placed_vm_ok_of_other_block_sat`
- `pqxdhHkdfExpand_8_placed_ok_sat`
- `pqxdhHkdfExpand_10_placed_ok_sat`
to `[HkdfPlacedHooksBudgetSat C.F H]` (`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat

open Arm64 ProofLib SepProp BitVec
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded blkPC_53 blkPl_53 expandMultiInfoSpec expandMultiInfoStack
   keys_ls_subroutine_ok_of_block_cro
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Keys
  (hmacCore_entails_cells stackAt_alloc_expand)
open CryptoVerification.E2E.Pqxdh.Initiator
  (INFO_MSG_KEYS INFO_RATCHET Primitives bytesToBv8)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (PrimitivesMatchCrypto bytesToBv8_hkdfExpandRef_64 bytesToBv8_hkdfExpandRef_80
   bytesToBv8_length pqxdhHmacStateAt_eq)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (pqxdhHkdfExpandCellsPlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxSat
  (expand_multi_info_placed_vm_ok_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksBudgetSat HkdfPlacedHooksExactBudgetSat)

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
  unfold INFO_RATCHET
  rw [toUTF8_toList_eq]
  decide

private theorem INFO_MSG_KEYS_length : INFO_MSG_KEYS.length = 18 := by
  unfold INFO_MSG_KEYS
  rw [toUTF8_toList_eq]
  decide

/-- Cross-block transfer of `expand_multi_info_placed_vm_ok_sat` to any caller block `i < 619`. -/
public theorem expand_multi_info_placed_vm_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} (H : LibsignalHooks)
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactBudgetSat C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 53)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (expandMultiInfoSpec C.F))) :=
  keys_ls_subroutine_ok_of_block_cro
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded (expand_multi_info_placed_vm_ok_sat C H))
    hi (by decide) (by decide)

/-- `HandshakeDeriveBudget.pqxdhHkdfExpandCellsPlacedSpec P lsmpl 8` (`64` B, `info = INFO_RATCHET`)
on Block `53` under `[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem pqxdhHkdfExpand_8_placed_ok_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactBudgetSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 8) := by
  have hexp := expand_multi_info_placed_vm_ok_sat C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [stackAt_alloc_expand sp, ← memRegion_cells okmA 8 (by decide)] at hpre
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
  · apply satisfies_withLsCodeLoaded_intro hF.code
    dsimp only [withVmPreserved, expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inl trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfoSpec,
      pqxdhHkdfExpandCellsPlacedSpec,
      CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    rw [show 8 * 8 = 64 from rfl, bytesToBv8_hkdfExpandRef_64 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 64) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨hvm, htr, by arm64_sep_close⟩

/-- `HandshakeDeriveBudget.pqxdhHkdfExpandCellsPlacedSpec P lsmpl 10` (`80` B, `info = INFO_MSG_KEYS`)
on Block `53` under `[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem pqxdhHkdfExpand_10_placed_ok_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactBudgetSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (lsmpl.base 53)
      (pqxdhHkdfExpandCellsPlacedSpec P lsmpl 10) := by
  have hexp := expand_multi_info_placed_vm_ok_sat C H
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsPlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpre
  rw [stackAt_alloc_expand sp, ← memRegion_cells okmA 10 (by decide)] at hpre
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
  · apply satisfies_withLsCodeLoaded_intro hF.code
    dsimp only [withVmPreserved, expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inr trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfoSpec,
      pqxdhHkdfExpandCellsPlacedSpec,
      CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExpandCellsPlacedSpec] at hpost ⊢
    rw [stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, htr, hpost⟩
    rw [show 8 * 10 = 80 from rfl, bytesToBv8_hkdfExpandRef_80 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 80) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨hvm, htr, by arm64_sep_close⟩

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
