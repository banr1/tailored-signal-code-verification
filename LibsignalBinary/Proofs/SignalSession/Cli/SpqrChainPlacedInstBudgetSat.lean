/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpand
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand

/-!
# `HookSat` Sibling of `SignalSession.Cli.SpqrChainPlacedInstBudget` (`SpqrChainPlacedInstBudgetSat`)

Replaces `H lsMemsetSym = some memsetHook` / `memset_row_placed` in `SpqrChainPlacedInstBudget` with
`HookSat ... "memset" (withAllocVmPreserved sessionMemsetRegionSpec)` via
`HkdfPlacedHooksAllocVmSat` and `HkdfToSliceOkBudgetSat.hkdf_to_slice_kdf_vm_sat`.
All `memset`-free theorems from `SpqrChainPlacedInstBudget` are re-exported via `public import`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudgetSat

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   blkPC_363 blkPC_379 blkPl_363 blkPl_379
   libsignalMutatedBlocks libsignalSessionLib
   ls_externAt?_of_mem lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send (spqrSendPlacedProg)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (disjointRegions_of_ro_rw)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet
  (CallingConventionPreserved_of_calleeSaved TraceEq
   extHookStack extract_withLsCodeRoLoaded
   keys_ls_subroutine_ok_of_block_cro lsCompress256Sym lsMemcpySym lsMemsetSym
   sessionMemsetRegionSpec withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (hkdfExpand_64_eq t1_length t2_length t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
   hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced compress256_row_placed
   lsRngFillSym trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (ls_subroutine_ok_callInv_of_block subroutine_ok_withLsCallInv_of_withLsCodeLoaded withLsCallInv)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (hkdfCodeFakeB hkdfExpand_32_eq hkdfExpand_96_eq hsp rodata_sha256IV_placed)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof (nfs3PlacedFakeB_add_iv spqrSha256IVAddr)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt (disjointRegions_of_outside)
open CryptoVerification.SpqrV1.States.Leaves
  (subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_323 blkPl_323 blkPC_328 blkPl_328)
open CryptoVerification.SpqrV1.Top.Recv
  (ls_subroutine_ok_callInv_of_callInv ls_subroutine_ok_cro_of_callInv spqrRecvPlacedProg)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyGhostExact (HookSatExactMemcpy)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_exactMemcpy_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
  (cliAllocBudgetWithStack_at_block cliChainFromPb_cl cliExternsPlaced_rustAllocShimVm_sat
   cliVecDequeGrow_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (chainNewSpecX vecDequeGrowSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.NewBudget (chainNew_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat
  (HFrameS2 HPreBase bytesAt_outside_rw bytesAt_read bytesAt_readable
   hkdf_to_slice_kdf_vm_sat stackAt_hkdfToSlice)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat (ProgMemsetAllocVm)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX chainFromSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlacedBudget
  (chainFrom_placed_ok_of_contracts_x)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlacedBudget
  (chainFromVersionNegotiation_placed_ok_of_contracts_x)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (subroutine_ok_withStack_of_subroutine_ok withStack)

/-! ## 0. `HkdfPlacedHooksAllocVmSat` & Block `379` `withAllocVmPreserved` under `HookSat` -/

/-- `withAllocVmPreserved`-strengthened `HookSat` sibling of `HkdfPlacedHooksExactSat` for SPQR
chain callees (`Chain::new`, `ChainEpochDirection::next_key_internal`, `Chain::add_epoch`). -/
class HkdfPlacedHooksAllocVmSat (F : ShaCompress) (H : LibsignalHooks) : Prop where
  memset : HookSat H lsMemsetSym (withAllocVmPreserved sessionMemsetRegionSpec)
  memcpy : HookSatExactMemcpy H lsMemcpySym
  compress256 : H lsCompress256Sym = some (compress256Hook F)

/-- Weakening from `withAllocVmPreserved sessionMemsetRegionSpec` to
`sessionMemsetRegionBudgetSpec`. -/
theorem hookSat_sessionMemsetRegionBudget_of_allocVm
    {H : String → Option (State → State)} {sym : String}
    (h : HookSat H sym (withAllocVmPreserved sessionMemsetRegionSpec)) :
    HookSat H sym sessionMemsetRegionBudgetSpec := by
  refine ProofLib.HookSat.mono h fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩
  dsimp only [withAllocVmPreserved, sessionMemsetRegionBudgetSpec] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨hpost.1.2, hpost.2⟩

/-- Coercion from `HkdfPlacedHooksAllocVmSat` to `HkdfPlacedHooksExactSat`. -/
theorem HkdfPlacedHooksAllocVmSat.toExactSat {F : ShaCompress} {H : LibsignalHooks}
    (h : HkdfPlacedHooksAllocVmSat F H) : HkdfPlacedHooksExactSat F H where
  memset := by
    refine ProofLib.HookSat.mono h.memset fun x R s0 hpre => ⟨x, R, hpre, fun sf hpost => ?_⟩
    dsimp only [withAllocVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  memcpy := h.memcpy
  compress256 := h.compress256

/-- **Block `379` (`spqr::kdf::hkdf_to_slice`, 473 instructions) meets
`withLsCodeRoLoaded lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))`** on
`(blkPC_379).rebase (blkPl_379).base H` under `[HkdfPlacedHooksAllocVmSat C.F H]`. -/
theorem hkdf_to_slice_spqr_allocVm_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [hH : HkdfPlacedHooksAllocVmSat C.F H] :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) := by
  let _ : HkdfPlacedHooksExactSat C.F H := hH.toExactSat
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨ (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)).pre x s0 ∗ R at hpre
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 544#64) 1232
  let R_inv : SepProp :=
    bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) := by dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 544#64) 1232 ∗
      (memRegion x.okmA x.okmLen ∗ R_inv) := by dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 544#64) 1232 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_placed hro
  have hread_iv : s0.mem.Readable spqrSha256IVAddr 32 := fun a ha =>
    let ⟨hp, hlf⟩ := hro_iv a ha; ⟨by rw [hp]; rfl, hlf⟩
  have hout_salt_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have hb : HPreBase x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0 :=
    { pre :=
        { pc_eq := by rw [hkdfCodeFakeB, BitVec.sub_add_cancel]; exact hpc,
          status := hrun,
          x0_eq := hx0, x1_eq := hx1, x2_eq := hx2, x3_eq := hx3,
          x4_eq := hx4, x5_eq := hx5, x6_eq := hx6, x7_eq := hx7,
          salt_lt := hsalt_lt, ikm_len := hikm_len, info_ge := hinfo_ge,
          info_lt := hinfo_lt, okm_len := hokm_len, base_al := trivial,
          ro_iv_bytes := by rw [nfs3PlacedFakeB_add_iv]; exact hiv_eq,
          ro_iv_read := by rw [nfs3PlacedFakeB_add_iv]; exact hread_iv,
          disj_iv_stk := by
            rw [nfs3PlacedFakeB_add_iv]
            exact disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk,
          disj_iv_okm := by
            rw [nfs3PlacedFakeB_add_iv]
            exact disjointRegions_of_ro_rw (by decide) hokm_pos hro_iv hrw_okm,
          salt_bytes := bytesAt_read (by omega) hsep_salt_stk,
          ikm_bytes := bytesAt_read (by omega) hsep_ikm_stk,
          info_bytes := bytesAt_read (by omega) hsep_info_stk,
          rw_okm := hrw_okm, rw_stack := hrw_stk,
          disj_okm_stk := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk,
          disj_salt_stk := by
            by_cases h0 : x.salt.length = 0; · exact Or.inl h0
            · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk),
          out_salt_stk := hout_salt_stk,
          out_salt_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm,
          out_ikm_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk,
          out_ikm_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm,
          out_info_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk,
          out_info_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm,
          sp_aligned := by simpa [State.spAligned] using hsp_al },
      read_salt := bytesAt_readable (by omega) hsep_salt_stk,
      read_ikm := bytesAt_readable (by omega) hsep_ikm_stk,
      read_info := bytesAt_readable (by omega) hsep_info_stk }
  intro hL0
  obtain ⟨sf, hsteps_H, hvm, hacp_imp, htr, _hvregs,
    ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩, _⟩ :=
    hkdf_to_slice_kdf_vm_sat (C := C)
      (hookSat_sessionMemsetRegionBudget_of_allocVm hH.memset) hcl hb hL0
  have hpma : ProgMemsetAllocVm ((blkPC_379).rebase (blkPl_379).base H) := by
    obtain ⟨f, hfH, hfOk⟩ := hH.memset
    refine ⟨f, ?_, hfOk⟩
    rw [ls_externAt?_of_mem (by decide) (by decide) (by decide), hfH]
  have _ : TraceEq s0 sf := ⟨htr, _hvregs⟩
  refine ⟨sf, hsteps_H, Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩⟩
  dsimp only [withLsCodeRoLoaded, withAllocVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hacp_imp hpma, hvm⟩, ?_⟩
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec]; dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]
    rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [t1_length, t2_length, t3_length]
  refine ⟨⟨h_exp_len, htr⟩, ?_⟩
  unfold HFrameS2 at hframe_sf
  rw [hx6] at hframe_sf
  rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    S2Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [stackAt_hkdfToSlice s0]
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- Cross-block lift of `hkdf_to_slice_spqr_allocVm_placed_ok_sat` to any caller block `i < 619`. -/
theorem hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksAllocVmSat C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl
        (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_slice_spqr_allocVm_placed_ok_sat C) hi

/-! ## 1. CLI Chain Callees under `HookSat ... "memset" (withAllocVmPreserved sessionMemsetRegionSpec)` -/

private theorem hkdfPlacedHooksAllocVmSat_cliExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    HkdfPlacedHooksAllocVmSat W.C.F H where
  memset := hookSat_of_eq (hExt _ (by decide)) hMemset
  memcpy := by
    rcases cliExternsPlaced_exactMemcpy_sat mmpl gh W hA with ⟨f, hf, hex⟩
    exact ⟨f, (hExt _ (by decide)).trans hf, hex⟩
  compress256 := by
    rw [hExt _ (by decide), cliGhostExterns_other gh (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W)

private theorem hExt_withPanics_sat
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym hne
  have h1 : Rust.withPanics ext sym =
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
    simp only [Rust.withPanics, hExt sym hne]
  exact h1.trans (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)

private theorem cliRustAllocShimVm_at_block_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (hShim : gh.shim = hookNoop := by rfl)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      rustAllocShimVmSpec :=
  spqr_hook_ok_of_mem
    (hookSat_of_eq (hExt lsRustNoAllocShimSymCli (by decide))
      (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hShim))
    (by decide) hi hunmut

private theorem cliRustAllocShimVmWithStack_at_block_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H] (stk : Nat := extHookStack)
    (hShim : gh.shim = hookNoop := by rfl)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack rustAllocShimVmSpec stk) :=
  subroutine_ok_withStack_of_subroutine_ok
    (cliRustAllocShimVm_at_block_sat mmpl gh W hExt hShim hi hunmut) stk

/-- Budget-threaded Block `363` (`<spqr::chain::Chain>::new`) under `cliGhostExterns` and
`HookSat ... "memset" (withAllocVmPreserved sessionMemsetRegionSpec)`. -/
theorem cliChainNew_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (blkPl_363).base
      (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have : HkdfPlacedHooksAllocVmSat W.C.F H :=
    hkdfPlacedHooksAllocVmSat_cliExt mmpl gh W hA hMemset hExt
  have hhkdf_363 : subroutine_ok
      ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat W.C)
  have hgrow_363 : subroutine_ok
      ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 353)
      (withLsCallInv lsmpl (vecDequeGrowSpec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (CryptoVerification.ls_subroutine_ok_of_block (i := 363) (j := 353)
        (cliVecDequeGrow_placed_ok mmpl gh W hA hExt))
  exact chainNew_placed_ok
    hhkdf_363 hgrow_363
    (cliRustAllocShimVmWithStack_at_block_sat mmpl gh W hExt extHookStack hA.shim_eq)
    (cliAllocBudgetWithStack_at_block mmpl gh W hA hExt)

/-- Own-block `blockProgram` form of Block `328` (`spqr::chain_from_version_negotiation`)
under `Rust.withPanics ext` and `HookSat ... "memset"`. -/
theorem cliChainFromVn_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 328 (Rust.withPanics ext))
      (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl
        (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have hnew_328 : subroutine_ok
      ((blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))
      (lsmpl.base 363)
      (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 328) (j := 363)
      (cliChainNew_placed_ok_sat mmpl gh W hA hMemset (hExt_withPanics_sat mmpl gh W hExt))
  have hraw := chainFromVersionNegotiation_placed_ok_of_contracts_x hnew_328
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))]
  exact subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hraw

/-- Block `328` (`spqr::chain_from_version_negotiation`) lifted to `spqrSendPlacedProg ext`
(`Block 427`) under `HookSat ... "memset"`. -/
theorem cliSpqrSend_chainFromVn_ok_ext_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl
        (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have hnew_328 : subroutine_ok
      ((blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))
      (lsmpl.base 363)
      (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 328) (j := 363)
      (cliChainNew_placed_ok_sat mmpl gh W hA hMemset
        (H := Rust.withPanics ext) (hExt_withPanics_sat mmpl gh W hExt))
  exact ls_subroutine_ok_cro_of_callInv (i := 427) (j := 328)
    (chainFromVersionNegotiation_placed_ok_of_contracts_x hnew_328)

/-- Exact `hChainFromVn` hypothesis of `spqrSendPlacedContractsTight_of_okX` at
`cliGhostExterns gh (cliExternsPlaced mmpl W)` under `HookSat ... "memset"`. -/
theorem cliSpqrSend_chainFromVn_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl
        (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  cliSpqrSend_chainFromVn_ok_ext_sat mmpl gh W hA hMemset (fun _ _ => rfl)

/-- Exact `chainNew_ok` field of `SpqrRecvPlacedContracts` under `HookSat ... "memset"`. -/
theorem cliSpqrRecv_chainNew_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 363) (withLsCodeRoLoaded lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  ls_subroutine_ok_cro_of_callInv (i := 329) (j := 363)
    (cliChainNew_placed_ok_sat mmpl gh W hA hMemset
      (H := Rust.withPanics ext) (hExt_withPanics_sat mmpl gh W hExt))

/-- Exact `chainFrom_ok` field of `SpqrRecvPlacedContracts` (Block `323`) under
`HookSat ... "memset"`. -/
theorem cliSpqrRecv_chainFrom_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 323) (withLsCodeRoLoaded lsmpl (chainFromSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have h_fpb_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
      (lsmpl.base 364) (withLsCallInv lsmpl (chainFromPbSpecX M A lim)) :=
    ls_subroutine_ok_callInv_of_callInv (i := 323) (j := 364)
      (subroutine_ok_withLsCallInv_of_withLsCodeLoaded
        (cliChainFromPb_cl mmpl gh W hA
          (H := Rust.withPanics ext) (hExt_withPanics_sat mmpl gh W hExt)))
  have h_new_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_callInv (i := 323) (j := 363)
      (cliChainNew_placed_ok_sat mmpl gh W hA hMemset
        (H := Rust.withPanics ext) (hExt_withPanics_sat mmpl gh W hExt))
  exact ls_subroutine_ok_cro_of_callInv (i := 329) (j := 323)
    (chainFrom_placed_ok_of_contracts_x h_fpb_323 h_new_323)

/-- Specialization of `cliSpqrRecv_chainNew_ok_sat` to
`trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem cliSpqrRecv_chainNew_ok_trTrap_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 363) (withLsCodeRoLoaded lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  cliSpqrRecv_chainNew_ok_sat mmpl gh W hA hMemset
    (fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne])

/-- Specialization of `cliSpqrRecv_chainFrom_ok_sat` to
`trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))`. -/
theorem cliSpqrRecv_chainFrom_ok_trTrap_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 323) (withLsCodeRoLoaded lsmpl (chainFromSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  cliSpqrRecv_chainFrom_ok_sat mmpl gh W hA hMemset
    (fun sym hne => by simp [trTrapExternsPlaced, lsRngFillSym, ProofLib.Variant.trapAt, hne])

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudgetSat
