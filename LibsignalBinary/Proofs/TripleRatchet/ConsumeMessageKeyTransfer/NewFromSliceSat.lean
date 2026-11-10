/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact
import ProofLib.SepLogic.Entry

/-!
# `HookSatExactMemcpy`-backed `ConsumeMessageKeyTransfer.NewFromSlice` Siblings (`NewFromSliceSat`)

Replaces `H lsMemcpySym = some memcpyHook` with `HookSatExactMemcpy H lsMemcpySym` in
`new_from_slice_placed_ro_ok` and `new_from_slice_placed_ok_withLsCodeLoaded_ro` (Block `114`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSliceSat

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement LibsignalRoLoaded blkPC_114 blkPl_114 lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  CallingConventionPreserved_of_calleeSaved Frame.update_two_blocks disjointRegions_of_ro_rw
  lsCompress256Sym lsMemcpySym lsSha256IVAddr
)
open CryptoVerification.LibsignalTripleRatchet (newFromSliceSpec newFromSliceStack)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (
  isBlock_nfsResult rodata_placed_sha256IV
)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceExact (
  new_from_slice_placed_run_exact
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)

/-- `HookSatExactMemcpy` sibling of
`ConsumeMessageKeyTransfer.new_from_slice_placed_ro_ok` (`NewFromSlice.lean:202`, Block `114`). -/
theorem new_from_slice_placed_ro_ok_sat [LibsignalPlacement] (F : ShaCompress)
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
  have hread_key : s0.mem.Readable keyA key.length := by
    intro a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hb_key.permNoLazy_rw hsep_key ha)
    exact ⟨by rw [hp]; rfl, hlf⟩
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hx2_len : (s0.readReg64 .x2).toNat = key.length := hx2_nat
  have hrunsTo := new_from_slice_placed_run_exact (F := F)
    h_memcpy h_compress
    hpc hrun (by rw [hx2_len]; exact hkey_len) hiv_eq
    hread_iv (disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
    (by rw [hx0]; exact hrw_out) hrw_stk
    (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
    (by rw [hx1, hx2_len]; exact hread_key)
    (by rw [hx1, hx2_len]; exact hdisj_key)
    (by simpa [State.spAligned] using hsp)
  rw [hx1, hx2_len, hkey_eq] at hrunsTo
  refine hrunsTo.to_reaches_pc fun sf h5 _ _ htr hvregs => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  dsimp only [newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  ac_nf at hpost ⊢

/-- `withLsCodeLoaded` corollary of `new_from_slice_placed_ro_ok_sat` (`NewFromSlice.lean:264`). -/
theorem new_from_slice_placed_ok_withLsCodeLoaded_ro_sat [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      (withLsCodeLoaded lsmpl
        { newFromSliceSpec F with
          pre := fun x s0 => (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }) :=
  subroutine_ok_withLsCodeLoaded_of_plain (new_from_slice_placed_ro_ok_sat F h_memcpy h_compress)

end LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSliceSat
