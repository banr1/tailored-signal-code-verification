/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxCSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxDSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedA
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.SepLogic.HeapIntro
import ProofLib.SepLogic.WP.Apply

/-!
# `HookSat` Sibling of `CryptoCalleesPlacedBudgetAux` (`CryptoCalleesPlacedBudgetAuxSat`)

Exports `expand_multi_info_96_46_placed_vm_ok_sat` from `CryptoCalleesPlacedBudgetAuxCSat` and
proves `extract_placed_vm_ok_cro_sat` and `pqxdhHkdfExtractNone_placed_ok_block54_sat` on Block `54`
(`GenericHkdf::extract`, `32`-B and `160` / `192` / `224`-B `ikm`) under
`[HkdfPlacedHooksBudgetSat C.F H]` (`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`).
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxSat

open Arm64 ProofLib SepProp BitVec
open CryptoGames.HKDF (hkdfExtract)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
   libsignalRoLoaded_of_keepsFrozen lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (memcpyHook)
open CryptoVerification.LibsignalHmac (compress256Hook)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved ExtractGhost
   HmacSt LibsignalCodeRoLoaded NewFromSliceGhost blkPC_123 blkPC_54 blkPl_123 blkPl_54
   effectiveSalt extPlacedFakeB extPlacedFakeB_off_380 extPlacedFakeB_off_80 extractSpec
   extractStack extract_withLsCodeRoLoaded finPlacedFakeB finPlacedFakeB_off_0
   hmacCoreAt isBlock_hmacCoreAt length_hmacWith lsCompress256Sym lsMemcpySym
   newFromSliceSpec newFromSliceStack optSaltAt withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x27
   CallingConventionPreserved.x29 EC88 EFinPlaced EMemcpyPlaced ENfs1Placed EPost ERet1 ERetFin
   ExtCommon ExtFrame ExtSaved RunsToE S2Frame
   disj_sp0_off disj_sp0_sub_off disj_stk_sub_right disjoint_fullComplementHeap
   effectiveSalt_length fullComplementHeap hmacSt_saltSliceOf isBlock_three_s2frame
   matches_fullComplementHeap nfs1_placed_runsTo pointsToBytes_saltRegOf_eq rw_stk_sub
   saltPtrOf saltRegOf saltSliceOf saltSliceOf_length_le satisfies_three_blocks
   seg0_placed_runsTo seg1a_placed_runsTo seg1c_placed_runsTo
   sp0_aligned sp0_aligned_0b1111)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open CryptoVerification.LibsignalTripleRatchet.Keys (stackAt_alloc_extract)
open CryptoVerification.E2E.Pqxdh.Initiator
  (Primitives bytesToBv8 hkdfExtractRef hkdfExtractRef_length)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (EC88Long ECompLongPlaced EFinLongPlaced EMemcpyLongPlaced ENfs1LongPlaced ERet1Long
   FinGenPre PrimitivesMatchCrypto
   bytesToBv8_hkdfExtractRef_none bytesToBv8_length
   nfs1_long_placed_runsTo pqxdhHmacStateAt_eq
   seg0_long_placed_runsTo seg1a_long_placed_runsTo seg1c_long_placed_runsTo)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (pqxdhHkdfExtractNonePlacedSpec)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
  (RunsToVm finalize_fixed_placed_runsToVm_sat stripS_hmacSt)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat
  (finalize_fixed_gen_placed_runsToVm_sat seg1b1_long_hc256 seg1b2_long_hmc seg1b_hmc
   stripS_hmacStGen)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxDSat
  (Ext54_114CodeRoLoaded cl_of_keepsFrozen ext54_114CodeRoLoaded_of_cro
   ext54_114CodeRoLoaded_strip keepExt54_114 lift_runsToE_ext54_114_vm
   lift_runsToE_ext54_114_vm_compress_only
   new_from_slice_ext54_114_ok noMemsetKdfHooks noMemsetKdfHooks_compress256
   noMemsetKdfHooks_memcpy noMemsetMemcpyKdfHooks noMemsetMemcpyKdfHooks_compress256
   post_fin_vm_runsTo_sat strip_permNoLazy_rw strip_readBytes
   unstrip_efinLongPlaced unstrip_efinPlaced)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedSat
  (extFrame_trans_triple_s2)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (stripS_pc stripS_readReg64 stripS_sp stripS_status)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
  (new_from_slice_placed_ro_vm_ok_at_block_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksBudgetSat HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget (extractBudgetSpec)

export LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxCSat
  (expand_multi_info_96_46_placed_vm_ok_sat)

/-! ## 1. Piece B (`finalize_fixed` on Block `123`) Lifted to Block `54` (`RunsToVm`) -/

private theorem fin_short_vm_runsTo_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksExactBudgetSat C.F H] {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinPlaced C.F x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (ERetFin extPlacedFakeB C.F x s0 sp0) := by
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
  have hrw_336 : Memory.RW s.mem (sp0 + 336#64) 96 :=
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
      disj_out_fsp := by
        rw [hx0, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by
        rw [hx1, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact sp0_aligned_0b1111 hsp_al }
  have h123 := RunsToVm.of_other_block (i := 54) (j := 123)
    (Pi := (blkPC_54).rebase (blkPl_54).base H)
    (Pj := (blkPC_123).rebase (blkPl_123).base H)
    (by decide) (by decide) hcl
    (finalize_fixed_placed_runsToVm_sat (C := C) (H := H) hcl hpre)
  refine h123.mono fun s' hs' => ?_
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

private theorem fin_long_vm_runsTo_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksExactBudgetSat C.F H] {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinLongPlaced C.F x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (ERetFin extPlacedFakeB C.F x s0 sp0) := by
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
  have hrw_336 : Memory.RW s.mem (sp0 + 336#64) 96 :=
    hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)
  have hpre : FinGenPre finPlacedFakeB C.F (effectiveSalt x.salt)
      (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64))) s :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hpc
      status := hstat
      key_le := by rw [effectiveSalt_length]; decide
      rem_lt := by simp; omega
      hmac_st := by rw [hx1]; exact hhm
      rw_out := by rw [hx0]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144.2)
      rw_hm := by rw [hx1]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_176.2)
      rw_fsp := by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_m144.2)
      disj_out_hm := by
        rw [hx0, hx1]; exact disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide)
      disj_out_fsp := by
        rw [hx0, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by
        rw [hx1, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact sp0_aligned_0b1111 hsp_al }
  have h123 := RunsToVm.of_other_block (i := 54) (j := 123)
    (Pi := (blkPC_54).rebase (blkPl_54).base H)
    (Pj := (blkPC_123).rebase (blkPl_123).base H)
    (by decide) (by decide) hcl
    (finalize_fixed_gen_placed_runsToVm_sat (C := C) (H := H) hcl hpre)
  refine h123.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0, List.take_append_drop] at hout
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

/-! ## 2. Block `54` `extract_placed_vm_ok_cro_sat` & `pqxdhHkdfExtractNone_placed_ok_block54_sat` -/

private theorem extract_salt_props_976 {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    {R : SepProp}
    (hb_stk : IsBlock (memRegion (sp0 - 544#64) 976) (sp0 - 544#64) 976 (fun _ => True))
    (hsep : s0.mem ⊨
      (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
        memRegion (sp0 - 544#64) 976) ∗ R) :
    ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      Memory.RW s0.mem x.saltA 32 ∧
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
  have hrw_sv : Memory.RW s0.mem x.saltA 32 :=
    fun a ha => hb_sv.permNoLazy_rw hsep_sv ha
  have hd_sv_stk : DisjointRegions x.saltA 32 (sp0 - 544#64) 976 :=
    hb_sv.disjoint hb_stk (by decide) (by decide) hsep_sv_stk
  exact ⟨hne, hsv_mem, hrw_sv, hd_sv_stk⟩

private theorem strip_read64_aux (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (ProofLib.stripExecOutside keep m).read64 a = m.read64 a := by
  simp only [Memory.read64, ProofLib.strip_read8]

private theorem strip_perm_r_aux (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ((ProofLib.stripExecOutside keep m).perm a).r = (m.perm a).r := by
  dsimp only [ProofLib.stripExecOutside, ProofLib.stripPerm, Memory.perm, Perm.rwx, Option.r]
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩
  · rfl
  · rfl
  · cases keep a <;> cases x <;> rfl

private theorem strip_perm_mapped_aux (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ((ProofLib.stripExecOutside keep m).perm a).mapped = (m.perm a).mapped := by
  dsimp only [ProofLib.stripExecOutside, ProofLib.stripPerm, Memory.perm, Perm.rwx, Option.mapped]
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> cases keep a <;> rfl

private theorem strip_perm_of_protNone_aux {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (h : m.perm a = some Perm.protNone) :
    (ProofLib.stripExecOutside keep m).perm a = some Perm.protNone := by
  dsimp only [ProofLib.stripExecOutside, ProofLib.stripPerm, Memory.perm, Perm.rwx, Perm.protNone] at h ⊢
  rcases hc : m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> simp [hc] at h ⊢
  rcases h with ⟨rfl, rfl, rfl⟩; cases keep a <;> simp

private theorem s2Frame_of_strip_vm_aux {keep : BitVec 64 → Bool} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf' : S2Frame (ProofLib.stripExecOutside keep m₁) (ProofLib.stripExecOutside keep m₂) regs)
    (hperm : ∀ a, m₂.perm a = m₁.perm a) : S2Frame m₁ m₂ regs := by
  refine ⟨?_, ⟨⟨?_, fun a ha => (hperm a).trans ha⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · intro a hr hlf hout
    have h1 := hf'.1 a (by rwa [strip_perm_r_aux]) (by rwa [ProofLib.strip_isLazyFree]) hout
    rwa [ProofLib.strip_read8, ProofLib.strip_read8] at h1
  · intro a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp ha
    have hr1 : (m₁.perm a).r = true := by rw [hp]; rfl
    have hlf2' := (hf'.2.2 a (by rwa [strip_perm_r_aux]) (by rwa [ProofLib.strip_isLazyFree])).2
    rw [ProofLib.strip_isLazyFree] at hlf2'
    exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨(hperm a).trans hp, hlf2'⟩
  · intro a ⟨hm, han⟩
    have h2 := (hf'.2.1.2.1 a ⟨by rwa [strip_perm_mapped_aux], by rwa [ProofLib.strip_isAnon]⟩).2
    rw [ProofLib.strip_isAnon] at h2; exact ⟨by rwa [hperm a], h2⟩
  · intro a hp hout
    have h2 := hf'.2.1.2.2 a (strip_perm_of_protNone_aux hp) hout
    refine ⟨(hperm a).trans hp, fun hlf => ?_⟩
    obtain ⟨hrd, hlf2⟩ := h2.2 (by rwa [ProofLib.strip_isLazyFree])
    rw [ProofLib.strip_read8, ProofLib.strip_read8] at hrd
    rw [ProofLib.strip_isLazyFree] at hlf2; exact ⟨hrd, hlf2⟩
  · intro a hr hlf
    have hlf2 := (hf'.2.2 a (by rwa [strip_perm_r_aux]) (by rwa [ProofLib.strip_isLazyFree])).2
    rw [ProofLib.strip_isLazyFree] at hlf2; exact ⟨by rwa [hperm a], hlf2⟩

private theorem extSaved_setMem_aux {s0 : State} {m m' : Memory} {sp0 : BitVec 64}
    (hs : ExtSaved s0 sp0 m) : ExtSaved (s0.setMem m') sp0 m := by
  rcases hs with ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩
  cases s0; exact ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩

private theorem extSaved_of_setMem_aux {s0 : State} {m m' : Memory} {sp0 : BitVec 64}
    (hs : ExtSaved (s0.setMem m') sp0 m) : ExtSaved s0 sp0 m := by
  rcases hs with ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩
  cases s0; exact ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩

private theorem strip_extSaved_aux (keep : BitVec 64 → Bool) {s0 sf : State} {sp0 : BitVec 64}
    (hs : ExtSaved s0 sp0 sf.mem) :
    ExtSaved (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf).mem := by
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  rcases hs with ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩
  rw [← strip_read64_aux keep sf.mem, ← hsf_mem, ← stripS_readReg64 keep s0]
    at h29 hlr h28 h26 h25 h24 h23 h22 h21 h20 h19
  exact ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩

private theorem unstrip_extCommon_aux {keep : BitVec 64 → Bool} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hc' : ExtCommon (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    ExtCommon s0 sp0 sf := by
  rcases hc' with ⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩
  have hs0_mem : (ProofLib.stripS keep s0).mem = ProofLib.stripExecOutside keep s0.mem := by
    cases s0; rfl
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  rcases hsaved' with ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩
  rw [hsf_mem] at h29 hlr h28 h26 h25 h24 h23 h22 h21 h20 h19
  simp only [strip_read64_aux, stripS_readReg64] at h29 hlr h28 h26 h25 h24 h23 h22 h21 h20 h19
  refine ⟨by simpa [stripS_status] using hstat', by simpa [stripS_sp] using hsp',
    by simpa [stripS_readReg64] using hx19', by simpa [stripS_readReg64] using hx27',
    by simpa [stripS_readReg64] using hx29',
    ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩, ?_⟩
  unfold ExtFrame at hframe' ⊢; rw [hs0_mem, hsf_mem, stripS_readReg64] at hframe'
  exact s2Frame_of_strip_vm_aux hframe' hperm

private theorem unstrip_enfs1Placed [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {x : ExtractGhost} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hs' : ENfs1Placed x (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    ENfs1Placed x s0 sp0 sf := by
  rcases hs' with ⟨hc', hpc', hlr', hx0', hx1', hx2', hx20', hx21', hne', hmem'⟩
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  rw [hsf_mem, strip_readBytes] at hmem'
  exact ⟨unstrip_extCommon_aux hperm hc',
    by simpa [stripS_pc] using hpc', by simpa [stripS_readReg64] using hlr',
    by simpa [stripS_readReg64] using hx0', by simpa [stripS_readReg64] using hx1',
    by simpa [stripS_readReg64] using hx2', by simpa [stripS_readReg64] using hx20',
    by simpa [stripS_readReg64] using hx21', hne', hmem'⟩

private theorem unstrip_ememcpyPlaced [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {C : Crypto} {x : ExtractGhost} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hs' : EMemcpyPlaced C.F x (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    EMemcpyPlaced C.F x s0 sp0 sf := by
  rcases hs' with ⟨hc', hpc', hlr', hx0', hx1', hx2', hx21', hx22', hx25', hhm'⟩
  rw [stripS_hmacSt] at hhm'
  exact ⟨unstrip_extCommon_aux hperm hc',
    by simpa [stripS_pc] using hpc', by simpa [stripS_readReg64] using hlr',
    by simpa [stripS_readReg64] using hx0', by simpa [stripS_readReg64] using hx1',
    by simpa [stripS_readReg64] using hx2', by simpa [stripS_readReg64] using hx21',
    by simpa [stripS_readReg64] using hx22', by simpa [stripS_readReg64] using hx25', hhm'⟩

private theorem unstrip_enfs1LongPlaced [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {x : ExtractGhost} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hs' : ENfs1LongPlaced x (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    ENfs1LongPlaced x s0 sp0 sf := by
  rcases hs' with ⟨hc', hpc', hlr', hx0', hx1', hx2', hx20', hx21', hmem'⟩
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  rw [hsf_mem, strip_readBytes] at hmem'
  exact ⟨unstrip_extCommon_aux hperm hc',
    by simpa [stripS_pc] using hpc', by simpa [stripS_readReg64] using hlr',
    by simpa [stripS_readReg64] using hx0', by simpa [stripS_readReg64] using hx1',
    by simpa [stripS_readReg64] using hx2', by simpa [stripS_readReg64] using hx20',
    by simpa [stripS_readReg64] using hx21', hmem'⟩

private theorem unstrip_ememcpyLongPlaced [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {C : Crypto} {x : ExtractGhost} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hs' : EMemcpyLongPlaced C.F x (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    EMemcpyLongPlaced C.F x s0 sp0 sf := by
  rcases hs' with ⟨hc', hpc', hlr', hx0', hx1', hx2', hx22', hpos', hist', hcnt1', hout', hcnt2'⟩
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  rw [hsf_mem, ProofLib.strip_read8] at hpos'
  rw [hsf_mem, strip_readBytes] at hist' hout'
  rw [hsf_mem, strip_read64_aux] at hcnt1' hcnt2'
  exact ⟨unstrip_extCommon_aux hperm hc',
    by simpa [stripS_pc] using hpc', by simpa [stripS_readReg64] using hlr',
    by simpa [stripS_readReg64] using hx0', by simpa [stripS_readReg64] using hx1',
    by simpa [stripS_readReg64] using hx2', by simpa [stripS_readReg64] using hx22',
    hpos', hist', hcnt1', hout', hcnt2'⟩

private theorem nfs_vm_runsTo_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H] {s : State} {ret keyRegA keyA : BitVec 64}
    {key : List (BitVec 8)}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 114) (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret) (hx1 : s.readReg64 .x1 = keyRegA)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 key.length)
    (hkey_len : key.length ≤ 32) (hkey_pts : (keyRegA ↦ₛ key) = (keyA ↦ₛ key))
    (hkey_mem : s.mem.readBytes keyA key.length = key)
    (hrw_ret : Memory.RW s.mem ret 0x98) (hrw_key : Memory.RW s.mem keyA 32)
    (hrw_stk : Memory.RW s.mem (s.sp - 544#64) 544)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧ s'.status = .Running ∧ CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧ HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) := by
  intro hL
  have hNfs := new_from_slice_placed_ro_vm_ok_at_block_sat
    (callerProg := (blkPC_54).rebase (blkPl_54).base H) (i := 54) C.F hH.memcpy hH.compress256
  let xg : NewFromSliceGhost := { ret := ret, keyA := keyRegA, key := key }
  let P1 : SepProp := memRegion ret 0x98
  let P2 : SepProp := (keyA ↦ₛ key)
  let P3 : SepProp := stackAt s.sp newFromSliceStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 := IsBlock.memRegion ret 0x98
  have hb2 := IsBlock.pointsToBytes keyA key
  have hb3 := IsBlock.memRegion (s.sp - 544#64) 544
  have hkey_le64 : key.length ≤ 64 := by omega
  have hkey_le264 : key.length ≤ 2 ^ 64 := by omega
  have hrw_key' : Memory.RW s.mem keyA key.length :=
    fun a ha => hrw_key a (by simp only [InRegion] at ha ⊢; omega)
  have hd_ret_key' : DisjointRegions ret 0x98 keyA key.length :=
    ⟨hd_ret_key.1, Nat.le_trans hkey_len hd_ret_key.2⟩
  have hd_key_stk' : DisjointRegions keyA key.length (s.sp - 544#64) 544 :=
    ⟨Nat.le_trans hkey_len hd_key_stk.1, hd_key_stk.2⟩
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks hb1 hb2 hb3 trivial ⟨hkey_le264, hkey_mem⟩ trivial
      hrw_ret hrw_key' hrw_stk hd_ret_key' hd_ret_stk hd_key_stk' hkey_le264 (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx2_nat : (s.readReg64 .x2).toNat = key.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpre_sat : s.mem ⊨
      (withLsCodeLoaded lsmpl
        { withVmPreserved (newFromSliceSpec C.F) with
          pre := fun g s0 =>
            (withVmPreserved (newFromSliceSpec C.F)).pre g s0 ∗
              ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }).pre xg s ∗ R := by
    dsimp only [withLsCodeLoaded, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm ((newFromSliceSpec C.F).pre xg s), satisfies_pure_sepConj]
    refine ⟨hcro.2, ?_⟩
    rw [newFromSliceSpec]; dsimp only [xg]
    rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_nat, hkey_le64⟩, by simpa [P, P1, P2, P3, sepConj_assoc] using hsatPR⟩
  have hcall := subroutine_ok_apply_full hNfs xg R hpc hstat hpre_sat
    (by simpa [State.spAligned] using hsp_al)
    (by intro _ _ hp; dsimp only [withLsCodeLoaded, withVmPreserved, newFromSliceSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [withLsCodeLoaded, withVmPreserved, newFromSliceSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [withLsCodeLoaded, withVmPreserved, newFromSliceSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, ⟨⟩⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, newFromSliceSpec, xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨hvm, hpost_sat⟩
  rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  let P1' : SepProp := (ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key []
  have hb1' : IsBlock P1' ret 0x98
      (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) C.F key []) :=
    (IsBlock.pointsTo64 ret 0#64).sepConj (isBlock_hmacCoreAt C.F (ret + 8#64) key [] (by decide))
      rfl (by decide)
  change s'.mem ⊨ ((ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key [] ∗ P2 ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by dsimp only [P1']; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by ac_nf at hpost_1 ⊢
  obtain ⟨hok, hhm⟩ := hb1'.read hpost_1
  have hkey_s' : s'.mem.readBytes keyA key.length = key := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'; exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)] :=
    isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP hpost_1 hpost_2 hpost_3
      hkey_le264 (hkey_s'.trans hkey_mem.symm) hmc.1 hmc.2.2
  exact ⟨s', hsteps, hvm, htr, CallingConventionPreserved.vregs hcc,
    ⟨hpc', hstat', hcc, hok, hhm, hframe⟩, hsteps.codeLoaded hL⟩

private theorem nfs1_vm_runsTo_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksExactBudgetSat C.F H] {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976)
    (hRW_salt : Memory.RW s0.mem (saltPtrOf sp0 x) 32)
    (hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98)
    (hsp_al : (sp0 &&& 15#64) = 0#64) (hs : ENfs1Placed x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (ERet1 extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_some_ne, hsalt_mem⟩
  have hsub_x0 : ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hrun := nfs_vm_runsTo_sat (C := C) (H := H) hcro hpc hstat hx0 hx1 hx2
    (saltSliceOf_length_le x) (pointsToBytes_saltRegOf_eq sp0 x hsalt_some_ne) hsalt_mem
    (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_x0))
    (hframe.rw_of_rw _ _ hRW_salt)
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_544))
    hd_salt_176.symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_544) (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8, hmacSt_saltSliceOf] at hhm
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem := hframe.trans_pair hfr' hsub_x0 hsub_544
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) := by
    rw [hlr, extPlacedFakeB_off_80]
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CallingConventionPreserved.x20 hcs).trans hx20,
    (CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

private theorem nfs1_long_vm_runsTo_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksExactBudgetSat C.F H] {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976)
    (hRW_salt : Memory.RW s0.mem (saltPtrOf sp0 x) 32)
    (hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544)
    (hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98)
    (hsp_al : (sp0 &&& 15#64) = 0#64) (hs : ENfs1LongPlaced x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (ERet1Long extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx20, hx21, hsalt_mem⟩
  have hsub_x0 : ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hlen : (effectiveSalt x.salt).length = 32 := effectiveSalt_length x.salt
  have hrun := nfs_vm_runsTo_sat (C := C) (H := H) hcro hpc hstat hx0 hx1
    (by rw [hx2, hlen]) (by omega) rfl (by rwa [hlen])
    (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_x0))
    (hframe.rw_of_rw _ _ hRW_salt)
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_544))
    hd_salt_176.symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact hd_salt_544) (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem := hframe.trans_pair hfr' hsub_x0 hsub_544
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 80) := by
    rw [hlr, extPlacedFakeB_off_80]
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CallingConventionPreserved.x20 hcs).trans hx20,
    (CallingConventionPreserved.x21 hcs).trans hx21, hok, hhm⟩

/-- Relocatable `subroutine_ok` with `VmPreserved` for
`GenericHkdf<Hmac<Sha256>>::extract` (Block `54`, `32`-B `ikm`) under `withLsCodeRoLoaded lsmpl`
and `[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem extract_placed_vm_ok_cro_sat [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooksExactBudgetSat C.F H] :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
      (withLsCodeRoLoaded lsmpl (extractBudgetSpec C.F)) := by
  let hH := ‹HkdfPlacedHooksExactBudgetSat C.F H›
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cro hsp => ?_
  obtain ⟨hcro, hpre⟩ := extract_withLsCodeRoLoaded hpre_cro
  dsimp only [extractBudgetSpec, withVmPreserved, extractSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hsalt_none, hx3, hx4, hikm_len⟩, hsep⟩
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 (by simpa [State.spAligned] using hsp)
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
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ (memRegion (sp0 - 544#64) 976 ∗ R))) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ R))) := by
    ac_nf at hsep ⊢
  have hRW_out : Memory.RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : Memory.RW s0.mem x.ikmA 32 :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm := by
    have h := (hb_ikm.read hsep_ikm_ret).2; rwa [hikm_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsalt_props := extract_salt_props_976 hb_stk hsep
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
  have hRW_salt : Memory.RW s0.mem (saltPtrOf sp0 x) 32 := by
    cases hsalt : x.salt with
    | none => rw [saltPtrOf, hsalt]; exact rw_stk_sub hRW_stk (sp0 + 144#64) 32 hsub_144
    | some sv => rw [saltPtrOf, hsalt]; exact (hsalt_props sv hsalt).2.2.1
  have hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    cases hsalt : x.salt with
    | none => rw [saltPtrOf, hsalt]; exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
    | some sv => rw [saltPtrOf, hsalt]; exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 _ _ hsub_544
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    cases hsalt : x.salt with
    | none => rw [saltPtrOf, hsalt]; exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
    | some sv => rw [saltPtrOf, hsalt]; exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 _ _ hsub_176
  let H' := noMemsetMemcpyKdfHooks H
  let s0' := ProofLib.stripS keepExt54_114 s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepExt54_114 s0.mem := by cases s0; rfl
  have hrw_strip0 : ∀ {base : BitVec 64} {len : Nat}, s0.mem.RW base len → s0'.mem.RW base len := by
    intro base len hrw a ha; rw [hs0'_mem]; exact strip_permNoLazy_rw (hrw a ha)
  have hp0 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0 (ENfs1Placed x s0 sp0) :=
    lift_runsToE_ext54_114_vm_compress_only (C := C) (H := H) hcro
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg0_placed_runsTo (H := H') hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
          (fun sv hsv => ⟨(hsalt_props sv hsv).1, (hsalt_props sv hsv).2.1, (hsalt_props sv hsv).2.2.2⟩)))
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg0_placed_runsTo (H := H')
          (by simpa [s0', stripS_pc] using hpc) (by simpa [s0', stripS_status] using hrun)
          (by simpa [s0', stripS_sp] using hsp0) (by simpa [s0', stripS_readReg64] using hx1)
          (fun hs => by simpa [s0', stripS_readReg64] using hx2 hs)
          (by simpa [s0', stripS_readReg64] using hx3) (by simpa [s0', stripS_readReg64] using hx4)
          hsp_al (hrw_strip0 hrw_sp0)
          (fun hs => (hsalt_none hs).imp id (fun h0 => by simpa [s0', stripS_readReg64] using h0))
          (fun sv hsv =>
            let ⟨hne, hmem, _, hdisj⟩ := hsalt_props sv hsv
            ⟨hne, by rw [hs0'_mem, strip_readBytes]; exact hmem, hdisj⟩)))
      (fun _ hs => hs.1.1) (fun _ hs => hs.1.1)
      (fun sf hvm hs' => unstrip_enfs1Placed hvm.perm_eq hs')
  have hp1 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0
      (ERet1 extPlacedFakeB C.F x s0 sp0) :=
    hp0.trans_full fun s1 hs1 hkf1 =>
      nfs1_vm_runsTo_sat ⟨cl_of_keepsFrozen hcro.1 hkf1, libsignalRoLoaded_of_keepsFrozen hcro.2 hkf1⟩
        hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs1
  have hp2 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0
      (EMemcpyPlaced C.F x s0 sp0) := by
    refine hp1.trans_full fun s2 hs2 hkf2 => ?_
    have hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem :=
      ⟨cl_of_keepsFrozen hcro.1 hkf2, libsignalRoLoaded_of_keepsFrozen hcro.2 hkf2⟩
    rcases hs2 with ⟨⟨hstat2, hsp2, hx19_2, hx27_2, hx29_2, hsaved2, hframe2⟩,
      hpc2, hx20_2, hx21_2, hok2, hhm2⟩
    let s0_2 : State := s0.setMem s2.mem
    have hs0_2_reg : ∀ r, s0_2.readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    have hRW_stk2 : Memory.RW s0_2.mem (sp0 - 544#64) 976 :=
      hframe2.rw_of_rw (sp0 - 544#64) 976 hRW_stk
    have hsaved_2 : ExtSaved s0_2 sp0 s2.mem := extSaved_setMem_aux hsaved2
    have hs2_re : ERet1 extPlacedFakeB C.F x s0_2 sp0 s2 :=
      ⟨⟨hstat2, hsp2, by rw [hs0_2_reg]; exact hx19_2, by rw [hs0_2_reg]; exact hx27_2, hx29_2,
        hsaved_2, S2Frame.refl s2.mem _⟩, hpc2, hx20_2, hx21_2, hok2, hhm2⟩
    let s2' := ProofLib.stripS keepExt54_114 s2
    let s0_2' := ProofLib.stripS keepExt54_114 s0_2
    have hs2'_mem : s2'.mem = ProofLib.stripExecOutside keepExt54_114 s2.mem := by cases s2; rfl
    have hs0_2'_mem : s0_2'.mem = ProofLib.stripExecOutside keepExt54_114 s2.mem := by cases s0; rfl
    have hrw_strip2 : ∀ {base : BitVec 64} {len : Nat}, s2.mem.RW base len → s0_2'.mem.RW base len := by
      intro base len hrw a ha; rw [hs0_2'_mem]; exact strip_permNoLazy_rw (hrw a ha)
    have hs2'_re : ERet1 extPlacedFakeB C.F x s0_2' sp0 s2' :=
      ⟨⟨by simpa [s2', stripS_status] using hstat2, by simpa [s2', stripS_sp] using hsp2,
        by simpa [s2', s0_2', stripS_readReg64, hs0_2_reg] using hx19_2,
        by simpa [s2', s0_2', stripS_readReg64, hs0_2_reg] using hx27_2,
        by simpa [s2', stripS_readReg64] using hx29_2,
        strip_extSaved_aux keepExt54_114 hsaved_2,
        by unfold ExtFrame; rw [hs0_2'_mem, hs2'_mem]; exact S2Frame.refl _ _⟩,
       by simpa [s2', stripS_pc] using hpc2, by simpa [s2', stripS_readReg64] using hx20_2,
       by simpa [s2', stripS_readReg64] using hx21_2,
       by rw [hs2'_mem, strip_read64_aux]; exact hok2,
       by rw [← stripS_hmacSt keepExt54_114] at hhm2; exact hhm2⟩
    have hSeg1a_re := lift_runsToE_ext54_114_vm_compress_only (C := C) (H := H) hcro2
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1a_placed_runsTo (H := H') hRW_stk2 hsp_al hs2_re))
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1a_placed_runsTo (H := H') (hrw_strip2 hRW_stk2) hsp_al hs2'_re))
      (fun _ hs => hs.1.1) (fun _ hs => hs.1.1)
      (fun sf hvm hs' => unstrip_ememcpyPlaced (by simpa [s0_2] using hvm.perm_eq) hs')
    refine hSeg1a_re.mono fun s3 hs3 => ?_
    rcases hs3 with ⟨⟨hstat3, hsp3, hx19_3, hx27_3, hx29_3, hsaved3, hframe3_re⟩, rest3⟩
    rw [hs0_2_reg] at hx19_3 hx27_3
    unfold ExtFrame at hframe2 hframe3_re
    rw [show s0_2.mem = s2.mem from by cases s0; rfl, hs0_2_reg] at hframe3_re
    exact ⟨⟨hstat3, hsp3, hx19_3, hx27_3, hx29_3, extSaved_of_setMem_aux hsaved3,
      hframe2.trans hframe3_re⟩, rest3⟩
  have hp3 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0
      (EC88 extPlacedFakeB C.F x s0 sp0) :=
    hp2.trans_full fun s3 hs3 _ =>
      seg1b_hmc (C := C) hH.memcpy hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs3
  have hpA : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0 (EFinPlaced C.F x s0 sp0) := by
    refine hp3.trans_full fun s4 hs4 hkf4 => ?_
    have hcro4 : LibsignalCodeRoLoaded lsmpl s4.mem :=
      ⟨cl_of_keepsFrozen hcro.1 hkf4, libsignalRoLoaded_of_keepsFrozen hcro.2 hkf4⟩
    rcases hs4 with ⟨⟨hstat4, hsp4, hx19_4, hx27_4, hx29_4, hsaved4, hframe4⟩, hpc4, hx22_4, hhm4⟩
    let s0_4 : State := s0.setMem s4.mem
    have hs0_4_reg : ∀ r, s0_4.readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    have hRW_stk4 : Memory.RW s0_4.mem (sp0 - 544#64) 976 :=
      hframe4.rw_of_rw (sp0 - 544#64) 976 hRW_stk
    have hsaved_4 : ExtSaved s0_4 sp0 s4.mem := extSaved_setMem_aux hsaved4
    have hs4_re : EC88 extPlacedFakeB C.F x s0_4 sp0 s4 :=
      ⟨⟨hstat4, hsp4, by rw [hs0_4_reg]; exact hx19_4, by rw [hs0_4_reg]; exact hx27_4, hx29_4,
        hsaved_4, S2Frame.refl s4.mem _⟩, hpc4, hx22_4, hhm4⟩
    let s4' := ProofLib.stripS keepExt54_114 s4
    let s0_4' := ProofLib.stripS keepExt54_114 s0_4
    have hs4'_mem : s4'.mem = ProofLib.stripExecOutside keepExt54_114 s4.mem := by cases s4; rfl
    have hs0_4'_mem : s0_4'.mem = ProofLib.stripExecOutside keepExt54_114 s4.mem := by cases s0; rfl
    have hrw_strip4 : ∀ {base : BitVec 64} {len : Nat}, s4.mem.RW base len → s0_4'.mem.RW base len := by
      intro base len hrw a ha; rw [hs0_4'_mem]; exact strip_permNoLazy_rw (hrw a ha)
    have hs4'_re : EC88 extPlacedFakeB C.F x s0_4' sp0 s4' :=
      ⟨⟨by simpa [s4', stripS_status] using hstat4, by simpa [s4', stripS_sp] using hsp4,
        by simpa [s4', s0_4', stripS_readReg64, hs0_4_reg] using hx19_4,
        by simpa [s4', s0_4', stripS_readReg64, hs0_4_reg] using hx27_4,
        by simpa [s4', stripS_readReg64] using hx29_4,
        strip_extSaved_aux keepExt54_114 hsaved_4,
        by unfold ExtFrame; rw [hs0_4'_mem, hs4'_mem]; exact S2Frame.refl _ _⟩,
       by simpa [s4', stripS_pc] using hpc4, by simpa [s4', stripS_readReg64] using hx22_4,
       by rw [← stripS_hmacSt keepExt54_114] at hhm4; exact hhm4⟩
    have hSeg1c_re := lift_runsToE_ext54_114_vm_compress_only (C := C) (H := H) hcro4
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1c_placed_runsTo (H := H') hRW_stk4 hsp_al hs4_re))
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1c_placed_runsTo (H := H') (hrw_strip4 hRW_stk4) hsp_al hs4'_re))
      (fun _ hs => hs.1.1) (fun _ hs => hs.1.1)
      (fun sf hvm hs' => unstrip_efinPlaced (by simpa [s0_4] using hvm.perm_eq) hs')
    refine hSeg1c_re.mono fun s5 hs5 => ?_
    rcases hs5 with ⟨⟨hstat5, hsp5, hx19_5, hx27_5, hx29_5, hsaved5, hframe5_re⟩, rest5⟩
    rw [hs0_4_reg] at hx19_5 hx27_5
    unfold ExtFrame at hframe4 hframe5_re
    rw [show s0_4.mem = s4.mem from by cases s0; rfl, hs0_4_reg] at hframe5_re
    exact ⟨⟨hstat5, hsp5, hx19_5, hx27_5, hx29_5, extSaved_of_setMem_aux hsaved5,
      hframe4.trans hframe5_re⟩, rest5⟩
  have hpAB : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0
      (ERetFin extPlacedFakeB C.F x s0 sp0) :=
    hpA.trans_full fun s1 hs1 hkf1 =>
      fin_short_vm_runsTo_sat (cl_of_keepsFrozen hcro.1 hkf1) hRW_stk hikm_len hsp_al hs1
  have hpAll : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0 (EPost C.F x s0 sp0) :=
    hpAB.trans_full fun s2 hs2 hkf2 =>
      post_fin_vm_runsTo_sat
        ⟨cl_of_keepsFrozen hcro.1 hkf2, libsignalRoLoaded_of_keepsFrozen hcro.2 hkf2⟩
        hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs2
  intro hL0
  obtain ⟨sf, hsteps, hvm, htr_eq, hv_eq, hpost, _⟩ := hpAll hL0
  refine ⟨sf, hsteps, Or.inl ?_⟩
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee ⟨htr_eq, hv_eq⟩⟩
  dsimp only [withLsCodeRoLoaded, extractBudgetSpec, withVmPreserved, extractSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr_eq, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]; exact length_hmacWith C.F _ _
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
  rw [hsp_m976]; dsimp only [R_rest] at hpost_sep; ac_nf at hpost_sep ⊢

/-- `subroutine_ok` for `HandshakeDeriveBudget.pqxdhHkdfExtractNonePlacedSpec` on Block `54`
(`salt = None`, `160` / `192` / `224`-B `ikm`, carrying `VmPreserved` in `post`) under
`[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem pqxdhHkdfExtractNone_placed_ok_block54_sat [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactBudgetSat C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 54)
      (pqxdhHkdfExtractNonePlacedSpec P lsmpl) := by
  let hH := ‹HkdfPlacedHooksExactBudgetSat C.F H›
  refine subroutine_ok_intro fun ⟨ret, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhHkdfExtractNonePlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractNonePlacedSpec] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  dsimp only [stackAt, extractStack, newFromSliceStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hx0, hx1, hx3, hx4, hsp_eq, hikm_len⟩, hsep⟩
  subst hsp_eq
  have hcro : LibsignalCodeRoLoaded lsmpl s0.mem := ⟨hF0.code, hF0.ro⟩
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 (by simpa [State.spAligned] using hsp)
  let x : ExtractGhost := ⟨ret, 0#64, none, ikmA, bytesToBv8 ikm⟩
  have hikm_bv_len : x.ikm.length = ikm.length := by dsimp [x]; exact bytesToBv8_length ikm
  have hikm_cases : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224 := by
    rwa [hikm_bv_len]
  have hikm_pos : 0 < x.ikm.length := by omega
  have hikm_le : x.ikm.length ≤ 2 ^ 64 := by omega
  have hx4' : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length := by rw [hikm_bv_len]; exact hx4
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
  have hRW_out : Memory.RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : Memory.RW s0.mem x.ikmA x.ikm.length :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm :=
    (hb_ikm.read hsep_ikm_ret).2
  have hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret hikm_pos (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk hikm_pos (by decide) hsep_ikm_stk
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stk_sub hRW_stk sp0 432 hsub_432
  have hRW_salt : Memory.RW s0.mem (saltPtrOf sp0 x) 32 := by
    dsimp [x, saltPtrOf]; exact rw_stk_sub hRW_stk _ _ hsub_144
  have hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    dsimp [x, saltPtrOf]; exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    dsimp [x, saltPtrOf]; exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
  let H' := noMemsetMemcpyKdfHooks H
  let s0' := ProofLib.stripS keepExt54_114 s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepExt54_114 s0.mem := by cases s0; rfl
  have hrw_strip0 : ∀ {base : BitVec 64} {len : Nat}, s0.mem.RW base len → s0'.mem.RW base len := by
    intro base len hrw a ha; rw [hs0'_mem]; exact strip_permNoLazy_rw (hrw a ha)
  have hhc256 := noMemsetMemcpyKdfHooks_compress256 (C := C) (H := H)
  have hp0 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0 (ENfs1LongPlaced x s0 sp0) :=
    lift_runsToE_ext54_114_vm_compress_only (C := C) (H := H) hcro
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg0_long_placed_runsTo (H := H') hpc hrun hsp0 hx1 hx3 hx4' hsp_al hrw_sp0 rfl rfl))
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg0_long_placed_runsTo (H := H')
          ((stripS_pc keepExt54_114 s0).trans hpc)
          (by simpa [s0', stripS_status] using hrun)
          (by simpa [s0', stripS_sp] using hsp0)
          (by simpa [s0', stripS_readReg64] using hx1)
          (by simpa [s0', stripS_readReg64] using hx3)
          (by simpa [s0', stripS_readReg64] using hx4')
          hsp_al (hrw_strip0 hrw_sp0) rfl rfl))
      (fun _ hs => hs.1.1) (fun _ hs => hs.1.1)
      (fun sf hvm hs' => unstrip_enfs1LongPlaced hvm.perm_eq hs')
  have hp1 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0
      (ERet1Long extPlacedFakeB C.F x s0 sp0) :=
    hp0.trans_full fun s1 hs1 hkf1 =>
      nfs1_long_vm_runsTo_sat ⟨cl_of_keepsFrozen hcro.1 hkf1, libsignalRoLoaded_of_keepsFrozen hcro.2 hkf1⟩
        hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs1
  have hp2 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0
      (EMemcpyLongPlaced C.F x s0 sp0) := by
    refine hp1.trans_full fun s2 hs2 hkf2 => ?_
    have hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem :=
      ⟨cl_of_keepsFrozen hcro.1 hkf2, libsignalRoLoaded_of_keepsFrozen hcro.2 hkf2⟩
    rcases hs2 with ⟨⟨hstat2, hsp2, hx19_2, hx27_2, hx29_2, hsaved2, hframe2⟩,
      hpc2, hx20_2, hx21_2, hok2, hhm2⟩
    let s0_2 : State := s0.setMem s2.mem
    have hs0_2_reg : ∀ r, s0_2.readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    have hRW_stk2 : Memory.RW s0_2.mem (sp0 - 544#64) 976 :=
      hframe2.rw_of_rw (sp0 - 544#64) 976 hRW_stk
    have hRW_ikm2 : Memory.RW s0_2.mem x.ikmA x.ikm.length :=
      hframe2.rw_of_rw x.ikmA x.ikm.length hRW_ikm
    have hikm_mem2 : s0_2.mem.readBytes x.ikmA x.ikm.length = x.ikm := by
      change s2.mem.readBytes x.ikmA x.ikm.length = x.ikm
      rw [hframe2.readBytes_eq hRW_ikm ?_ hikm_le]; · exact hikm_mem0
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl; exacts [hd_ikm_out.symm, hd_ikm_stk.symm]
    have hd_ikm_out2 : DisjointRegions x.ikmA x.ikm.length (s0_2.readReg64 .x0) 0xb0 := by
      rwa [hs0_2_reg]
    have hsaved_2 : ExtSaved s0_2 sp0 s2.mem := extSaved_setMem_aux hsaved2
    have hs2_re : ERet1Long extPlacedFakeB C.F x s0_2 sp0 s2 :=
      ⟨⟨hstat2, hsp2, by rw [hs0_2_reg]; exact hx19_2, by rw [hs0_2_reg]; exact hx27_2, hx29_2,
        hsaved_2, S2Frame.refl s2.mem _⟩, hpc2, hx20_2, hx21_2, hok2, hhm2⟩
    let s2' := ProofLib.stripS keepExt54_114 s2
    let s0_2' := ProofLib.stripS keepExt54_114 s0_2
    have hs2'_mem : s2'.mem = ProofLib.stripExecOutside keepExt54_114 s2.mem := by cases s2; rfl
    have hs0_2'_mem : s0_2'.mem = ProofLib.stripExecOutside keepExt54_114 s2.mem := by cases s0; rfl
    have hrw_strip2 : ∀ {base : BitVec 64} {len : Nat}, s2.mem.RW base len → s0_2'.mem.RW base len := by
      intro base len hrw a ha; rw [hs0_2'_mem]; exact strip_permNoLazy_rw (hrw a ha)
    have hs2'_re : ERet1Long extPlacedFakeB C.F x s0_2' sp0 s2' :=
      ⟨⟨by simpa [s2', stripS_status] using hstat2, by simpa [s2', stripS_sp] using hsp2,
        by simpa [s2', s0_2', stripS_readReg64, hs0_2_reg] using hx19_2,
        by simpa [s2', s0_2', stripS_readReg64, hs0_2_reg] using hx27_2,
        by simpa [s2', stripS_readReg64] using hx29_2,
        strip_extSaved_aux keepExt54_114 hsaved_2,
        by unfold ExtFrame; rw [hs0_2'_mem, hs2'_mem]; exact S2Frame.refl _ _⟩,
       by simpa [s2', stripS_pc] using hpc2, by simpa [s2', stripS_readReg64] using hx20_2,
       by simpa [s2', stripS_readReg64] using hx21_2,
       by rw [hs2'_mem, strip_read64_aux]; exact hok2,
       by rw [← stripS_hmacSt keepExt54_114] at hhm2; exact hhm2⟩
    have hRuns20 := (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1a_long_placed_runsTo (H := H') hRW_stk2 hikm_cases hsp_al hs2_re)).trans fun sc hsc =>
      CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1b1_long_hc256 (C := C) hhc256 hRW_stk2 hRW_ikm2 hikm_cases hikm_mem2
          hd_ikm_stk hd_ikm_out2 hsp_al hsc)
    have hRuns2' := (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1a_long_placed_runsTo (H := H') (hrw_strip2 hRW_stk2) hikm_cases hsp_al hs2'_re)).trans
        fun sc hsc =>
      CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1b1_long_hc256 (C := C) hhc256 (hrw_strip2 hRW_stk2) (hrw_strip2 hRW_ikm2) hikm_cases
          (by rw [hs0_2'_mem, strip_readBytes]; exact hikm_mem2)
          hd_ikm_stk (by simpa [s0_2', stripS_readReg64] using hd_ikm_out2) hsp_al hsc)
    have hSeg1ab_re := lift_runsToE_ext54_114_vm_compress_only (C := C) (H := H) hcro2
      hRuns20 hRuns2' (fun _ hs => hs.1.1) (fun _ hs => hs.1.1)
      (fun sf hvm hs' => unstrip_ememcpyLongPlaced (by simpa [s0_2] using hvm.perm_eq) hs')
    refine hSeg1ab_re.mono fun s3 hs3 => ?_
    rcases hs3 with ⟨⟨hstat3, hsp3, hx19_3, hx27_3, hx29_3, hsaved3, hframe3_re⟩, rest3⟩
    rw [hs0_2_reg] at hx19_3 hx27_3
    unfold ExtFrame at hframe2 hframe3_re
    rw [show s0_2.mem = s2.mem from by cases s0; rfl, hs0_2_reg] at hframe3_re
    exact ⟨⟨hstat3, hsp3, hx19_3, hx27_3, hx29_3, extSaved_of_setMem_aux hsaved3,
      hframe2.trans hframe3_re⟩, rest3⟩
  have hp3 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0
      (EC88Long extPlacedFakeB C.F x s0 sp0) :=
    hp2.trans_full fun s3 hs3 _ =>
      seg1b2_long_hmc (C := C) hH.memcpy hRW_stk hRW_ikm hikm_cases hikm_mem0
        hd_ikm_stk hd_ikm_out hsp_al hs3
  have hpA : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0 (EFinLongPlaced C.F x s0 sp0) := by
    refine hp3.trans_full fun s4 hs4 hkf4 => ?_
    have hcro4 : LibsignalCodeRoLoaded lsmpl s4.mem :=
      ⟨cl_of_keepsFrozen hcro.1 hkf4, libsignalRoLoaded_of_keepsFrozen hcro.2 hkf4⟩
    rcases hs4 with ⟨⟨hstat4, hsp4, hx19_4, hx27_4, hx29_4, hsaved4, hframe4⟩, hpc4, hx22_4, hhm4⟩
    let s0_4 : State := s0.setMem s4.mem
    have hs0_4_reg : ∀ r, s0_4.readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    have hRW_stk4 : Memory.RW s0_4.mem (sp0 - 544#64) 976 :=
      hframe4.rw_of_rw (sp0 - 544#64) 976 hRW_stk
    have hsaved_4 : ExtSaved s0_4 sp0 s4.mem := extSaved_setMem_aux hsaved4
    have hs4_re : EC88Long extPlacedFakeB C.F x s0_4 sp0 s4 :=
      ⟨⟨hstat4, hsp4, by rw [hs0_4_reg]; exact hx19_4, by rw [hs0_4_reg]; exact hx27_4, hx29_4,
        hsaved_4, S2Frame.refl s4.mem _⟩, hpc4, hx22_4, hhm4⟩
    let s4' := ProofLib.stripS keepExt54_114 s4
    let s0_4' := ProofLib.stripS keepExt54_114 s0_4
    have hs4'_mem : s4'.mem = ProofLib.stripExecOutside keepExt54_114 s4.mem := by cases s4; rfl
    have hs0_4'_mem : s0_4'.mem = ProofLib.stripExecOutside keepExt54_114 s4.mem := by cases s0; rfl
    have hrw_strip4 : ∀ {base : BitVec 64} {len : Nat}, s4.mem.RW base len → s0_4'.mem.RW base len := by
      intro base len hrw a ha; rw [hs0_4'_mem]; exact strip_permNoLazy_rw (hrw a ha)
    have hs4'_re : EC88Long extPlacedFakeB C.F x s0_4' sp0 s4' :=
      ⟨⟨by simpa [s4', stripS_status] using hstat4, by simpa [s4', stripS_sp] using hsp4,
        by simpa [s4', s0_4', stripS_readReg64, hs0_4_reg] using hx19_4,
        by simpa [s4', s0_4', stripS_readReg64, hs0_4_reg] using hx27_4,
        by simpa [s4', stripS_readReg64] using hx29_4,
        strip_extSaved_aux keepExt54_114 hsaved_4,
        by unfold ExtFrame; rw [hs0_4'_mem, hs4'_mem]; exact S2Frame.refl _ _⟩,
       by simpa [s4', stripS_pc] using hpc4, by simpa [s4', stripS_readReg64] using hx22_4,
       by rw [← stripS_hmacStGen keepExt54_114] at hhm4; exact hhm4⟩
    have hSeg1c_re := lift_runsToE_ext54_114_vm_compress_only (C := C) (H := H) hcro4
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1c_long_placed_runsTo (H := H') hRW_stk4 hsp_al hs4_re))
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg1c_long_placed_runsTo (H := H') (hrw_strip4 hRW_stk4) hsp_al hs4'_re))
      (fun _ hs => hs.1.1) (fun _ hs => hs.1.1)
      (fun sf hvm hs' => unstrip_efinLongPlaced (by simpa [s0_4] using hvm.perm_eq) hs')
    refine hSeg1c_re.mono fun s5 hs5 => ?_
    rcases hs5 with ⟨⟨hstat5, hsp5, hx19_5, hx27_5, hx29_5, hsaved5, hframe5_re⟩, rest5⟩
    rw [hs0_4_reg] at hx19_5 hx27_5
    unfold ExtFrame at hframe4 hframe5_re
    rw [show s0_4.mem = s4.mem from by cases s0; rfl, hs0_4_reg] at hframe5_re
    exact ⟨⟨hstat5, hsp5, hx19_5, hx27_5, hx29_5, extSaved_of_setMem_aux hsaved5,
      hframe4.trans hframe5_re⟩, rest5⟩
  have hpAB : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0
      (ERetFin extPlacedFakeB C.F x s0 sp0) :=
    hpA.trans_full fun s1 hs1 hkf1 =>
      fin_long_vm_runsTo_sat (cl_of_keepsFrozen hcro.1 hkf1) hRW_stk hikm_cases hsp_al hs1
  have hpAll : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s0 (EPost C.F x s0 sp0) :=
    hpAB.trans_full fun s2 hs2 hkf2 =>
      post_fin_vm_runsTo_sat
        ⟨cl_of_keepsFrozen hcro.1 hkf2, libsignalRoLoaded_of_keepsFrozen hcro.2 hkf2⟩
        hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs2
  intro hL0
  obtain ⟨sf, hsteps, hvm, htr_eq, hv_eq, hpost, _⟩ := hpAll hL0
  refine ⟨sf, hsteps, Or.inl ?_⟩
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee ⟨htr_eq, hv_eq⟩⟩
  dsimp only [pqxdhHkdfExtractNonePlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractNonePlacedSpec]
  rw [stackAt_alloc_extract s0.sp]
  dsimp only [stackAt, extractStack, newFromSliceStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr_eq, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P none ikm) := by
    dsimp [x, ExtractGhost.prk]; exact (bytesToBv8_hkdfExtractRef_none hP ikm).symm
  have hprk_ref_len : (hkdfExtractRef P none ikm).length = 32 := hkdfExtractRef_length P none ikm
  have hprk_len : (x.prk C.F).length = 32 := by rw [hprk_eq, bytesToBv8_length, hprk_ref_len]
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
  rw [hsp_m976]; dsimp only [R_rest] at hpost_sep; ac_nf at hpost_sep ⊢

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxSat
