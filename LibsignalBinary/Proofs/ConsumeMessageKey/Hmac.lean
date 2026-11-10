/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.Placed.BridgeReloc

/-!
# Refinement of `crypto::hmac_sha256`

Proves that `libsignal_protocol::crypto::hmac_sha256` (`0x20b88`, Block 73) with
`<Hmac<Sha256> as KeyInit>::new_from_slice` (`0x2b3b0`, Block 114) satisfies `hmacSpec F`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- `libsignal_protocol::crypto::hmac_sha256` satisfies `HmacOk`. -/
theorem hmac_sha256_ok (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) (himg : Obj.Loads libsignalSessionImage img) :
    HmacOk img F alloc := by
  exact CryptoHmacSha256.hmac_sha256_ok' img F alloc himg

namespace CryptoHmacSha256

open CryptoVerification.LibsignalHmac CryptoVerification.LibsignalAesCbc

set_option maxRecDepth 2000000 in
/-- `lsSha256IVAddr` holds the 32-byte SHA-256 initial state under `LibsignalRoLoaded`. -/
theorem rodata_placed_sha256IV [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) :
    m.RO lsSha256IVAddr 32 ∧ m.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV := by
  have h := lsro_read_chk hro (sym := lsSha256IVSym) (bs := shaStateBytes sha256IV)
    (by decide +kernel)
  have haddr : lsSha256IVAddr = lsmpl.ρ lsSha256IVSym :=
    ls_resolve_data (tgt := lsSha256IVSym) (by decide)
  rwa [← haddr, shaStateBytes_length] at h

/-- Relocatable `hmac_sha256` specification under `LibsignalRoLoaded`. -/
def hmacPlacedSpec [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) : Spec HmacGhost where
  pre := fun (out, ka, key, ia, inp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = ka ∧ (s.readReg64 .x2).toNat = key.length ∧
      s.readReg64 .x3 = ia ∧ (s.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
      inp.length = 1 ∧ LibsignalRoLoaded lsmpl s.mem⌝ ∗
    memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s.sp 2048
  post := fun (out, ka, key, ia, inp) s0 sf =>
    ⌜sf.trace = s0.trace ∧ LibsignalRoLoaded lsmpl sf.mem⌝ ∗
    (out ↦ₛ hmacWith F key inp) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s0.sp 2048

theorem hmac_sha256_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : H lsMemcpySym = some hookMemcpy)
    (h_ms : H lsMemsetSym = some hookMemset)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl (hmacPlacedSpec F)) := by
  have h_mc' : H lsMemcpySym = some memcpyHook := hookMemcpy_eq_memcpyHook ▸ h_mc
  have h_ms' : H lsMemsetSym = some memsetHook := hookMemset_eq_memsetHook ▸ h_ms
  refine subroutine_ok_intro fun ⟨out, ka, key, ia, inp⟩ R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre
  rw [hmacPlacedSpec] at hpre
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hx3, hx4_nat, hkey_len, hinp_len, hro⟩, hsep⟩
  rcases inp with _ | ⟨byte, _ | _⟩ <;> try { simp at hinp_len }
  have hx2 : s0.readReg64 .x2 = 32#64 := by
    apply BitVec.eq_of_toNat_eq; simp [hx2_nat, hkey_len]
  have hx4 : s0.readReg64 .x4 = 1#64 := by
    apply BitVec.eq_of_toNat_eq; simp at hx4_nat; simp [hx4_nat]
  have hsp_split : stackAt s0.sp 2048 = memRegion (s0.sp - 2048#64) 1024 ∗ memRegion (s0.sp - 1024#64) 1024 :=
    stackAt_split_bottom s0.sp 1024 1024 (by decide)
  rw [hsp_split] at hsep
  have hb_out := IsBlock.memRegion out 32
  have hb_key := IsBlock.pointsToBytes_len (a := ka) hkey_len
  have hb_inp := IsBlock.pointsToBytes_len (a := ia) (rfl : [byte].length = 1)
  have hb_stk := IsBlock.memRegion (s0.sp - 1024#64) 1024
  have hsep_key : s0.mem ⊨ (ka ↦ₛ key) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_inp : s0.mem ⊨ (ia ↦ₛ [byte]) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_out : s0.mem ⊨ memRegion out 32 ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 1024#64) 1024 ∗
      (memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R) := by
    ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes ka 32 = key := by
    have h := (hb_key.read hsep_key).2
    rwa [hkey_len] at h
  have hinp_eq : s0.mem.readBytes ia 1 = [byte] :=
    (hb_inp.read hsep_inp).2
  have hrw_out : RW s0.mem out 32 :=
    fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : RW s0.mem (s0.sp - 1024#64) 1024 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hread_inp : s0.mem.Readable ia 1 :=
    Memory.RW.readable (fun a ha => hb_inp.permNoLazy_rw hsep_inp ha)
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hpre_hmac : HmacPlacedPre F key [byte] s0 := {
    pc_eq := hpc
    status := hrun
    sp_aligned := by simpa [State.spAligned] using hsp
    x2_eq := hx2
    x4_eq := hx4
    key_len := hkey_len
    inp_len := rfl
    key_eq := by rw [hx1]; exact hkey_eq
    inp_eq := by rw [hx3]; exact hinp_eq
    iv_eq := hiv_eq
    read_iv := hread_iv
    read_inp := by rw [hx3]; exact hread_inp
    rw_out := by rw [hx0]; exact hrw_out
    rw_stack := hrw_stk
    disj_iv_stack := disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
    disj_out_stack := by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
    disj_key_stack := by rw [hx1]; exact hb_key.disjoint hb_stk (by decide) (by decide) hsep_key
    disj_inp_stack := by rw [hx3]; exact hb_inp.disjoint hb_stk (by simp) (by decide) hsep_inp
  }
  refine (hmac_placed_runsTo h_mc' h_ms' h_c256 hcl hpre_hmac).to_reaches_pc fun sf h5 hkf hsym htr hvregs => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  dsimp only [withLsCodeLoaded, hmacPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨htr, libsignalRoLoaded_of_keepsFrozen hro hkf⟩, ?_⟩
  rw [hsp_split]
  have hb_out' := IsBlock.pointsToBytes_len (a := out) (length_hmacWith F key [byte])
  rw [hx0] at hout_sf hframe_sf
  have hpost_sep : sf.mem ⊨ (out ↦ₛ hmacWith F key [byte]) ∗ (memRegion (s0.sp - 1024#64) 1024 ∗
      ((ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗ memRegion (s0.sp - 2048#64) 1024 ∗ R)) :=
    Frame.update_two_blocks hb_out hb_out' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial
  ac_nf at hpost_sep ⊢

theorem hmac_sha256_placed_ro_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : H lsMemcpySym = some hookMemcpy)
    (h_ms : H lsMemsetSym = some hookMemset)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) := by
  refine subroutine_ok_mono (hmac_sha256_placed_ok F h_mc h_ms h_c256)
    (fun ⟨out, ka, key, ia, inp⟩ R s0 hp => ?_)
    (fun ⟨out, ka, key, ia, inp⟩ R s0 sf hq => ?_)
  · have ⟨hcl, hp'⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsCodeLoaded, hmacPlacedSpec, hmacSpec] at hp' ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp' ⊢
    rcases hp' with ⟨hro, hp''⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp''
    rcases hp'' with ⟨hpure, hsep⟩
    refine ⟨hcl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpure.1, hpure.2.1, hpure.2.2.1, hpure.2.2.2.1, hpure.2.2.2.2.1,
      hpure.2.2.2.2.2.1, hpure.2.2.2.2.2.2, hro⟩, hsep⟩
  · dsimp only [withLsCodeLoaded, hmacPlacedSpec, hmacSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    exact ⟨hq.1.1, hq.2⟩

end CryptoHmacSha256

theorem hmac_sha256_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : H CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoHmacSha256.lsCompress256Sym = some (LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl (CryptoHmacSha256.hmacPlacedSpec F)) :=
  CryptoHmacSha256.hmac_sha256_placed_ok F h_mc h_ms h_c256

theorem hmac_sha256_placed_ro_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : H CryptoHmacSha256.lsMemcpySym = some hookMemcpy)
    (h_ms : H CryptoHmacSha256.lsMemsetSym = some hookMemset)
    (h_c256 : H CryptoHmacSha256.lsCompress256Sym = some (LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) :=
  CryptoHmacSha256.hmac_sha256_placed_ro_ok F h_mc h_ms h_c256

end CryptoVerification.LibsignalSession
