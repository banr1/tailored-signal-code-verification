/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon

/-!
# `HookSat`-Backed `crypto::hmac_sha256` Contract (Block 73)

Proves placed `hmac_sha256` contracts (`hmac_sha256_placed_ok_sat` and
`hmac_sha256_placed_ro_ok_sat`) under `HookSat H lsMemsetSym sessionMemsetRegionSpec`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState hmacWith sha256IV)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
   blkPC_73 blkPl_73 extract_withLsCodeLoaded libsignalRoLoaded_of_keepsFrozen
   lsProg_73 lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession (hmacSpec)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame
   HmacPlacedPre HmacSaved RW RunsTo StateH1mPlaced StateH1pPlaced StateH2Placed
   disjointRegions_of_ro_rw hmacPlacedSpec hsp hsp_align innerState
   length_hmacWith lsCompress256Sym lsMemcpySym lsMemsetSym lsSha256IVAddr outerState
   read64_writeBytes_replicate_off_disjoint read64_writeBytes_replicate_zero_off
   readBytes_writeBytes_replicate_off_disjoint rodata_placed_sha256IV
   seg1a_placed_runsTo seg2_placed_runsTo seg3_placed_runsTo
   seg4_placed_runsTo toLEBytes_8_read64_writeBytes_146_62)
open CryptoVerification.LibsignalTripleRatchet (sessionMemsetRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (AgreesOn)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
  (hmacSaved_of_agreesOn placed_memset_step_sat s2Frame_of_hmacFrame
   s2Frame_readBytes_eq_of_readable s2Frame_readable_of_readable)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlockExact
  (seg0_placed_runsTo_exact seg1b1_placed_runsTo_exact)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26)

/-! ## `S2Frame` Cut Predicates -/

public structure HmacCommonSat (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x29_eq : s.readReg64 .x29 = hsp s₀ + 384#64
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  saved  : HmacSaved s₀ (hsp s₀) s.mem
  frame  : S2Frame s₀.mem s.mem [(s₀.sp - 1024#64, 1024)]

public structure StateH2PlacedSat [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = (blkPl_73).base + 388#64
  common : HmacCommonSat s₀ s
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq : s.readReg64 .x23 = 128#64
  x24_eq : s.readReg64 .x24 = 1#64
  x25_eq : s.readReg64 .x25 = 1#64
  x26_eq : s.readReg64 .x26 = 62#64
  m144   : toLEBytes 8 (s.mem.read64 (hsp s₀ + 144#64)) = [byte, 0x80#8, 0, 0, 0, 0, 0, 0]
  m152   : s.mem.read64 (hsp s₀ + 152#64) = 0#64
  m160   : s.mem.read64 (hsp s₀ + 160#64) = 0#64
  m168   : s.mem.read64 (hsp s₀ + 168#64) = 0#64
  m176   : s.mem.read64 (hsp s₀ + 176#64) = 0#64
  m184   : s.mem.read64 (hsp s₀ + 184#64) = 0#64
  m192   : s.mem.read64 (hsp s₀ + 192#64) = 0#64
  ist_eq : s.mem.readBytes (hsp s₀ + 208#64) 32 = shaStateBytes (innerState F key)
  ibl_eq : s.mem.read64 (hsp s₀ + 240#64) = 1#64
  ost_eq : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (hsp s₀ + 280#64) = 1#64

public structure StateH5Sat (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq       : s.pc = s₀.readReg64 .lr
  status      : s.status = .Running
  calleeSaved : CalleeSaved s₀ s
  out_eq      : s.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key [byte]
  frame       : S2Frame s₀.mem s.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 1024#64, 1024)]

/-! ## `HookSat` `memset` Step and `hmac_placed_runsTo_sat` -/

public theorem seg1b2_placed_runsTo_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH1pPlaced F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH2PlacedSat F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26,
    hm144_0, hm144_1, hist, hibl, host, hobl⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hsp_al : (s.sp &&& 15#64) = 0#64 := by
    rw [hsp_eq]; exact hsp_align hpre.sp_aligned
  refine placed_memset_step_sat h_memset
    (dst := hsp s₀ + 146#64) (lr := (blkPl_73).base + 388#64) (val := 0#8) (len := 62)
    (htr_s := ⟨rfl, rfl⟩)
    hstat hpc hx0 hx1 (by rw [hx2]; rfl) hlr hsp_al rfl
    (hrw_hsp.sub (by clear * -; bv_omega))
    fun s' htr' hpc' hstat' hcc' _ _ _ hs2_frame hag_on => ?_
  refine RunsTo.refl ?_ htr'
  have hP_hsp : ∀ {off : BitVec 64} {n : Nat},
      (off - hsp s₀).toNat + n ≤ 480 →
      ∀ a, InRegion off n a → (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false := by
    intro off n hsub a ha
    have hnl := hrw_hsp a (by unfold InRegion at ha ⊢; bv_omega)
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
    exact ⟨by rw [hp]; rfl, hlf⟩
  have hframe_s' : S2Frame s₀.mem s'.mem [(s₀.sp - 1024#64, 1024)] := by
    refine (s2Frame_of_hmacFrame hframe).trans (hs2_frame.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    subst hr_mem
    have ha_stk := ha (s₀.sp - 1024#64, 1024) (by simp)
    clear * - ha_stk
    unfold hsp OutsideRegion at ha_stk ⊢
    bv_omega
  have hsaved_wb : HmacSaved s₀ (hsp s₀)
      (s.mem.writeBytes (hsp s₀ + 146#64) (List.replicate 62 0#8)) :=
    hsaved.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by clear * -; simp only [List.length_replicate, DisjointRegions]; bv_omega)
  refine
    { pc_eq := hpc'
      common :=
        { status := hstat'
          sp_eq := (CallingConventionPreserved.sp_eq hcc').trans hsp_eq
          x29_eq := (CallingConventionPreserved.x29 hcc').trans hx29
          x27_eq := (CallingConventionPreserved.x27 hcc').trans hx27
          saved := hmacSaved_of_agreesOn hag_on hsaved_wb
            (hP_hsp (by clear * -; bv_omega))
          frame := hframe_s' }
      x19_eq := (CallingConventionPreserved.x19 hcc').trans hx19
      x20_eq := (CallingConventionPreserved.x20 hcc').trans hx20
      x21_eq := (CallingConventionPreserved.x21 hcc').trans hx21
      x22_eq := (CallingConventionPreserved.x22 hcc').trans hx22
      x23_eq := (CallingConventionPreserved.x23 hcc').trans hx23
      x24_eq := (CallingConventionPreserved.x24 hcc').trans hx24
      x25_eq := (CallingConventionPreserved.x25 hcc').trans hx25
      x26_eq := (CallingConventionPreserved.x26 hcc').trans hx26
      m144 := by
        rw [AgreesOn.read64_eq hag_on (hsp s₀ + 144#64) (hP_hsp (by clear * -; bv_omega)),
            toLEBytes_8_read64_writeBytes_146_62 s.mem (hsp s₀), hm144_0, hm144_1]
        rfl
      m152 := (AgreesOn.read64_eq hag_on (hsp s₀ + 152#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 152#64 62)
      m160 := (AgreesOn.read64_eq hag_on (hsp s₀ + 160#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 160#64 62)
      m168 := (AgreesOn.read64_eq hag_on (hsp s₀ + 168#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 168#64 62)
      m176 := (AgreesOn.read64_eq hag_on (hsp s₀ + 176#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 176#64 62)
      m184 := (AgreesOn.read64_eq hag_on (hsp s₀ + 184#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 184#64 62)
      m192 := (AgreesOn.read64_eq hag_on (hsp s₀ + 192#64) (hP_hsp (by clear * -; bv_omega))).trans
        (read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 192#64 62)
      ist_eq := (AgreesOn.readBytes_eq hag_on (hsp s₀ + 208#64) 32 (by decide)
          (hP_hsp (by clear * -; bv_omega))).trans
        ((readBytes_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 208#64 32 62 0#8).trans hist)
      ibl_eq := (AgreesOn.read64_eq hag_on (hsp s₀ + 240#64) (hP_hsp (by clear * -; bv_omega))).trans
        ((read64_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 240#64 62 0#8).trans hibl)
      ost_eq := (AgreesOn.readBytes_eq hag_on (hsp s₀ + 248#64) 32 (by decide)
          (hP_hsp (by clear * -; bv_omega))).trans
        ((readBytes_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 248#64 32 62 0#8).trans host)
      obl_eq := (AgreesOn.read64_eq hag_on (hsp s₀ + 280#64) (hP_hsp (by clear * -; bv_omega))).trans
        ((read64_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 280#64 62 0#8).trans hobl) }

public theorem seg1b_placed_runsTo_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH1mPlaced F key s₀ s) :
    RunsTo (lsProg_73 H) s (StateH2PlacedSat F key byte s₀) :=
  (seg1b1_placed_runsTo_exact h_memcpy hpre hs).trans fun _ h1p =>
  seg1b2_placed_runsTo_sat h_memset hpre h1p

/-- Placed `RunsTo` execution of `hmac_sha256` (Block 73) under `HookSat` for `memset`. -/
public theorem hmac_placed_runsTo_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem)
    (hpre : HmacPlacedPre F key [byte] s₀)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) 32) :
    RunsTo (lsProg_73 H) s₀ (StateH5Sat F key byte s₀) := by
  refine (seg0_placed_runsTo_exact h_memcpy h_compress hcl hpre hread_key).trans fun _ h1 => ?_
  refine (seg1a_placed_runsTo hpre h1).trans fun _ h1m => ?_
  refine (seg1b_placed_runsTo_sat h_memcpy h_memset hpre h1m).trans fun s₂ h2 => ?_
  let s₀' : State := s₀.setMem s₂.mem
  have hs2_frame : S2Frame s₀.mem s₂.mem [(s₀.sp - 1024#64, 1024)] := h2.common.frame
  have hpre' : HmacPlacedPre F key [byte] s₀' :=
    { pc_eq := hpre.pc_eq
      status := hpre.status
      sp_aligned := hpre.sp_aligned
      x2_eq := hpre.x2_eq
      x4_eq := hpre.x4_eq
      key_len := hpre.key_len
      inp_len := hpre.inp_len
      key_eq := (s2Frame_readBytes_eq_of_readable hs2_frame hread_key (by decide)
        (by simp [hpre.disj_key_stack.symm])).trans hpre.key_eq
      inp_eq := (s2Frame_readBytes_eq_of_readable hs2_frame hpre.read_inp (by decide)
        (by simp [hpre.disj_inp_stack.symm])).trans hpre.inp_eq
      iv_eq := (s2Frame_readBytes_eq_of_readable hs2_frame hpre.read_iv (by decide)
        (by simp [hpre.disj_iv_stack.symm])).trans hpre.iv_eq
      read_iv := s2Frame_readable_of_readable hs2_frame hpre.read_iv
      read_inp := s2Frame_readable_of_readable hs2_frame hpre.read_inp
      rw_out := hs2_frame.rw_of_rw _ _ hpre.rw_out
      rw_stack := hs2_frame.rw_of_rw _ _ hpre.rw_stack
      disj_iv_stack := hpre.disj_iv_stack
      disj_out_stack := hpre.disj_out_stack
      disj_key_stack := hpre.disj_key_stack
      disj_inp_stack := hpre.disj_inp_stack }
  have h2' : StateH2Placed F key byte s₀' s₂ :=
    { pc_eq := h2.pc_eq
      common :=
        { status := h2.common.status
          sp_eq := h2.common.sp_eq
          x29_eq := h2.common.x29_eq
          x27_eq := h2.common.x27_eq
          saved := h2.common.saved
          frame := Frame.refl s₂.mem _ }
      x19_eq := h2.x19_eq, x20_eq := h2.x20_eq, x21_eq := h2.x21_eq, x22_eq := h2.x22_eq,
      x23_eq := h2.x23_eq, x24_eq := h2.x24_eq, x25_eq := h2.x25_eq, x26_eq := h2.x26_eq,
      m144 := h2.m144, m152 := h2.m152, m160 := h2.m160, m168 := h2.m168,
      m176 := h2.m176, m184 := h2.m184, m192 := h2.m192,
      ist_eq := h2.ist_eq, ibl_eq := h2.ibl_eq, ost_eq := h2.ost_eq, obl_eq := h2.obl_eq }
  refine ((seg2_placed_runsTo h_compress hpre' h2').trans fun _ h3 =>
    (seg3_placed_runsTo h_compress hpre' h3).trans fun _ h4 =>
    seg4_placed_runsTo hpre' h4).mono fun s₅ h5 => ?_
  have hs2_widen : S2Frame s₀.mem s₂.mem
      [(s₀.readReg64 .x0, 32), (s₀.sp - 1024#64, 1024)] :=
    hs2_frame.mono fun a ha r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ha _ (by simp)
  rcases h5 with ⟨hpc5, hstat5, hcs5, hout5, hfr5⟩
  exact
    { pc_eq := hpc5
      status := hstat5
      calleeSaved := hcs5
      out_eq := hout5
      frame := hs2_widen.trans (s2Frame_of_hmacFrame hfr5) }

/-! ## Separation-Logic Contracts -/

/-- Placed `hmac_sha256` contract on Block 73 under `HookSatExactMemcpy H lsMemcpySym` and `HookSat H lsMemsetSym sessionMemsetRegionSpec` (sibling of `hmac_sha256_placed_ok`). -/
public theorem hmac_sha256_placed_ok_sat [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl (hmacPlacedSpec F)) := by
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
  have hsp_split : stackAt s0.sp 2048 =
      memRegion (s0.sp - 2048#64) 1024 ∗ memRegion (s0.sp - 1024#64) 1024 :=
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
  have hread_key : s0.mem.Readable ka 32 :=
    Memory.RW.readable (fun a ha => hb_key.permNoLazy_rw hsep_key ha)
  have hread_inp : s0.mem.Readable ia 1 :=
    Memory.RW.readable (fun a ha => hb_inp.permNoLazy_rw hsep_inp ha)
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hpre_hmac : HmacPlacedPre F key [byte] s0 :=
    { pc_eq := hpc
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
      disj_inp_stack := by rw [hx3]; exact hb_inp.disjoint hb_stk (by simp) (by decide) hsep_inp }
  have hread_x1 : s0.mem.Readable (s0.readReg64 .x1) 32 := by rw [hx1]; exact hread_key
  refine (hmac_placed_runsTo_sat h_mc h_ms h_c256 hcl hpre_hmac hread_x1).to_reaches_pc
    fun sf h5 hkf _ htr hvregs => ?_
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
    S2Frame.update_two_blocks hb_out hb_out' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial
  change (sf.mem ⊨
    ((out ↦ₛ hmacWith F key [byte]) ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ [byte]) ∗
      (memRegion (s0.sp - 2048#64) 1024 ∗ memRegion (s0.sp - 1024#64) 1024)) ∗ R)
  ac_nf at hpost_sep ⊢

/-- `.rodata`-backed placed `hmac_sha256` contract on Block 73 under `HookSatExactMemcpy H lsMemcpySym` and `HookSat H lsMemsetSym sessionMemsetRegionSpec` (sibling of `hmac_sha256_placed_ro_ok`). -/
public theorem hmac_sha256_placed_ro_ok_sat [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    {H : String → Option (State → State)}
    (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_ms : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    subroutine_ok ((blkPC_73).rebase (blkPl_73).base H) (blkPl_73).base
      (withLsCodeLoaded lsmpl
        { hmacSpec F with pre := fun g s => (hmacSpec F).pre g s ∗ ⌜LibsignalRoLoaded lsmpl s.mem⌝ }) := by
  refine subroutine_ok_mono (hmac_sha256_placed_ok_sat F h_mc h_ms h_c256)
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

end LibsignalBinary.Proofs.ConsumeMessageKey.HmacSat
