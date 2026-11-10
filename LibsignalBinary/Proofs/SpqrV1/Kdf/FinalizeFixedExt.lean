/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedInnerExt
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.SpqrV1.Kdf.HooksExt
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon

/-!
# Outer Hash, Epilogue, and `Fin3GenRunsToEExt` for `finalize_fixed` (`0x6ce50`)

Completes `finalize_fixed3_gen_runsToE_ext : Fin3GenRunsToEExt img F ext` from
`SpqrKdfHooksExt img F ext` at `finalizeFixed3StackExt` (`16528` B).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SpqrV1.Kdf

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.CodeLayout
open ProofLib.ProgramReflection
open SpqrKdfExt

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

@[simp, arm64_norm] private
gen_decodes libsignalSessionCode_tree libsignalSessionCode [(ls_off% finalizeFixed3Name + 180) → (ls_off% finalizeFixed3Name + 444)]

namespace FinalizeFixed3ExtProof

/-! ### Shared Outer Hash & Epilogue (`hex:6cf04 → lr`) -/

private structure StateF3bGen (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (h_in : ShaState) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 304)
  common  : FinCommonExt s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = outerBlock (digestBytes h_in)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateF4Gen (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (h_in : ShaState) (s0 s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 308)
  common  : FinCommonExt s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key) (outerBlock (digestBytes h_in)))

private structure StateF5Gen (img : Obj.Image) (out_bytes : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = img.base + bv% (ls_off% finalizeFixed3Name + 420)
  common : FinCommonExt s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = out_bytes

private theorem seg3a_gen_runsTo {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)}
    {h_in : ShaState} {s0 s : State}
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hs : StateF3Gen img F key h_in s0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (StateF3bGen img F key h_in s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_hm_of hpre.rw_hm hframe
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_fsp144_of hpre.rw_fsp hframe
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = 0x0003000000000000#64 := by decide
  have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  iterate 31 fin3_step
  clear hread32 hread40
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _ _ _ _ 0#64 0x0003000000000000#64 0x80#64 0#64 0#64 0x0003000000000000#64
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hpre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by
            rw [mem_setMem]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside
                (FinSaved.of_agreesOutside
                  (FinSaved.of_agreesOutside hsaved hag1 hd_hm64_saved)
                  hag2 hd_fsp64_saved)
                hag3 hd_hm64_saved)
              hag4 hd_fsp64_saved
          frame := by rw [mem_setMem]; exact s2frame_seg3a hframe hag1 hag2 hag3 hag4 }
      x0_eq := by fin3_reg, x1_eq := by fin3_reg, x2_eq := by fin3_reg,
      x19_eq := by fin3_reg, x20_eq := by fin3_reg
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
            toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
        have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
            toLEBytes 8 (rev64 768#64) =
            [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
        unfold outerBlock
        rw [digestBytes_eq_append h_in]
        simp only [List.append_assoc] at htail ⊢
        rw [htail]; rfl
      ost_eq := by
        rw [mem_setMem]
        exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost }

private theorem seg3b_gen_runsToE {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)}
    {h_in : ShaState} {s0 s : State}
    (hHooks : SpqrKdfHooksExt img F ext)
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hs : StateF3bGen img F key h_in s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateF4Gen img F key h_in s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_hm_of hpre.rw_hm hframe
  have hrw_stk : s.mem.RW (s0.sp - 16528#64) 16528 := hframe.rw_of_rw _ _ hpre.rw_fsp
  have hbl : RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s_bl =>
      s_bl.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") ∧
      s_bl.readReg64 .lr = img.base + bv% (ls_off% finalizeFixed3Name + 308) ∧
      s_bl.status = .Running ∧
      s_bl.sp = s0.sp - 144#64 ∧
      s_bl.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64 ∧
      s_bl.readReg64 .x1 = s0.sp - 144#64 ∧
      s_bl.readReg64 .x2 = 1#64 ∧
      s_bl.readReg64 .x19 = s0.readReg64 .x0 ∧
      s_bl.readReg64 .x20 = s0.readReg64 .x1 ∧
      s_bl.readReg64 .x26 = s0.readReg64 .x26 ∧
      s_bl.readReg64 .x27 = s0.readReg64 .x27 ∧
      s_bl.readReg64 .x28 = s0.readReg64 .x28 ∧
      s_bl.readReg64 .x29 = s0.sp - 144#64 + 64#64 ∧
      s_bl.mem = s.mem) := by
    fin3_step
    exact RunsTo.refl ⟨by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg, by fin3_reg,
      by fin3_reg, by fin3_reg, rfl⟩
  refine RunsToE.trans_frozen hfrz hsym (runsTo_toE hbl) fun s_bl hfrz_bl hsym_bl hs_bl => ?_
  rcases hs_bl with ⟨hpc_bl, hlr_bl, hstat_bl, hsp_bl, hx0_bl, hx1_bl, hx2_bl,
    hx19_bl, hx20_bl, hx26_bl, hx27_bl, hx28_bl, hx29_bl, hmem_bl⟩
  have hrw_ost : s_bl.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := by
    rw [hmem_bl]; exact hrw_hm.sub (by bv_omega)
  have hrw_blk : s_bl.mem.RW (s0.sp - 144#64) 64 := by
    rw [hmem_bl]; exact hrw_stk.sub (by bv_omega)
  have hrw_hstk : s_bl.mem.RW (s_bl.sp - 16384#64) 16384 := by
    rw [hmem_bl, hsp_bl]; exact hrw_stk.sub (by bv_omega)
  have hd_ost_blk : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ost_hstk : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s_bl.sp - 16384#64) 16384 := by
    rw [hsp_bl]
    exact (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_blk_hstk : DisjointRegions (s0.sp - 144#64) 64 (s_bl.sp - 16384#64) 16384 := by
    rw [hsp_bl]; unfold DisjointRegions; bv_omega
  have hal_bl : (s_bl.sp &&& 15#64) = 0#64 := by
    rw [hsp_bl]; exact fsp_aligned hpre.sp_aligned
  have host_bl : s_bl.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
      shaStateBytes (hmacOuterInit F key) := by rw [hmem_bl]; exact host
  have hblk_bl : s_bl.mem.readBytes (s0.sp - 144#64) 64 = outerBlock (digestBytes h_in) := by
    rw [hmem_bl]; exact hblk
  refine (compress256_one_subroutine_runsTo hHooks.compress256 (by decide) hfrz_bl hsym_bl hpc_bl hstat_bl hx0_bl hx1_bl
    hx2_bl host_bl hblk_bl
    hrw_ost hrw_blk hrw_hstk hd_ost_blk hd_ost_hstk hd_blk_hstk hal_bl).mono fun sf hsf => ?_
  rcases hsf with ⟨hpc_sf, hstat_sf, hcc_sf, host_sf, _, hframe_sf⟩
  rcases hcc_sf with ⟨hsp_cc, hx19_cc, hx20_cc, _, _, _, _, _, hx26_cc, hx27_cc, hx28_cc, hx29_cc, _⟩
  have hframe_s : S2Frame s.mem sf.mem
      [(s0.readReg64 .x1 + 0x68#64, 32), ((s0.sp - 144#64) - 16384#64, 16384)] := by
    rw [← hmem_bl, ← hsp_bl]; exact hframe_sf
  have hframe_tot : S2Frame s0.mem sf.mem (FinRegsExt s0) :=
    s2frame_hook_hm_sub hframe hframe_s (by bv_omega)
  set out_st := shaStateBytes (F (hmacOuterInit F key) (outerBlock (digestBytes h_in)))
  have hlen_st : out_st.length = 32 := shaStateBytes_length _
  have hag_on : AgreesOn (fun a => ((s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false) ∧
      OutsideRegion ((s0.sp - 144#64) - 16384#64) 16384 a) sf.mem
      (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) out_st) := by
    have host_sf' : sf.mem.readBytes (s0.readReg64 .x1 + 0x68#64) out_st.length = out_st := by
      rw [hlen_st]; exact host_sf
    have hfr' : S2Frame s.mem sf.mem
        [(s0.readReg64 .x1 + 0x68#64, out_st.length), ((s0.sp - 144#64) - 16384#64, 16384)] := by
      rw [hlen_st]; exact hframe_s
    exact AgreesOn.of_s2Frame_writeBytes host_sf' hfr' (by rw [hlen_st]; decide)
  have hag_wb : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) out_st)
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    rw [← hlen_st]; exact ProofLib.AgreesOutside.writeBytes_self s.mem _ out_st
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      ((s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false) ∧ OutsideRegion ((s0.sp - 144#64) - 16384#64) 16384 a := by
    intro a ha
    have ha_stk : InRegion (s0.sp - 16528#64) 16528 a := by unfold InRegion at ha ⊢; bv_omega
    exact ⟨hrw_stk.readable a ha_stk, by unfold InRegion at ha; unfold OutsideRegion; bv_omega⟩
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  exact
    { pc_eq := hpc_sf.trans hlr_bl
      common :=
        { status := hstat_sf
          sp_eq := hsp_cc.trans hsp_bl
          x29_eq := hx29_cc.trans hx29_bl
          x26_eq := hx26_cc.trans hx26_bl
          x27_eq := hx27_cc.trans hx27_bl
          x28_eq := hx28_cc.trans hx28_bl
          saved := hag_on.finSaved_of (FinSaved.of_agreesOutside hsaved hag_wb hd_ost_saved) hP_saved
          frame := hframe_tot }
      x19_eq := hx19_cc.trans hx19_bl
      x20_eq := hx20_cc.trans hx20_bl
      ost_eq := host_sf }

private theorem read32_seg4a_mid (m : Memory) (hm fsp off : BitVec 64) (w : BitVec 32)
    (hoff : off = 128#64 ∨ off = 132#64)
    (hd : DisjointRegions fsp 64 hm 0x90)
    (hw : m.read32 (hm + off) = w) :
    (((((((((m.write8 (hm + 63#64) 0#8).write64
      fsp 0#64).write64 (fsp + 8#64) 0#64).write64
      (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
      (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
      (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64).read32
      (hm + off) = w := by
  have hag_fsp : AgreesOutside (m.write8 (hm + 63#64) 0#8)
      (((((((((m.write8 (hm + 63#64) 0#8).write64
        fsp 0#64).write64 (fsp + 8#64) 0#64).write64
        (fsp + 16#64) 0#64).write64 (fsp + 24#64) 0#64).write64
        (fsp + 32#64) 0#64).write64 (fsp + 40#64) 0#64).write64
        (fsp + 48#64) 0#64).write64 (fsp + 56#64) 0#64)
      fsp 64 := by agrees_outside_writes
  have hag_63 : AgreesOutside m (m.write8 (hm + 63#64) 0#8) (hm + 63#64) 1 := by
    agrees_outside_writes
  rcases hoff with rfl | rfl <;>
    rw [hag_fsp.read32_eq (hd.sub_right _ ⟨by decide, by bv_omega⟩),
        hag_63.read32_eq (by unfold DisjointRegions; bv_omega), hw]

private theorem seg4a_disj {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {key pfx tail : List (BitVec 8)} {s0 : State} (hpre : FinPre3PfxGenExt img F key pfx tail s0) :
    DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 ∧
    DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 ∧
    DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
  ⟨(hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩).symm,
   hpre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩,
   by unfold DisjointRegions; bv_omega,
   hpre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩⟩

private theorem seg4a_gen_runsTo {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)}
    {h_in : ShaState} {out_bytes : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hout_eq : digestBytes (F (hmacOuterInit F key) (outerBlock (digestBytes h_in))) = out_bytes)
    (hs : StateF4Gen img F key h_in s0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (StateF5Gen img out_bytes s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_hm_of hpre.rw_hm hframe
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_fsp144_of hpre.rw_fsp hframe
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_out_of hpre.rw_out hframe
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := F (hmacOuterInit F key) (outerBlock (digestBytes h_in))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 fin3_step
  have hd_fsp64_hm := (seg4a_disj hpre).1
  have hread128 := read32_seg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_seg4a_mid s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
    (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 fin3_step
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 fin3_step
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
    (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
  obtain ⟨_, hd_hm_saved, hd_fsp64_saved, hd_out_saved⟩ := seg4a_disj hpre
  refine
    { pc_eq := by fin3_reg
      common :=
        { status := by fin3_reg, sp_eq := by fin3_reg, x29_eq := by fin3_reg,
          x26_eq := by fin3_reg, x27_eq := by fin3_reg, x28_eq := by fin3_reg,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4
              hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by rw [mem_setMem]; exact s2frame_seg4a hframe hag1 hag2 hag3 hag4 }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
          hout_eq }

private def FinPostGenExt (out_bytes : List (BitVec 8)) (s0 s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = out_bytes ∧
  S2Frame s0.mem s'.mem (FinRegsExt s0)

private theorem seg4b_gen_runsTo {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)}
    {out_bytes : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hs : StateF5Gen img out_bytes s0 s) :
    RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s0.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s0 s' ∧
      s'.mem.readBytes (s0.readReg64 .x0) 32 = out_bytes ∧
      S2Frame s0.mem s'.mem (FinRegsExt s0)) := by
  change RunsTo (tripleRatchetProgAtExt img.base ext) s (FinPostGenExt out_bytes s0)
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_fsp144_of hpre.rw_fsp hframe
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  rcases hsaved with ⟨hs29, hslr, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hs29' : s.mem.read64 (s0.sp - 144#64 + 64#64) = s0.readReg64 .x29 := hs29
  have hslr' : s.mem.read64 (s0.sp - 144#64 + 72#64) = s0.readReg64 .lr := hslr
  have hs25' : s.mem.read64 (s0.sp - 144#64 + 80#64) = s0.readReg64 .x25 := hs25
  have hs24' : s.mem.read64 (s0.sp - 144#64 + 96#64) = s0.readReg64 .x24 := hs24
  have hs23' : s.mem.read64 (s0.sp - 144#64 + 104#64) = s0.readReg64 .x23 := hs23
  have hs22' : s.mem.read64 (s0.sp - 144#64 + 112#64) = s0.readReg64 .x22 := hs22
  have hs21' : s.mem.read64 (s0.sp - 144#64 + 120#64) = s0.readReg64 .x21 := hs21
  have hs20' : s.mem.read64 (s0.sp - 144#64 + 128#64) = s0.readReg64 .x20 := hs20
  have hs19' : s.mem.read64 (s0.sp - 144#64 + 136#64) = s0.readReg64 .x19 := hs19
  iterate 7 fin3_step
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
    ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arm64_norm, hx26, hx27, hx28]

private theorem post_f3_runsToE {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)}
    {h_in : ShaState} {s0 s : State}
    (hHooks : SpqrKdfHooksExt img F ext)
    (hpre : FinPre3PfxGenExt img F key pfx tail s0)
    (hout_eq : digestBytes (F (hmacOuterInit F key) (outerBlock (digestBytes h_in))) =
      hmacWith F key (pfx ++ tail))
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hs : StateF3Gen img F key h_in s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s0.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s0 s' ∧
      s'.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (pfx ++ tail) ∧
      S2Frame s0.mem s'.mem (FinRegsExt s0)) :=
  RunsToE.trans_frozen hfrz hsym (runsTo_toE (seg3a_gen_runsTo hpre hs)) fun s1 hfrz1 hsym1 hs1 =>
  RunsToE.trans_frozen hfrz1 hsym1 (seg3b_gen_runsToE hHooks hpre hfrz1 hsym1 hs1) fun s2 hfrz2 hsym2 hs2 =>
  RunsToE.trans_frozen hfrz2 hsym2 (runsTo_toE (seg4a_gen_runsTo hpre hout_eq hs2)) fun _ _ _ hs3 =>
  runsTo_toE (seg4b_gen_runsTo hpre hs3)

theorem finalize_fixed3_pfx_lt64_runsToE_ext {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key pfx tail : List (BitVec 8)} {s0 : State}
    (hHooks : SpqrKdfHooksExt img F ext)
    (hpre : FinPre3PfxGenExt img F key pfx tail s0) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s0 (fun s' =>
      s'.pc = s0.readReg64 .lr ∧
      s'.status = .Running ∧
      CalleeSaved s0 s' ∧
      s'.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key (pfx ++ tail) ∧
      S2Frame s0.mem s'.mem (FinRegsExt s0)) := by
  refine RunsToE.trans_frozen hpre.frz hpre.sym (runsTo_toE (seg1a_runsTo hpre)) fun s1 hfrz1 hsym1 hs1 => ?_
  refine RunsToE.trans_frozen hfrz1 hsym1 (seg1b_runsToE hHooks hpre hfrz1 hsym1 hs1) fun s2 hfrz2 hsym2 hs2 => ?_
  by_cases hlt56 : tail.length < 56
  · refine RunsToE.trans_frozen hfrz2 hsym2 (runsTo_toE (seg2a_runsTo hpre hlt56 hs2)) fun s3 hfrz3 hsym3 hs3 => ?_
    refine RunsToE.trans_frozen hfrz3 hsym3 (seg2b_runsToE hHooks hpre hlt56 hfrz3 hsym3 hs3) fun s4 hfrz4 hsym4 hs4 => ?_
    exact post_f3_runsToE hHooks hpre
      (hmacWith_pfx_short F key pfx tail hpre.key_le hpre.hmac_st.1 hlt56).symm hfrz4 hsym4 hs4
  · have hge56 : 56 ≤ tail.length := Nat.le_of_not_lt hlt56
    refine RunsToE.trans_frozen hfrz2 hsym2 (runsTo_toE (seg2_two_a_runsTo hpre hge56 hs2)) fun s3 hfrz3 hsym3 hs3 => ?_
    refine RunsToE.trans_frozen hfrz3 hsym3 (seg2_two_b_runsToE hHooks hpre hfrz3 hsym3 hs3) fun s4 hfrz4 hsym4 hs4 => ?_
    refine RunsToE.trans_frozen hfrz4 hsym4 (runsTo_toE (seg2_two_c_runsTo hpre hs4)) fun s5 hfrz5 hsym5 hs5 => ?_
    refine RunsToE.trans_frozen hfrz5 hsym5 (seg2_two_d_runsToE hHooks hpre hfrz5 hsym5 hs5) fun s6 hfrz6 hsym6 hs6 => ?_
    exact post_f3_runsToE hHooks hpre
      (hmacWith_pfx_two_blocks F key pfx tail hpre.key_le hpre.hmac_st.1 hge56 hpre.tail_lt).symm
      hfrz6 hsym6 hs6

end FinalizeFixed3ExtProof

/-- Generalized `RunsToE` contract of `finalize_fixed [local#3]` (`hex:6ce50`) at `16528` B stack
from `SpqrKdfHooksExt img F ext` (covering `< 56` and `[56, 64)` over `HmacStN` and arbitrary `key`). -/
theorem finalize_fixed3_gen_runsToE_ext (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (ext : String → Option (State → State)) (hHooks : SpqrKdfHooksExt img F ext) :
    Fin3GenRunsToEExt img F ext := by
  intro key pfx tail s₀ hpre
  have hpre' : FinalizeFixed3ExtProof.FinPre3PfxGenExt img F (effectiveHmacKey F key) pfx tail s₀ :=
    { frz          := hpre.frz
      sym          := hpre.sym
      pc_eq        := hpre.pc_eq
      status       := hpre.status
      key_le       := effectiveHmacKey_length_le F key
      tail_lt      := hpre.tail_lt
      hmac_st      := hpre.hmac_st
      rw_out       := hpre.rw_out
      rw_hm        := hpre.rw_hm
      rw_fsp       := hpre.rw_fsp
      disj_out_hm  := hpre.disj_out_hm
      disj_out_fsp := hpre.disj_out_fsp
      disj_hm_fsp  := hpre.disj_hm_fsp
      sp_aligned   := hpre.sp_aligned }
  refine (FinalizeFixed3ExtProof.finalize_fixed3_pfx_lt64_runsToE_ext hHooks hpre').mono
    fun s' ⟨hpc', hstat', hcs', hout', hfr'⟩ => ?_
  rw [hmacWith_effectiveHmacKey] at hout'
  exact ⟨hpc', hstat', hcs', hout', hfr'⟩

end CryptoVerification.SpqrV1.Kdf
