/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSegsExt
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import ProofLib.SepLogic.HeapIntro

/-!
# Extended-Stack Verification of `finalize_fixed`

Completes segments 3a–4b, establishes `FinalizeFixedOkExt'` on `tripleRatchetProgAtExt`
from `HkdfContractsExt`, and provides the `RunsToE` bridge `finalize_fixed_runsTo_ext_x`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

namespace HkdfExt.FinX

open FinalizeFixedProof

theorem seg3a_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)} {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreX img C.F key msg s0)
    (hs : StateF3X img C.F key msg s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateF3bX img C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.toFinPre.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hpre.toFinPre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = 0x0003000000000000#64 := by decide
  have hrun : RunsTo (tripleRatchetProgAtExt img.base ext) s (StateF3bX img C.F key msg s0) := by
    have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
      read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
    have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
      read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
    iterate 31 s2_step
    clear hread32 hread40
    refine RunsTo.refl ?_
    obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
      _ _ _ _ _ _ _ _ _ _ _ _ 0#64 0x0003000000000000#64 0x80#64 0#64 0#64 0x0003000000000000#64
    have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
      unfold DisjointRegions; bv_omega
    have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
      (hpre.toFinPre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
      (hpre.toFinPre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
      unfold DisjointRegions; bv_omega
    refine ⟨by fin_reg,
      ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
       by rw [mem_setMem]
          exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved,
       by rw [mem_setMem]; exact s2Frame_of_frame_fsp hframe (frame_seg3a (Frame.refl s.mem _) hag1 hag2 hag3 hag4)⟩,
      by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      by rw [mem_setMem]
         refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
         rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
             toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
         have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
             toLEBytes 8 (rev64 768#64) =
             [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
         unfold outerBlock
         rw [digestBytes_eq_append h_in]
         simp only [List.append_assoc] at htail ⊢
         rw [htail]; rfl,
      by rw [mem_setMem]
         exact ost_eq_seg3a host hag1 hag2 hag3 hag4 hd_hm64_ost hd_fsp64_ost⟩
  exact runsTo_toE hrun

theorem seg3b_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec C.F extHookStack).inImage img))
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreX img C.F key msg s0)
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hs : StateF3bX img C.F key msg s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateF4X img C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_stk : s.mem.RW (s0.sp - 16528#64) 16528 := hframe.rw_of_rw _ _ hpre.rw_fsp
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  have hstep1 : RunsTo (tripleRatchetProgAtExt img.base ext) s (fun s1 =>
      s1.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") ∧
      s1.status = .Running ∧
      s1.sp = s0.sp - 144#64 ∧
      s1.readReg64 .lr = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]" + 308) ∧
      s1.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64 ∧
      s1.readReg64 .x1 = s0.sp - 144#64 ∧
      s1.readReg64 .x2 = 1#64 ∧
      s1.readReg64 .x19 = s0.readReg64 .x0 ∧
      s1.readReg64 .x20 = s0.readReg64 .x1 ∧
      s1.readReg64 .x26 = s0.readReg64 .x26 ∧
      s1.readReg64 .x27 = s0.readReg64 .x27 ∧
      s1.readReg64 .x28 = s0.readReg64 .x28 ∧
      s1.readReg64 .x29 = s0.sp - 144#64 + 0x40#64 ∧
      s1.mem = s.mem) := by
    s2_step
    refine RunsTo.refl ⟨rfl, hstat, hsp, rfl,
      by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
      by fin_reg, by fin_reg, by fin_reg, by fin_reg, rfl⟩
  refine (runsTo_toE hstep1).trans_full fun s1 hs1 hkf1 hsym1 => ?_
  rcases hs1 with ⟨hpc1, hstat1, hsp1, hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx26_1, hx27_1, hx28_1, hx29_1, hmem1⟩
  have hstk_eq : s1.sp - 16384#64 = s0.sp - 16528#64 := by
    rw [hsp1]; bv_omega
  have hrw_st : RW s1.mem (s0.readReg64 .x1 + 0x68#64) 32 := by
    rw [hmem1]; exact hrw_hm.sub (by bv_omega)
  have hrw_blk : RW s1.mem (s0.sp - 144#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by bv_omega)
  have hrw_ext_stk : RW s1.mem (s1.sp - 16384#64) 16384 := by
    rw [hmem1, hstk_eq]; exact hrw_stk.sub (by bv_omega)
  have hd_st_blk : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64) 64 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_st_stk : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s1.sp - 16384#64) 16384 := by
    rw [hstk_eq]
    exact (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_blk_stk : DisjointRegions (s0.sp - 144#64) 64 (s1.sp - 16384#64) 16384 := by
    rw [hstk_eq]; unfold DisjointRegions; bv_omega
  have hsp1_al : (s1.sp &&& 15#64) = 0#64 := by
    rw [hsp1]; exact fsp_aligned hpre.sp_aligned
  refine (compress256_one_subroutine_runsTo hComp (by decide)
    (hfrz.of_keepsFrozen hkf1) (hsym1.trans hsym)
    hpc1 hstat1 hx0_1 hx1_1 hx2_1 (hmem1 ▸ host) (hmem1 ▸ hblk)
    hrw_st hrw_blk hrw_ext_stk hd_st_blk hd_st_stk hd_blk_stk hsp1_al).trans_full
    fun s2 hs2 _ _ => ?_
  rcases hs2 with ⟨hpc2, hstat2, hcc2, host2, _, hframe2⟩
  intro hL2
  refine ⟨s2, .refl s2, ⟨rfl, rfl⟩, ?_, hL2⟩
  set blk_out := shaStateBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes h_in)))
  set m_ideal := s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out
  have hlen_out : blk_out.length = 32 := LibsignalTripleRatchet.shaStateBytes_length _
  have hag_comp : AgreesOutside s.mem m_ideal (s0.readReg64 .x1 + 0x68#64) 32 := by
    rw [← hlen_out]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hframe2' : S2Frame s.mem s2.mem
      [(s0.readReg64 .x1 + 0x68#64, blk_out.length), (s0.sp - 16528#64, 16384)] := by
    rw [hlen_out, ← hmem1, ← hstk_eq]; exact hframe2
  have hag_on : AgreesOn
      (fun a => s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a)
      s2.mem m_ideal :=
    AgreesOn.of_s2Frame_writeBytes (by rwa [hlen_out]) hframe2' (by rw [hlen_out]; decide)
  have hP_saved : ∀ a, InRegion (s0.sp - 144#64 + 0x40#64) 0x50 a →
      s.mem.permNoLazy a = some Perm.rw ∧ OutsideRegion (s0.sp - 16528#64) 16384 a := by
    intro a ha
    exact ⟨hrw_stk a (by unfold InRegion at ha ⊢; bv_omega),
      by simp only [InRegion, OutsideRegion] at ha ⊢; bv_omega⟩
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.toFinPre.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hframe_s2 : S2Frame s0.mem s2.mem
      [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 16528#64, 16528)] := by
    refine hframe.trans (hframe2'.mono fun a ha => ?_)
    intro r hr_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    rcases hr_mem with rfl | rfl
    · have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      rw [hlen_out]; unfold OutsideRegion at ha_hm ⊢; bv_omega
    · have ha_stk := ha (s0.sp - 16528#64, 16528) (by simp)
      unfold OutsideRegion at ha_stk ⊢; bv_omega
  refine
    { pc_eq := hpc2.trans hlr1
      common :=
        { status := hstat2
          sp_eq := (Extract.CallingConventionPreserved.sp_eq hcc2).trans hsp1
          x29_eq := (Extract.CallingConventionPreserved.x29 hcc2).trans hx29_1
          x26_eq := hcc2.2.2.2.2.2.2.2.2.1.trans hx26_1
          x27_eq := (Extract.CallingConventionPreserved.x27 hcc2).trans hx27_1
          x28_eq := hcc2.2.2.2.2.2.2.2.2.2.2.1.trans hx28_1
          saved := hag_on.finSaved_of (FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved) hP_saved
          frame := hframe_s2 }
      x19_eq := (Extract.CallingConventionPreserved.x19 hcc2).trans hx19_1
      x20_eq := (Extract.CallingConventionPreserved.x20 hcc2).trans hx20_1
      ost_eq := host2 }

theorem read32_seg4a_mid_x (m : Memory) (hm fsp off : BitVec 64) (w : BitVec 32)
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

theorem seg4a_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)} {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreX img C.F key msg s0)
    (hs : StateF4X img C.F key msg s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateF5X img C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := hframe.rw_of_rw _ _ hpre.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.toFinPre.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := hframe.rw_of_rw _ _ hpre.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  have hd_fsp64_hm : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 :=
    hpre.toFinPre.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩
  have hrun : RunsTo (tripleRatchetProgAtExt img.base ext) s (StateF5X img C.F key msg s0) := by
    iterate 11 s2_step
    have hread128 := read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
      (Or.inl rfl) hd_fsp64_hm hw6
    have hread132 := read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
      (Or.inr rfl) hd_fsp64_hm hw7
    iterate 2 s2_step
    clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
    iterate 15 s2_step
    refine RunsTo.refl ?_
    obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
      (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
    have hd_hm_saved : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 :=
      hpre.toFinPre.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩
    have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
      unfold DisjointRegions; bv_omega
    have hd_out_saved : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
      hpre.toFinPre.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩
    refine ⟨by fin_reg,
      ⟨by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg, by fin_reg,
       by rw [mem_setMem]
          exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved,
       by rw [mem_setMem]; exact s2Frame_of_frame_fsp hframe (frame_seg4a (Frame.refl s.mem _) hag1 hag2 hag3 hag4)⟩,
      by rw [mem_setMem]
         exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
           (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
           (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
           (hmacWith_short C.F key msg hpre.key_le hpre.msg_lt).symm⟩
  exact runsTo_toE hrun

theorem seg4b_x_runsTo {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)} {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPreX img C.F key msg s0)
    (hs : StateF5X img C.F key msg s0 s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (FinPostX C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := hframe.rw_of_rw _ _ hpre.toFinPre.rw_fsp
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
  have hrun : RunsTo (tripleRatchetProgAtExt img.base ext) s (FinPostX C.F key msg s0) := by
    iterate 7 s2_step
    refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
      ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [arm64_norm, hx26, hx27, hx28, hs19', hs20', hs21', hs22', hs23', hs24', hs25', hs29', hslr']
  exact runsTo_toE hrun

theorem finalize_fixed_runsToE_x {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hMemset : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memset"))
      ((session2MemsetExternSpec extHookStack).inImage img))
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec C.F extHookStack).inImage img))
    {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPreX img C.F key msg s0) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s0 (FinPostX C.F key msg s0) :=
  (seg1a_x_runsTo hpre).trans_full fun _ hs1 hkf1 hsym1 =>
  (seg1b_x_runsTo hMemset hpre (hpre.frz.of_keepsFrozen hkf1) (hsym1.trans hpre.sym) hs1).trans_full fun _ hs2 hkf2 hsym2 =>
  (seg2a_x_runsTo hpre hs2).trans_full fun _ hs3 hkf3 hsym3 =>
  (seg2b_x_runsTo hComp hpre
    (((hpre.frz.of_keepsFrozen hkf1).of_keepsFrozen hkf2).of_keepsFrozen hkf3)
    (hsym3.trans (hsym2.trans (hsym1.trans hpre.sym))) hs3).trans_full fun _ hs4 hkf4 hsym4 =>
  (seg3a_x_runsTo hpre hs4).trans_full fun _ hs5 hkf5 hsym5 =>
  (seg3b_x_runsTo hComp hpre
    (((((hpre.frz.of_keepsFrozen hkf1).of_keepsFrozen hkf2).of_keepsFrozen hkf3).of_keepsFrozen hkf4).of_keepsFrozen hkf5)
    (hsym5.trans (hsym4.trans (hsym3.trans (hsym2.trans (hsym1.trans hpre.sym))))) hs5).trans fun _ hs6 =>
  (seg4a_x_runsTo hpre hs6).trans fun _ hs7 =>
  seg4b_x_runsTo hpre hs7

end HkdfExt.FinX

/-! ## Top-Level `finalize_fixed_ok_ext'` and `RunsToE` Bridge -/

/-- `Hmac<Sha256>::finalize_fixed` meets `(finalizeFixedSpecExt C.F).inImage img` on
`tripleRatchetProgAtExt img.base ext` from `memset` and `compress256` stub contracts. -/
theorem finalize_fixed_ok_ext'_of_stubs {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hMemset : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memset"))
      ((HkdfExt.session2MemsetExternSpec extHookStack).inImage img))
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((HkdfExt.compress256ExternShaSpec C.F extHookStack).inImage img)) :
    FinalizeFixedOkExt' img C ext := by
  unfold FinalizeFixedOkExt'
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr finalizeFixedName =
      img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]") := by
    unfold tripleRatchetProgAtExt finalizeFixedName
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")]
  rw [hfn]
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, finalizeFixedSpecExt, sepConj_assoc, satisfies_pure_sepConj,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hkey_le, hmsg_lt⟩, hsep⟩
  have hmsg_lt64 : x.msg.length < 64 := by omega
  have hb_out := IsBlock.memRegion x.out 32
  have hb_hm := isBlock_hmacCoreAt C.F x.hm x.key x.msg hmsg_lt64
  have hb_stk := IsBlock.memRegion (s0.sp - 16528#64) 16528
  change s0.mem ⊨
    (memRegion x.out 32 ∗ hmacCoreAt C.F x.hm x.key x.msg ∗ memRegion (s0.sp - 16528#64) 16528) ∗ R at hsep
  have hsep_out : s0.mem ⊨ memRegion x.out 32 ∗
      (hmacCoreAt C.F x.hm x.key x.msg ∗ (memRegion (s0.sp - 16528#64) 16528 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_out_stk : s0.mem ⊨ memRegion x.out 32 ∗
      (memRegion (s0.sp - 16528#64) 16528 ∗ (hmacCoreAt C.F x.hm x.key x.msg ∗ R)) := by ac_nf at hsep ⊢
  have hsep_hm : s0.mem ⊨ hmacCoreAt C.F x.hm x.key x.msg ∗
      (memRegion x.out 32 ∗ (memRegion (s0.sp - 16528#64) 16528 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 16528#64) 16528 ∗
      (memRegion x.out 32 ∗ (hmacCoreAt C.F x.hm x.key x.msg ∗ R)) := by ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hm x.key x.msg ∗
      (memRegion (s0.sp - 16528#64) 16528 ∗ (memRegion x.out 32 ∗ R)) := by ac_nf at hsep ⊢
  have hhmac_st : HmacSt s0.mem x.hm C.F x.key x.msg := hb_hm.read hsep_hm
  have hrw_out : RW s0.mem x.out 32 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_hm : RW s0.mem x.hm 0x90 := fun a ha => hb_hm.permNoLazy_rw hsep_hm ha
  have hrw_stk : RW s0.mem (s0.sp - 16528#64) 16528 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hd_out_hm : DisjointRegions x.out 32 x.hm 0x90 :=
    hb_out.disjoint hb_hm (by decide) (by decide) hsep_out
  have hd_out_stk : DisjointRegions x.out 32 (s0.sp - 16528#64) 16528 :=
    hb_out.disjoint hb_stk (by decide) (by decide) hsep_out_stk
  have hd_hm_stk : DisjointRegions x.hm 0x90 (s0.sp - 16528#64) 16528 :=
    hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
  have hfin_pre : HkdfExt.FinX.FinPreX img C.F x.key x.msg s0 :=
    { frz := hfrz
      sym := hsym
      pc_eq := hpc
      status := hrun
      key_le := hkey_le
      msg_lt := hmsg_lt
      hmac_st := by rw [hx1]; exact hhmac_st
      rw_out := by rw [hx0]; exact hrw_out
      rw_hm := by rw [hx1]; exact hrw_hm
      rw_fsp := hrw_stk
      disj_out_hm := by rw [hx0, hx1]; exact hd_out_hm
      disj_out_fsp := by rw [hx0]; exact hd_out_stk
      disj_hm_fsp := by rw [hx1]; exact hd_hm_stk
      sp_aligned := by simpa [State.spAligned] using hsp }
  refine (HkdfExt.FinX.finalize_fixed_runsToE_x hMemset hComp hfin_pre).to_reaches_pc
    fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hout_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, LibsignalTripleRatchet.CallingConventionPreserved_of_calleeSaved hcallee⟩
  rw [Spec.inImage, finalizeFixedSpecExt]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  rw [hx0] at hout_sf
  rw [hx0, hx1] at hframe_sf
  have hb_out' := IsBlock.pointsToBytes_len (a := x.out) (length_hmacWith C.F x.key x.msg)
  have hb_hm' := IsBlock.memRegion x.hm 0x90
  have hpost_sep : sf.mem ⊨ (x.out ↦ₛ hmacWith C.F x.key x.msg) ∗
      (memRegion x.hm 0x90 ∗ (memRegion (s0.sp - 16528#64) 16528 ∗ R)) :=
    HkdfExt.S2Frame.update_three_blocks hb_out hb_out' hb_hm hb_hm' hb_stk hb_stk hsep_out hframe_sf
      ⟨by rw [length_hmacWith]; decide, by rwa [length_hmacWith]⟩ trivial trivial
  change sf.mem ⊨
    ((x.out ↦ₛ hmacWith C.F x.key x.msg) ∗ memRegion x.hm 0x90 ∗ memRegion (s0.sp - 16528#64) 16528) ∗ R
  ac_nf at hpost_sep ⊢

theorem finalize_fixed_ok_ext' (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State))
    (hHkdf : HkdfContractsExt img C.F ext) :
    FinalizeFixedOkExt' img C ext :=
  finalize_fixed_ok_ext'_of_stubs hHkdf.memset hHkdf.compress256

/-- Turn `FinalizeFixedOkExt' img C ext` into a `RunsToE` transition on
`tripleRatchetProgAtExt img.base ext` at `finalizeFixedStackExt = 16528` B. -/
theorem finalize_fixed_runsTo_ext_x {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hFin : FinalizeFixedOkExt' img C ext)
    {s : State} {out hm : BitVec 64} {key msg : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = out)
    (hx1 : s.readReg64 .x1 = hm)
    (hkey_le : key.length ≤ 64)
    (hmsg_lt : msg.length < 56)
    (hhm : HmacSt s.mem hm C.F key msg)
    (hrw_out : RW s.mem out 32)
    (hrw_hm : RW s.mem hm 0x90)
    (hrw_stk : RW s.mem (s.sp - 16528#64) 16528)
    (hd_out_hm : DisjointRegions out 32 hm 0x90)
    (hd_out_stk : DisjointRegions out 32 (s.sp - 16528#64) 16528)
    (hd_hm_stk : DisjointRegions hm 0x90 (s.sp - 16528#64) 16528)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.readBytes out 32 = hmacWith C.F key msg ∧
      S2Frame s.mem s'.mem [(out, 32), (hm, 0x90), (s.sp - 16528#64, 16528)]) := by
  intro hL
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr finalizeFixedName =
      img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]") := by
    unfold tripleRatchetProgAtExt finalizeFixedName
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<hmac::Hmac<sha2::Sha256> as digest::FixedOutput>::finalize_fixed [local#1]")]
  let xg : FinalizeFixedGhost := { out := out, hm := hm, key := key, msg := msg }
  let P1 : SepProp := memRegion out 32
  let P2 : SepProp := hmacCoreAt C.F hm key msg
  let P3 : SepProp := stackAt s.sp finalizeFixedStackExt
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 out 32 (fun _ => True) := IsBlock.memRegion out 32
  have hb2 : IsBlock P2 hm 0x90 (fun m => HmacSt m hm C.F key msg) :=
    isBlock_hmacCoreAt C.F hm key msg (by omega)
  have hb3 : IsBlock P3 (s.sp - 16528#64) 16528 (fun _ => True) :=
    IsBlock.memRegion (s.sp - 16528#64) 16528
  have hsatP : s.mem ⊨ P :=
    HkdfExt.satisfies_three_blocks hb1 hb2 hb3 trivial hhm trivial
      hrw_out hrw_hm hrw_stk hd_out_hm hd_out_stk hd_hm_stk (by decide) (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hpre_sat : s.mem ⊨ ((finalizeFixedSpecExt C.F).inImage img).pre xg s ∗ R := by
    rw [Spec.inImage, finalizeFixedSpecExt]
    dsimp only [xg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hkey_le, hmsg_lt⟩, ?_⟩
    simpa [P, P1, P2, P3, sepConj_assoc] using hsatPR
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hFin xg R (hpc.trans hfn.symm) hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [Spec.inImage, finalizeFixedSpecExt] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [Spec.inImage, finalizeFixedSpecExt] at he; rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [Spec.inImage, finalizeFixedSpecExt] at ho; rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  rw [Spec.inImage, finalizeFixedSpecExt] at hpost_sat
  dsimp only [xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  have hmac_len : (hmacWith C.F key msg).length = 32 := length_hmacWith C.F key msg
  let P1' : SepProp := (out ↦ₛ hmacWith C.F key msg)
  let P2' : SepProp := memRegion hm 0x90
  have hb1' : IsBlock P1' out 32
      (fun m => (hmacWith C.F key msg).length ≤ 2 ^ 64 ∧
        m.readBytes out (hmacWith C.F key msg).length = hmacWith C.F key msg) :=
    IsBlock.pointsToBytes_len hmac_len
  have hb2' : IsBlock P2' hm 0x90 (fun _ => True) := IsBlock.memRegion hm 0x90
  change s'.mem ⊨ (P1' ∗ P2' ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2' ∗ (P3 ∗ R)) := by ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2' ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2' ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2' ∗ P3)) := by ac_nf at hpost_1 ⊢
  have hout_s' : s'.mem.readBytes out 32 = hmacWith C.F key msg := by
    have h := (hb1'.read hpost_1).2
    rwa [hmac_len] at h
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : S2Frame s.mem s'.mem [(out, 32), (hm, 0x90), (s.sp - 16528#64, 16528)] :=
    HkdfExt.isBlock_three_all_s2frame hb1 hb1' hb2 hb2' hb3 hpP hmP hpost_1 hpost_2 hpost_3 hmc.1 hmc.2.2
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩, ⟨hpc', hstat', hcc, hout_s', hframe⟩,
    hsteps.codeLoaded hL⟩

end CryptoVerification.LibsignalTripleRatchet
