/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtHmacStepsA
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants

/-!
# `crypto::hmac_sha256` Symbolic-Offset Segments (`seg1b2` through `seg4b`)

Part B of the `RunsToE (tripleRatchetProgAtExt img.base ext)` segment proofs for
`libsignal_protocol::crypto::hmac_sha256` at `extHookStack` (`16384` B).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.CBC CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
  (tripleRatchetProgAtExt sessionMemcpySpec extHookStack)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsToE S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (session2MemsetExternSpec compress256ExternShaSpec
   memcpy_subroutine_runsTo memset_subroutine_runsTo
   compress256_subroutine_runsTo compress256_one_subroutine_runsTo)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

attribute [local arm64_norm]
  Memory.read128 Memory.write128 MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds
  read32_write8_base_off_disjoint

private theorem pc_setMem' (s : State) (m : Memory) :
    (s.setMem m).pc = s.pc := rfl

private theorem status_setMem' (s : State) (m : Memory) :
    (s.setMem m).status = s.status := rfl

private theorem sp_setMem' (s : State) (m : Memory) :
    (s.setMem m).sp = s.sp := rfl

private theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := rfl

private theorem read8_eq_of_readBytes_eq' {m₁ m₂ : Memory} {a₁ a₂ : BitVec 64} {n : ℕ}
    (h : m₁.readBytes a₁ n = m₂.readBytes a₂ n) {i : ℕ} (hi : i < n) :
    m₁.read8 (a₁ + BitVec.ofNat 64 i) = m₂.read8 (a₂ + BitVec.ofNat 64 i) := by
  have hget : (m₁.readBytes a₁ n)[i]? = (m₂.readBytes a₂ n)[i]? := by rw [h]
  simpa [Memory.readBytes, hi] using hget

private theorem read64_eq_writeBytes_146_62_of_s2Frame
    {m m' : Memory} {base : BitVec 64}
    (hrw : RW m (base + 144#64) 64)
    (hrep : m'.readBytes (base + 146#64) 62 = List.replicate 62 0#8)
    (hfr : S2Frame m m' [(base + 146#64, 62), (base - 16384#64, 16384)])
    (off : BitVec 64)
    (hoff : (off - 144#64).toNat + 8 ≤ 64 := by decide) :
    m'.read64 (base + off) =
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read64 (base + off) := by
  let mw := m.writeBytes (base + 146#64) (List.replicate 62 0#8)
  have hrep_w : mw.readBytes (base + 146#64) 62 = List.replicate 62 0#8 :=
    Layout.readBytes_writeBytes_eq m (base + 146#64) (List.replicate 62 0#8) 62 (by simp) (by decide)
  have hbyte (k : ℕ) (hk : k < 8) :
      m'.read8 ((base + off) + BitVec.ofNat 64 k) =
        mw.read8 ((base + off) + BitVec.ofNat 64 k) := by
    let a := (base + off) + BitVec.ofNat 64 k
    have hin64 : InRegion (base + 144#64) 64 a := by
      dsimp only [a]; unfold InRegion; clear * - hoff hk; bv_omega
    obtain ⟨hperm_a, hlf_a⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw a hin64)
    have hr_a : (m.perm a).r = true := by
      rw [hperm_a]; rfl
    by_cases hin62 : InRegion (base + 146#64) 62 a
    · obtain ⟨i, hi, ha_eq⟩ := (inRegion_iff_exists_offset (base + 146#64) 62 a (by decide)).mp hin62
      change m'.read8 a = mw.read8 a
      rw [ha_eq]
      exact read8_eq_of_readBytes_eq' (hrep.trans hrep_w.symm) hi
    · have hout62 : OutsideRegion (base + 146#64) 62 a :=
        (outsideRegion_iff_not_inRegion (base + 146#64) 62 a).mpr hin62
      have hout_stk : OutsideRegion (base - 16384#64) 16384 a := by
        dsimp only [a]; unfold OutsideRegion; clear * - hoff hk; bv_omega
      have hm' : m'.read8 a = m.read8 a :=
        hfr.1 a hr_a hlf_a (by
          intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hout62
          · exact hout_stk)
      have hmw : mw.read8 a = m.read8 a :=
        (_root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.AgreesOutside.writeBytes_self
          m (base + 146#64) (List.replicate 62 0#8)).1 a
          (by simpa using hout62)
      exact hm'.trans hmw.symm
  have e0 := hbyte 0 (by decide)
  have e1 := hbyte 1 (by decide)
  have e2 := hbyte 2 (by decide)
  have e3 := hbyte 3 (by decide)
  have e4 := hbyte 4 (by decide)
  have e5 := hbyte 5 (by decide)
  have e6 := hbyte 6 (by decide)
  have e7 := hbyte 7 (by decide)
  change m'.read64 (base + off) = mw.read64 (base + off)
  dsimp only [Memory.read64]
  simp only [e0, e1, e2, e3, e4, e5, e6, e7]

theorem seg1b2_runsTo_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hMemset : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memset"))
      ((session2MemsetExternSpec extHookStack).inImage img))
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH1pX img F key byte s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH2X img F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26,
    hm144_0, hm144_1, hist, hibl, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_stack : RW s.mem (s₀.sp - 17408#64) 17408 :=
    hframe.rw_of_rw _ _ hpre.rw_stack
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    hrw_stack.sub (by unfold hsp; clear * -; bv_omega)
  have hsp_ext_eq : s.sp - BitVec.ofNat 64 extHookStack = hsp s₀ - 16384#64 := by
    rw [hsp_eq]; rfl
  have hrw_stk_ext : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]
    exact hrw_stack.sub (by unfold hsp extHookStack; clear * -; bv_omega)
  have hd_dst_stk : DisjointRegions (hsp s₀ + 146#64) 62 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega
  have hrun := memset_subroutine_runsTo hMemset
    (dst := hsp s₀ + 146#64) (val := 0#8) (n := 62)
    hfrz hsym hpc hstat hx0 hx1 (by rw [hx2]; rfl)
    (hrw_hsp.sub (by clear * -; bv_omega)) hrw_stk_ext hd_dst_stk
    (by rw [hsp_eq]; exact hal_hsp)
  refine runsToE_mono_with_inv hrun hfrz hsym fun s₁ hfrz₁ hsym₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, hrep₁, hfr_ms⟩
  rw [hlr] at hpc₁
  have hfr_ms' : S2Frame s.mem s₁.mem [(hsp s₀ + 146#64, 62), (hsp s₀ - 16384#64, 16384)] := by
    rwa [← hsp_ext_eq]
  have hrw144 : RW s.mem (hsp s₀ + 144#64) 64 := hrw_hsp.sub (by clear * -; bv_omega)
  have hr64 (off : BitVec 64) (hoff : (off - 144#64).toNat + 8 ≤ 64 := by decide) :=
    read64_eq_writeBytes_146_62_of_s2Frame hrw144 hrep₁ hfr_ms' off hoff
  have hread_hsp (off : BitVec 64) (len : ℕ) (hsub : off.toNat + len ≤ 480) :
      RW s.mem (hsp s₀ + off) len :=
    hrw_hsp.sub (by clear * - hsub; bv_omega)
  refine {
    pc_eq := hpc₁
    common := {
      frz := hfrz₁
      sym := hsym₁
      status := hstat₁
      sp_eq := hcc₁.1.trans hsp_eq
      x29_eq := hcc₁.2.readReg64_x29.trans hx29
      x27_eq := hcc₁.2.2.2.2.2.2.2.2.2.1.trans hx27
      saved := hmacSaved_of_s2Frame hsaved (hrw_hsp.sub (by clear * -; bv_omega)) hfr_ms' (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega))
      frame := s2Frame_trans_pair_stk17408 hframe hfr_ms'
        (by unfold hsp; clear * -; bv_omega)
        (by unfold hsp; clear * -; bv_omega)
    }
    x19_eq := hcc₁.2.1.trans hx19
    x20_eq := hcc₁.2.2.1.trans hx20
    x21_eq := hcc₁.2.2.2.1.trans hx21
    x22_eq := hcc₁.2.2.2.2.1.trans hx22
    x23_eq := hcc₁.2.2.2.2.2.1.trans hx23
    x24_eq := hcc₁.2.2.2.2.2.2.1.trans hx24
    x25_eq := hcc₁.2.2.2.2.2.2.2.1.trans hx25
    x26_eq := hcc₁.2.2.2.2.2.2.2.2.1.trans hx26
    m144 := by
      rw [hr64 144#64, toLEBytes_8_read64_writeBytes_146_62 s.mem (hsp s₀), hm144_0, hm144_1]
      rfl
    m152 := by rw [hr64 152#64]; exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 152#64 62
    m160 := by rw [hr64 160#64]; exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 160#64 62
    m168 := by rw [hr64 168#64]; exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 168#64 62
    m176 := by rw [hr64 176#64]; exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 176#64 62
    m184 := by rw [hr64 184#64]; exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 184#64 62
    m192 := by rw [hr64 192#64]; exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 192#64 62
    ist_eq := (hfr_ms'.readBytes_eq (hread_hsp 208#64 32 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega)) (by decide)).trans hist
    ibl_eq := (hfr_ms'.read64_eq (hread_hsp 240#64 8 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega))).trans hibl
    ost_eq := (hfr_ms'.readBytes_eq (hread_hsp 248#64 32 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega)) (by decide)).trans host
    obl_eq := (hfr_ms'.read64_eq (hread_hsp 280#64 8 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega))).trans hobl
  }

theorem seg2a_runsTo_ext {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH2X img F key byte s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH2cX img F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26,
    hm144, hm152, hm160, hm168, hm176, hm184, hm192,
    hist, hibl, host, hobl⟩
  refine runsToE_of_runsTo_with_inv (tripleRatchetProgAtExt img.base ext) hfrz hsym ?_
  generalize hPost : (fun s' => img.FrozenLoaded s' → s'.symtab = img.symtab → StateH2cX img F key byte s₀ s') = Post
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    (hframe.rw_of_rw _ _ hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 14 sess_step
  subst hPost
  refine _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo.refl ?_
  intro hfrz' hsym'
  refine ⟨?_, ⟨hfrz', hsym', ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [pc_setMem']; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · rw [status_setMem']; simp only [arm64_norm, hstat]
  · rw [sp_setMem']; simp only [arm64_norm, hsp_eq]
  · rw [readReg64_setMem']; simp only [arm64_norm, hx29]
  · rw [readReg64_setMem']; simp only [arm64_norm, hx27]
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm,
        s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine s2Frame_trans_r7b_stack1024 hframe ?_
    iterate 9 refine Frame.write64_stack1024 ?_ _ _
    exact Frame.refl s.mem _
  · rw [readReg64_setMem']; simp only [arm64_norm, hx21]
  · rw [readReg64_setMem']; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · rw [readReg64_setMem']; simp only [arm64_norm]
  · rw [readReg64_setMem']; simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · rw [readReg64_setMem']; simp only [arm64_norm, hx19]
  · rw [readReg64_setMem']; simp only [arm64_norm, hx20]
  · rw [readReg64_setMem']; simp only [arm64_norm, hx21]
  · rw [readReg64_setMem']; simp only [arm64_norm, hx22]
  · rw [readReg64_setMem']; simp only [arm64_norm, hx23]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]
    rw [readBytes_32_off_eq_read64] at hist
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at hist ⊢
    exact hist
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_64_off_eq_read64]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm,
      hm144, hm152, hm160, hm168, hm176, hm184, hm192, toLEBytes_8_rev64]
    unfold innerLastBlock
    simp only [List.length_cons, List.length_nil]
    rfl
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]
    rw [readBytes_32_off_eq_read64] at host
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at host ⊢
    exact host
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl]

theorem seg2b_runsTo_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec F extHookStack).inImage img))
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH2cX img F key byte s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH3X img F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, hx21, hx22, hx23, hist, hiblk, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_stack : RW s.mem (s₀.sp - 17408#64) 17408 :=
    hframe.rw_of_rw _ _ hpre.rw_stack
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    hrw_stack.sub (by unfold hsp; clear * -; bv_omega)
  have hsp_ext_eq : s.sp - BitVec.ofNat 64 extHookStack = hsp s₀ - 16384#64 := by
    rw [hsp_eq]; rfl
  have hrw_stk_ext : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]
    exact hrw_stack.sub (by unfold hsp extHookStack; clear * -; bv_omega)
  have hd_st_blk : DisjointRegions (hsp s₀ + 208#64) 32 (hsp s₀ + 304#64) 64 := by
    unfold hsp DisjointRegions; clear * -; bv_omega
  have hd_st_stk : DisjointRegions (hsp s₀ + 208#64) 32 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega
  have hd_blk_stk : DisjointRegions (hsp s₀ + 304#64) 64 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega
  have hrun := compress256_one_subroutine_runsTo hComp
    (by decide) hfrz hsym hpc hstat hx0 hx1 hx2 hist hiblk
    (hrw_hsp.sub (by clear * -; bv_omega)) (hrw_hsp.sub (by clear * -; bv_omega)) hrw_stk_ext
    hd_st_blk hd_st_stk hd_blk_stk (by rw [hsp_eq]; exact hal_hsp)
  refine runsToE_mono_with_inv hrun hfrz hsym fun s₁ hfrz₁ hsym₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, hst₁, _, hfr_c⟩
  rw [hlr] at hpc₁
  have hfr_c' : S2Frame s.mem s₁.mem [(hsp s₀ + 208#64, 32), (hsp s₀ - 16384#64, 16384)] := by
    rwa [← hsp_ext_eq]
  have hread_hsp (off : BitVec 64) (len : ℕ) (hsub : off.toNat + len ≤ 480) :
      RW s.mem (hsp s₀ + off) len :=
    hrw_hsp.sub (by clear * - hsub; bv_omega)
  have hr32 (i : Fin 8) :
      s₁.mem.read32 ((hsp s₀ + 208#64) + BitVec.ofNat 64 (4 * i.val)) =
        (innerDigest F key byte).get i :=
    read32_of_readBytes_shaStateBytes hst₁ i
  refine {
    pc_eq := hpc₁
    common := {
      frz := hfrz₁
      sym := hsym₁
      status := hstat₁
      sp_eq := hcc₁.1.trans hsp_eq
      x29_eq := hcc₁.2.readReg64_x29.trans hx29
      x27_eq := hcc₁.2.2.2.2.2.2.2.2.2.1.trans hx27
      saved := hmacSaved_of_s2Frame hsaved (hrw_hsp.sub (by clear * -; bv_omega)) hfr_c' (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega))
      frame := s2Frame_trans_pair_stk17408 hframe hfr_c'
        (by unfold hsp; clear * -; bv_omega)
        (by unfold hsp; clear * -; bv_omega)
    }
    x19_eq := hcc₁.2.1.trans hx19
    x20_eq := hcc₁.2.2.1.trans hx20
    x21_eq := hcc₁.2.2.2.1.trans hx21
    x22_eq := hcc₁.2.2.2.2.1.trans hx22
    x23_eq := hcc₁.2.2.2.2.2.1.trans hx23
    hi0 := by simpa [BitVec.add_assoc] using hr32 0
    hi1 := by simpa [BitVec.add_assoc] using hr32 1
    hi2 := by simpa [BitVec.add_assoc] using hr32 2
    hi3 := by simpa [BitVec.add_assoc] using hr32 3
    hi4 := by simpa [BitVec.add_assoc] using hr32 4
    hi5 := by simpa [BitVec.add_assoc] using hr32 5
    hi6 := by simpa [BitVec.add_assoc] using hr32 6
    hi7 := by simpa [BitVec.add_assoc] using hr32 7
    ost_eq := (hfr_c'.readBytes_eq (hread_hsp 248#64 32 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega)) (by decide)).trans host
    obl_eq := (hfr_c'.read64_eq (hread_hsp 280#64 8 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega))).trans hobl
  }

theorem seg3a_runsTo_ext {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH3X img F key byte s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH3cX img F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, hx21, hx22, hx23,
    hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, host, hobl⟩
  refine runsToE_of_runsTo_with_inv (tripleRatchetProgAtExt img.base ext) hfrz hsym ?_
  generalize hPost : (fun s' => img.FrozenLoaded s' → s'.symtab = img.symtab → StateH3cX img F key byte s₀ s') = Post
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    (hframe.rw_of_rw _ _ hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 32 sess_step
  subst hPost
  refine _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo.refl ?_
  intro hfrz' hsym'
  refine ⟨?_, ⟨hfrz', hsym', ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · simp only [arm64_norm, hstat]
  · simp only [arm64_norm, hsp_eq]
  · simp only [arm64_norm, hx29]
  · simp only [arm64_norm, hx27]
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm,
        s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine s2Frame_trans_r7b_stack1024 hframe ?_
    iterate 10 refine Frame.write64_stack1024 ?_ _ _
    iterate 4 refine Frame.write32_stack1024 ?_ _ _
    refine Frame.write64_stack1024 ?_ _ _
    iterate 4 refine Frame.write32_stack1024 ?_ _ _
    refine Frame.write64_stack1024 ?_ _ _
    refine Frame.write8_stack1024 ?_ _ _
    exact Frame.refl s.mem _
  · simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · simp only [arm64_norm]
  · simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · simp only [arm64_norm, hx19]
  · simp only [arm64_norm, hx20]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_32_off_eq_read64]
    rw [readBytes_32_off_eq_read64] at host
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm] at host ⊢
    exact host
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [readBytes_64_off_eq_read64]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm,
      hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hobl,
      toLEBytes_8_rev32_append, toLEBytes_8_rev64]
    rw [toLEBytes_8_read64_eq, toLEBytes_8_read64_eq]
    simp (config := { decide := true }) only [Memory.readBytes, List.range, List.range.loop, List.map,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
    unfold outerBlock
    rw [digestBytes_eq_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl

theorem seg3b_runsTo_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec F extHookStack).inImage img))
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH3cX img F key byte s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH4X img F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, host, hoblk⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_stack : RW s.mem (s₀.sp - 17408#64) 17408 :=
    hframe.rw_of_rw _ _ hpre.rw_stack
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    hrw_stack.sub (by unfold hsp; clear * -; bv_omega)
  have hsp_ext_eq : s.sp - BitVec.ofNat 64 extHookStack = hsp s₀ - 16384#64 := by
    rw [hsp_eq]; rfl
  have hrw_stk_ext : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]
    exact hrw_stack.sub (by unfold hsp extHookStack; clear * -; bv_omega)
  have hd_st_blk : DisjointRegions (hsp s₀ + 248#64) 32 (hsp s₀ + 304#64) 64 := by
    unfold hsp DisjointRegions; clear * -; bv_omega
  have hd_st_stk : DisjointRegions (hsp s₀ + 248#64) 32 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega
  have hd_blk_stk : DisjointRegions (hsp s₀ + 304#64) 64 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega
  have hrun := compress256_one_subroutine_runsTo hComp
    (by decide) hfrz hsym hpc hstat hx0 hx1 hx2 host hoblk
    (hrw_hsp.sub (by clear * -; bv_omega)) (hrw_hsp.sub (by clear * -; bv_omega)) hrw_stk_ext
    hd_st_blk hd_st_stk hd_blk_stk (by rw [hsp_eq]; exact hal_hsp)
  refine runsToE_mono_with_inv hrun hfrz hsym fun s₁ hfrz₁ hsym₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, hst₁, _, hfr_c⟩
  rw [hlr] at hpc₁
  have hfr_c' : S2Frame s.mem s₁.mem [(hsp s₀ + 248#64, 32), (hsp s₀ - 16384#64, 16384)] := by
    rwa [← hsp_ext_eq]
  have hr32 (i : Fin 8) :
      s₁.mem.read32 ((hsp s₀ + 248#64) + BitVec.ofNat 64 (4 * i.val)) =
        (outerDigest F key byte).get i :=
    read32_of_readBytes_shaStateBytes hst₁ i
  refine {
    pc_eq := hpc₁
    common := {
      frz := hfrz₁
      sym := hsym₁
      status := hstat₁
      sp_eq := hcc₁.1.trans hsp_eq
      x29_eq := hcc₁.2.readReg64_x29.trans hx29
      x27_eq := hcc₁.2.2.2.2.2.2.2.2.2.1.trans hx27
      saved := hmacSaved_of_s2Frame hsaved (hrw_hsp.sub (by clear * -; bv_omega)) hfr_c' (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; clear * -; bv_omega))
      frame := s2Frame_trans_pair_stk17408 hframe hfr_c'
        (by unfold hsp; clear * -; bv_omega)
        (by unfold hsp; clear * -; bv_omega)
    }
    x19_eq := hcc₁.2.1.trans hx19
    x20_eq := hcc₁.2.2.1.trans hx20
    ho0 := by simpa [BitVec.add_assoc] using hr32 0
    ho1 := by simpa [BitVec.add_assoc] using hr32 1
    ho2 := by simpa [BitVec.add_assoc] using hr32 2
    ho3 := by simpa [BitVec.add_assoc] using hr32 3
    ho4 := by simpa [BitVec.add_assoc] using hr32 4
    ho5 := by simpa [BitVec.add_assoc] using hr32 5
    ho6 := by simpa [BitVec.add_assoc] using hr32 6
    ho7 := by simpa [BitVec.add_assoc] using hr32 7
  }

theorem seg4a_runsTo_ext {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH4X img F key byte s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH4bX img F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7⟩
  refine runsToE_of_runsTo_with_inv (tripleRatchetProgAtExt img.base ext) hfrz hsym ?_
  generalize hPost : (fun s' => img.FrozenLoaded s' → s'.symtab = img.symtab → StateH4bX img F key byte s₀ s') = Post
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    (hframe.rw_of_rw _ _ hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  have hrw_out : s.mem.RW (s₀.readReg64 .x0) 32 :=
    hframe.rw_of_rw _ _ hpre.rw_out
  iterate 31 sess_step
  subst hPost
  refine _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo.refl ?_
  intro hfrz' hsym'
  refine ⟨hfrz', hsym', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hpc, BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · simp only [arm64_norm, hstat]
  · simp only [arm64_norm, hsp_eq]
  · simp only [arm64_norm, hx27]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    have hsaved1 : HmacSaved s₀ (hsp s₀)
        (((((((((((((((((s.mem.write8 (hsp s₀ + 207#64) 0#8).write64
          (hsp s₀ + 304#64) 0#64).write64
          (hsp s₀ + 312#64) 0#64).write64
          (hsp s₀ + 320#64) 0#64).write64
          (hsp s₀ + 328#64) 0#64).write64
          (hsp s₀ + 336#64) 0#64).write64
          (hsp s₀ + 344#64) 0#64).write64
          (hsp s₀ + 352#64) 0#64).write64
          (hsp s₀ + 360#64) 0#64).write64
          (hsp s₀ + 192#64) 0#64).write64
          (hsp s₀ + 200#64) 0#64).write64
          (hsp s₀ + 176#64) 0#64).write64
          (hsp s₀ + 184#64) 0#64).write64
          (hsp s₀ + 160#64) 0#64).write64
          (hsp s₀ + 168#64) 0#64).write64
          (hsp s₀ + 144#64) 0#64).write64
          (hsp s₀ + 152#64) 0#64) := by
      rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
      dsimp only [HmacSaved]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm,
          s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
    exact hsaved1.of_agreesOutside
      (_root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.AgreesOutside.writeBytes_self _ _ _) (by
      have hd := hpre.disj_out_stack
      simp only [digestBytes_length, DisjointRegions, Reg.x0] at hd ⊢
      unfold hsp; clear * - hd; bv_omega)
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    have hread : ∀ m : Memory,
        (m.writeBytes (s₀.readReg64 .x0) (digestBytes (outerDigest F key byte))).readBytes
          (s₀.readReg64 .x0) 32 = digestBytes (outerDigest F key byte) :=
      fun m => Layout.readBytes_writeBytes_eq m _ _ 32 (digestBytes_length _) (by decide)
    rw [hread, hmacWith_short F key [byte] (by rw [hpre.key_len]; decide) (by simp)]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [write32_rev32_64_8_eq_writeBytes_digestBytes]
    refine s2Frame_writeBytes_out_stk17408 (s2Frame_trans_r7b_stack1024 hframe ?_) _ (digestBytes_length _)
    iterate 16 refine Frame.write64_stack1024 ?_ _ _
    refine Frame.write8_stack1024 ?_ _ _
    exact Frame.refl s.mem _

theorem seg4b_runsTo_ext {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH4bX img F key byte s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH5X F key byte s₀) := by
  refine runsToE_hmac ?_
  generalize hPost : StateH5X F key byte s₀ = Post
  rcases hs with ⟨_, _, hpc, hstat, hsp_eq, hx27, hsaved, hout, hframe⟩
  rcases hsaved with ⟨s29, slr, s28, s26, s25, s24, s23, s22, s21, s20, s19⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    (hframe.rw_of_rw _ _ hpre.rw_stack).sub (by unfold hsp; clear * -; bv_omega)
  iterate 8 sess_step
  subst hPost
  refine _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo.refl ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [arm64_norm, slr]
  · simp only [arm64_norm, hstat]
  · refine ⟨?_, ?_⟩
    · simp only [arm64_norm, hsp_eq, ← hsp_eq_add]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [arm64_norm, s19, s20, s21, s22, s23, s24, s25, s26, hx27, s28, s29, slr]
  · exact hout
  · exact hframe

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX
