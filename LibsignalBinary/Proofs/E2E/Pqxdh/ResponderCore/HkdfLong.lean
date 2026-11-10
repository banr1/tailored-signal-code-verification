/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand -- shake: keep
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFin
public import LibsignalBinary.Proofs.CodeLayout -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandLoop
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandSegsExt
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep

/-!
# `Hkdf<Sha256>::expand_multi_info` (`0x1a874`) for 96-Byte Output and 46-Byte Info

Proves `expand_multi_info_96_46_runsTo` for `<hkdf::Hkdf<sha2::Sha256>>::expand_multi_info`
(`b + 0x1a874`) when `okmLen = 96` and `info.length = 46` (`INFO_PQXDH`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet.Expand


set_option maxRecDepth 200000
set_option maxHeartbeats 800000

variable {b : BitVec 64}
theorem hkdfExpand_96_eq (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 96 =
      t1 F prk info ++ t2 F prk info ++ t3 F prk info := by
  dsimp only [hkdfExpand]
  have h3 : (96 + 31) / 32 = 3 := rfl
  have hblocks : (hkdfBlocks F prk info 3).flatten =
      t1 F prk info ++ t2 F prk info ++ t3 F prk info := by
    simp [hkdfBlocks, t1, t2, t3, List.append_assoc]
  rw [h3, hblocks, List.take_of_length_le]
  simp [t1, t2, t3, length_hmacWith]

/-- Bundled preconditions of `expand_multi_info` (`b + 0x1a874`) for `okmLen = 96` and
`info.length = 46`. -/
structure ExpandPre96_46 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) (infoPtr : BitVec 64) (s₀ : State) : Prop where
  pc_eq         : s₀.pc = b + 0x1a874#64
  status        : s₀.status = .Running
  x3_eq         : s₀.readReg64 .x3 = 96#64
  prk_le        : prk.length ≤ 64
  info_len_eq   : info.length = 46
  hmac_st       : HmacSt s₀.mem (s₀.readReg64 .x0) F prk []
  info_ptr      : s₀.mem.read64 (s₀.readReg64 .x1) = infoPtr
  info_len      : s₀.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64
  info_bytes    : s₀.mem.readBytes infoPtr 46 = info
  read_x0       : s₀.mem.Readable (s₀.readReg64 .x0) 0x90
  read_x1       : s₀.mem.Readable (s₀.readReg64 .x1) 16
  rw_x2         : RW s₀.mem (s₀.readReg64 .x2) 96
  rw_stack      : RW s₀.mem (s₀.sp - 640#64) 640
  disj_x2_stack : DisjointRegions (s₀.readReg64 .x2) 96 (s₀.sp - 640#64) 640
  disj_x0_stack : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.sp - 640#64) 640
  disj_x0_x2    : DisjointRegions (s₀.readReg64 .x0) 0x90 (s₀.readReg64 .x2) 96
  disj_x1_stack : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.sp - 640#64) 640
  disj_x1_x2    : DisjointRegions (s₀.readReg64 .x1) 16 (s₀.readReg64 .x2) 96
  out_info_stk  : ∀ a, InRegion infoPtr 46 a → OutsideRegion (s₀.sp - 640#64) 640 a
  out_info_x2   : ∀ a, InRegion infoPtr 46 a → OutsideRegion (s₀.readReg64 .x2) 96 a
  sp_aligned    : (s₀.sp &&& 15#64) = 0#64

namespace ExpandPre96_46

variable {F : ShaState → List (BitVec 8) → ShaState}
  {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State} {m : Memory}

theorem rw_esp (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.RW (esp s₀) 496 := by
  have hrw : m.RW (s₀.sp - 640#64) 640 := (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_stack
  unfold esp
  exact hrw.sub (by bv_omega)

theorem rw_x2_frame (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.RW (s₀.readReg64 .x2) 96 :=
  (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_x2

theorem readable_x0 (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.Readable (s₀.readReg64 .x0) 0x90 :=
  (Expand.Frame.readable_iff hf _ _).mpr hpre.read_x0

theorem readable_x1 (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.Readable (s₀.readReg64 .x1) 16 :=
  (Expand.Frame.readable_iff hf _ _).mpr hpre.read_x1

theorem hmac_x0 (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    HmacSt m (s₀.readReg64 .x0) F prk [] := by
  have hd : ∀ r ∈ [(s₀.readReg64 .x2, 96), (s₀.sp - 640#64, 640)],
      DisjointRegions r.1 r.2 (s₀.readReg64 .x0) 0x90 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x0_x2.symm
    · exact hpre.disj_x0_stack.symm
  rcases hpre.hmac_st with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · refine (hf.1 _ (fun r hr => ?_)).trans hpos
    exact (hd r hr).outside (by unfold InRegion; bv_omega) (by decide)
  · refine (Expand.Frame.readBytes_eq hf (fun r hr => ?_) (by decide)).trans hin
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x40#64) ⟨by decide, by bv_omega⟩
  · refine (Expand.Frame.read64_eq hf (fun r hr => ?_)).trans hcnt1
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x60#64) ⟨by decide, by bv_omega⟩
  · refine (Expand.Frame.readBytes_eq hf (fun r hr => ?_) (by decide)).trans hout
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x68#64) ⟨by decide, by bv_omega⟩
  · refine (Expand.Frame.read64_eq hf (fun r hr => ?_)).trans hcnt2
    exact (hd r hr).sub_right (s₀.readReg64 .x0 + 0x88#64) ⟨by decide, by bv_omega⟩

theorem info_ptr_eq (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.read64 (s₀.readReg64 .x1) = infoPtr := by
  rw [Expand.Frame.read64_eq hf]
  · exact hpre.info_ptr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
    · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem info_len_eq_46 (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 := by
  rw [Expand.Frame.read64_eq hf]
  · exact hpre.info_len
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hpre.disj_x1_x2.symm.sub_right _ ⟨by decide, by bv_omega⟩
    · exact hpre.disj_x1_stack.symm.sub_right _ ⟨by decide, by bv_omega⟩

theorem info_bytes_eq (hpre : ExpandPre96_46 b F prk info infoPtr s₀) (hf : ExpandFrame 96 s₀ m) :
    m.readBytes infoPtr 46 = info := by
  refine (List.ext_getElem (by simp [hpre.info_len_eq]) fun i h1 h2 => ?_).trans hpre.info_bytes
  rw [Bytes.readBytes_getElem _ _ _ i h1, Bytes.readBytes_getElem _ _ _ i h2]
  have hi : i < 46 := by simpa using h1
  have hin : InRegion infoPtr 46 (infoPtr + BitVec.ofNat 64 i) :=
    inRegion_base_add infoPtr 46 i hi (by decide)
  refine hf.1 _ (fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hpre.out_info_x2 _ hin
  · exact hpre.out_info_stk _ hin

theorem saved_of_agreesOutside_x2 {m' : Memory} {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre96_46 b F prk info infoPtr s₀)
    (hs : ExpandSaved s₀ m)
    (hA : AgreesOutside m m' (s₀.readReg64 .x2 + off) sz)
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 96) :
    ExpandSaved s₀ m' := by
  have hd_x2_saved : DisjointRegions (s₀.readReg64 .x2 + off) sz (esp s₀ + 400#64) 96 := by
    have hd1 := hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + off)
      ⟨hoff.1, by have := hoff.2; bv_omega⟩
    unfold esp
    exact hd1.sub_right (s₀.sp - 496#64 + 400#64) ⟨by decide, by bv_omega⟩
  have hread (k : BitVec 64) (hk : 400 ≤ k.toNat ∧ k.toNat + 8 ≤ 496) :
      m'.read64 (esp s₀ + k) = m.read64 (esp s₀ + k) := by
    refine hA.read64_eq ?_
    exact hd_x2_saved.sub_right (esp s₀ + k) ⟨by decide, by bv_omega⟩
  exact
    { m400 := (hread 400#64 (by decide)).trans hs.m400
      m408 := (hread 408#64 (by decide)).trans hs.m408
      m416 := (hread 416#64 (by decide)).trans hs.m416
      m424 := (hread 424#64 (by decide)).trans hs.m424
      m432 := (hread 432#64 (by decide)).trans hs.m432
      m440 := (hread 440#64 (by decide)).trans hs.m440
      m448 := (hread 448#64 (by decide)).trans hs.m448
      m456 := (hread 456#64 (by decide)).trans hs.m456
      m464 := (hread 464#64 (by decide)).trans hs.m464
      m472 := (hread 472#64 (by decide)).trans hs.m472
      m480 := (hread 480#64 (by decide)).trans hs.m480
      m488 := (hread 488#64 (by decide)).trans hs.m488 }

theorem common_of_agreesOutside_x2 {s s' : State} {off : BitVec 64} {sz : ℕ}
    (hpre : ExpandPre96_46 b F prk info infoPtr s₀)
    (hc : ExpandCommon 96 s₀ s)
    (hstat : s'.status = .Running)
    (hsp   : s'.sp = esp s₀)
    (hx29  : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27  : s'.readReg64 .x27 = esp s₀ + 64#64)
    (hx20  : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hA    : AgreesOutside s.mem s'.mem (s₀.readReg64 .x2 + off) sz)
    (hoff  : 0 < sz ∧ off.toNat + sz ≤ 96) :
    ExpandCommon 96 s₀ s' := by
  have hd_x2_esp : DisjointRegions (s₀.readReg64 .x2 + off) sz (esp s₀) 32 := by
    have hd1 := hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + off)
      ⟨hoff.1, by have := hoff.2; bv_omega⟩
    unfold esp
    exact hd1.sub_right (s₀.sp - 496#64) ⟨by decide, by bv_omega⟩
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hA.read64_eq (hd_x2_esp.sub_right (esp s₀ + 8#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hA.read64_eq (hd_x2_esp.sub_right (esp s₀ + 16#64) ⟨by decide, by bv_omega⟩)]
    exact hc.m16_eq
  exact ⟨hstat, hsp, hx29, hx27, hx20, hm8, hm16,
    hpre.saved_of_agreesOutside_x2 hc.saved hA hoff,
    ExpandFrame.of_agreesOutside_x2 hc.frame hA hoff.2⟩

theorem read64_x0_write64_esp (hpre : ExpandPre96_46 b F prk info infoPtr s₀) :
    (∀ (m : Memory) (off v : BitVec 64) (hoff : decide (off.toNat + 8 ≤ 496) = true),
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x0) = m.read64 (s₀.readReg64 .x0)) ∧
    (∀ (m : Memory) (off x0_off v : BitVec 64)
        (hoff : decide (off.toNat + 8 ≤ 496) = true)
        (hx0 : decide (x0_off.toNat + 8 ≤ 0x90) = true),
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x0 + x0_off) =
        m.read64 (s₀.readReg64 .x0 + x0_off)) := by
  refine ⟨fun m off v hoff => ?_, fun m off x0_off v hoff hx0 => ?_⟩
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 0x90 :=
      hpre.disj_x0_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 8 :=
      h1.sub_right (s₀.readReg64 .x0) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have hx0' : x0_off.toNat + 8 ≤ 0x90 := of_decide_eq_true hx0
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0) 0x90 :=
      hpre.disj_x0_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x0 + x0_off) 8 :=
      h1.sub_right (s₀.readReg64 .x0 + x0_off) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd

theorem read64_x1_write_esp (hpre : ExpandPre96_46 b F prk info infoPtr s₀) :
    (∀ (m : Memory) (off v : BitVec 64) (hoff : decide (off.toNat + 8 ≤ 496) = true),
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x1) = m.read64 (s₀.readReg64 .x1)) ∧
    (∀ (m : Memory) (off v : BitVec 64) (hoff : decide (off.toNat + 8 ≤ 496) = true),
      (m.write64 (esp s₀ + off) v).read64 (s₀.readReg64 .x1 + 8#64) =
        m.read64 (s₀.readReg64 .x1 + 8#64)) ∧
    (∀ (m : Memory) (off : BitVec 64) (v : BitVec 8) (hoff : decide (off.toNat < 496) = true),
      (m.write8 (esp s₀ + off) v).read64 (s₀.readReg64 .x1) = m.read64 (s₀.readReg64 .x1)) ∧
    (∀ (m : Memory) (off : BitVec 64) (v : BitVec 8) (hoff : decide (off.toNat < 496) = true),
      (m.write8 (esp s₀ + off) v).read64 (s₀.readReg64 .x1 + 8#64) =
        m.read64 (s₀.readReg64 .x1 + 8#64)) := by
  refine ⟨fun m off v hoff => ?_, fun m off v hoff => ?_,
          fun m off v hoff => ?_, fun m off v hoff => ?_⟩
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 8 :=
      h1.sub_right (s₀.readReg64 .x1) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat + 8 ≤ 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 8 (s₀.readReg64 .x1 + 8#64) 8 :=
      h1.sub_right (s₀.readReg64 .x1 + 8#64) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 8 |>.write64 (by bv_omega) (by decide)).read64_eq hd
  · have hoff' : off.toNat < 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 8 :=
      h1.sub_right (s₀.readReg64 .x1) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 1 |>.write8 (by simp [InRegion])).read64_eq hd
  · have hoff' : off.toNat < 496 := of_decide_eq_true hoff
    have h1 : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1) 16 :=
      hpre.disj_x1_stack.symm.sub_left (esp s₀ + off) ⟨by decide, by unfold esp; bv_omega⟩
    have hd : DisjointRegions (esp s₀ + off) 1 (s₀.readReg64 .x1 + 8#64) 8 :=
      h1.sub_right (s₀.readReg64 .x1 + 8#64) ⟨by decide, by bv_omega⟩
    exact (AgreesOutside.rfl' m (esp s₀ + off) 1 |>.write8 (by simp [InRegion])).read64_eq hd

theorem fin_side_conditions {s : State}
    (hpre : ExpandPre96_46 b F prk info infoPtr s₀)
    (hf : ExpandFrame 96 s₀ s.mem) :
    RW s.mem (esp s₀ + 208#64) 32 ∧
    RW s.mem (esp s₀ + 240#64) 0x90 ∧
    RW s.mem (esp s₀ - 144#64) 144 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ + 240#64) 0x90 ∧
    DisjointRegions (esp s₀ + 208#64) 32 (esp s₀ - 144#64) 144 ∧
    DisjointRegions (esp s₀ + 240#64) 0x90 (esp s₀ - 144#64) 144 := by
  have hrw_stack : s.mem.RW (s₀.sp - 640#64) 640 :=
    (Expand.Frame.rw_iff hf _ _).mpr hpre.rw_stack
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hf
  refine ⟨hrw_esp.sub (by bv_omega), hrw_esp.sub (by bv_omega),
    hrw_stack.sub (by unfold esp; bv_omega),
    by unfold DisjointRegions; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega,
    by unfold DisjointRegions esp at *; bv_omega⟩

end ExpandPre96_46

/-! ## Block 1 (`T(1)`) -/

theorem HmacSt.of_memcpy_counter_64_0_46 {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key info : List (BitVec 8)}
    (h₀ : HmacSt m₀ (esp s₀ + 64#64) F key [])
    (hinfo : info.length = 46) :
    HmacSt (((((m₀.writeBytes (esp s₀ + 64#64) info).write8
      (esp s₀ + 127#64) 46#8).write8
      (esp s₀ + 240#64) 1#8).write8
      (esp s₀ + 110#64) 1#8).write8
      (esp s₀ + 127#64) 47#8)
      (esp s₀ + 64#64) F key (info ++ [1#8]) := by
  let a := esp s₀ + 64#64
  let m₁ := m₀.writeBytes a info
  let m₂ := (((m₁.write8 (a + 63#64) 46#8).write8 (a + 176#64) 1#8).write8
    (a + 46#64) 1#8).write8 (a + 63#64) 47#8
  have h127 : esp s₀ + 127#64 = a + 63#64 := by dsimp [a]; bv_lin
  have h240 : esp s₀ + 240#64 = a + 176#64 := by dsimp [a]; bv_lin
  have h110 : esp s₀ + 110#64 = a + 46#64 := by dsimp [a]; bv_lin
  rw [h127, h240, h110]
  change HmacSt m₂ a F key (info ++ [1#8])
  rcases h₀ with ⟨_, _, _, hin, hcnt1, hout, hcnt2⟩
  have hlen : (info ++ [1#8]).length = 47 := by simp [hinfo]
  have hag_w : AgreesOutside m₁ m₂ (a + 46#64) 177 := by
    dsimp only [m₂]
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    exact AgreesOutside.write8 (AgreesOutside.rfl' _ _ _) (by simp only [InRegion]; bv_omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen, show (47 : ℕ) = 46 + 1 from rfl, Bytes.readBytes_add m₂ a 46 1]
    have h_info : m₂.readBytes a 46 = info := by
      have hd2 : DisjointRegions (a + 46#64) 177 a 46 := by
        unfold DisjointRegions; bv_omega
      rw [hag_w.readBytes_eq hd2 (by decide)]
      dsimp only [m₁]
      have h := Bytes.readBytes_writeBytes_same m₀ a info (by omega)
      rwa [hinfo] at h
    have h_c : m₂.readBytes (a + BitVec.ofNat 64 46) 1 = [1#8] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_info, h_c]
  · rw [hlen, show (0x3f#64 : BitVec 64) = 63#64 from rfl]
    dsimp only [m₂]
    exact Memory.read8_write8_same _ _ _
  · have h_ag_st : ∀ (off : BitVec 64) (sz : ℕ),
        0 < sz → 64 ≤ off.toNat → off.toNat + sz ≤ 144 →
        m₂.readBytes (a + off) sz = m₀.readBytes (a + off) sz := by
      intro off sz hsz0 h64 h144
      dsimp only [m₂, m₁]
      rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by omega),
          writeBytes_readBytes_disj m₀ _ info (a + off) sz
            (fun _ _ => by unfold DisjointRegions; bv_omega) (by omega)]
    exact (h_ag_st 0x40#64 32 (by decide) (by decide) (by decide)).trans hin
  · dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        writeBytes_read64_disj m₀ _ info (a + 0x60#64)
          (fun _ => by unfold DisjointRegions; bv_omega),
        hcnt1]
  · have h_ag_out : m₂.readBytes (a + 0x68#64) 32 = m₀.readBytes (a + 0x68#64) 32 := by
      dsimp only [m₂, m₁]
      rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
            (by unfold DisjointRegions; bv_omega) (by decide),
          writeBytes_readBytes_disj m₀ _ info (a + 0x68#64) 32
            (fun _ _ => by unfold DisjointRegions; bv_omega) (by decide)]
    exact h_ag_out.trans hout
  · dsimp only [m₂, m₁]
    rw [(AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 46#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 176#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        (AgreesOutside.rfl' _ (a + 63#64) 1 |>.write8 (by simp [InRegion])).read64_eq
          (by unfold DisjointRegions; bv_omega),
        writeBytes_read64_disj m₀ _ info (a + 0x88#64)
          (fun _ => by unfold DisjointRegions; bv_omega),
        hcnt2]

/-- Cut `LoopA2_96` at `b + 0x9722c` (`memcpy(esp + 96, infoPtr, 32)`). -/
structure StateLoopA2_96 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  common  : ExpandCommon 96 s₀ s
  lr_eq   : s.readReg64 .lr = b + 0x1abf0#64
  x0_eq   : s.readReg64 .x0 = esp s₀ + 96#64
  x1_eq   : s.readReg64 .x1 = infoPtr
  x2_eq   : s.readReg64 .x2 = 32#64
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = 32#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = 14#64
  m0_eq   : s.mem.read64 (esp s₀) = infoPtr + 32#64
  hmac_64 : HmacSt s.mem (esp s₀ + 64#64) F prk tPrev
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopB1_96` at `b + 0x972e0` (`compress256(esp + 128, esp + 64, 1)`). -/
structure StateLoopB1_96 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "sha2::sha256::compress256")
  common   : ExpandCommon 96 s₀ s
  lr_eq    : s.readReg64 .lr = b + 0x1ac0c#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 128#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 64#64
  x2_eq    : s.readReg64 .x2 = 1#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq   : s.readReg64 .x28 = 14#64
  m0_eq    : s.mem.read64 (esp s₀) = infoPtr + 32#64
  blk_64   : s.mem.readBytes (esp s₀ + 64#64) 64 = tPrev ++ info.take 32
  ist_128  : s.mem.readBytes (esp s₀ + 128#64) 32 = shaStateBytes (hmacInnerInit F prk)
  cnt1_160 : s.mem.read64 (esp s₀ + 160#64) = 2#64
  ost_168  : s.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk)
  cnt2_200 : s.mem.read64 (esp s₀ + 200#64) = 1#64
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopB2_96` at `b + 0x9722c` (`memcpy(esp + 64, infoPtr + 32, 14)`). -/
structure StateLoopB2_96 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8)) (infoPtr : BitVec 64)
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + bv% (ls_off% "memcpy")
  common   : ExpandCommon 96 s₀ s
  lr_eq    : s.readReg64 .lr = b + 0x1ac50#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 64#64
  x1_eq    : s.readReg64 .x1 = infoPtr + 32#64
  x2_eq    : s.readReg64 .x2 = 14#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 rem
  pos_127  : s.mem.read8 (esp s₀ + 127#64) = 14#8
  ist_128  : s.mem.readBytes (esp s₀ + 128#64) 32 =
               shaStateBytes (F (hmacInnerInit F prk) (tPrev ++ info.take 32))
  cnt1_160 : s.mem.read64 (esp s₀ + 160#64) = 2#64
  ost_168  : s.mem.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F prk)
  cnt2_200 : s.mem.read64 (esp s₀ + 200#64) = 1#64
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopB_96` at `b + 0x1aad0` (after `memcpy` of `info.drop 32` and appending `(i + 1)#8`). -/
structure StateLoopB_96 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8))
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + 0x1aad0#64
  common  : ExpandCommon 96 s₀ s
  x19_eq  : s.readReg64 .x19 = BitVec.ofNat 64 i
  x22_eq  : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq  : s.readReg64 .x23 = 32#64
  x24_eq  : s.readReg64 .x24 = 64#64
  x26_eq  : s.readReg64 .x26 = BitVec.ofNat 64 rem
  x28_eq  : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_64 : HmacStGen s.mem (esp s₀ + 64#64) F prk (tPrev ++ info.take 32)
              (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

/-- Cut `LoopC_96` at `b + 0x30680` (`finalize_fixed` entry in loop). -/
structure StateLoopC_96 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (prk info tPrev okmSoFar : List (BitVec 8))
    (i rem dstOff : ℕ) (s₀ s : State) : Prop where
  pc_eq    : s.pc = b + 0x30764#64
  common   : ExpandCommon 96 s₀ s
  lr_eq    : s.readReg64 .lr = b + 0x1ab14#64
  x0_eq    : s.readReg64 .x0 = esp s₀ + 208#64
  x1_eq    : s.readReg64 .x1 = esp s₀ + 240#64
  x19_eq   : s.readReg64 .x19 = BitVec.ofNat 64 i
  x21_eq   : s.readReg64 .x21 = s₀.readReg64 .x2 + BitVec.ofNat 64 (dstOff + 32)
  x22_eq   : s.readReg64 .x22 = s₀.readReg64 .x2 + BitVec.ofNat 64 dstOff
  x23_eq   : s.readReg64 .x23 = 32#64
  x24_eq   : s.readReg64 .x24 = 64#64
  x26_eq   : s.readReg64 .x26 = BitVec.ofNat 64 (rem - 32)
  x28_eq   : s.readReg64 .x28 = esp s₀ + 64#64
  hmac_240 : HmacStGen s.mem (esp s₀ + 240#64) F prk (tPrev ++ info.take 32)
               (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)])
  okm_pre  : s.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar

theorem ExpandCommon.of_write64_esp0_and_low64 {s₀ s s' : State} {v : BitVec 64} {m_mid : Memory}
    (hc : ExpandCommon 96 s₀ s)
    (hstat : s'.status = .Running)
    (hsp   : s'.sp = esp s₀)
    (hx29  : s'.readReg64 .x29 = esp s₀ + 400#64)
    (hx27  : s'.readReg64 .x27 = esp s₀ + 64#64)
    (hx20  : s'.readReg64 .x20 = s₀.readReg64 .x0)
    (hmid  : AgreesOutside s.mem m_mid (esp s₀ + 64#64) 64)
    (hmem' : s'.mem = m_mid.write64 (esp s₀) v) :
    ExpandCommon 96 s₀ s' := by
  have hc_mid : ExpandCommon 96 s₀ (s.setMem m_mid) :=
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 64) hc
      (by rw [State.status_setMem]; exact hc.status)
      (by rw [State.sp_setMem]; exact hc.sp_eq)
      (by rw [State.readReg64_setMem]; exact hc.x29_eq)
      (by rw [State.readReg64_setMem]; exact hc.x27_eq)
      (by rw [State.readReg64_setMem]; exact hc.x20_eq)
      (by rw [mem_setMem]; exact hmid) (by decide)
  have hA0 : AgreesOutside m_mid s'.mem (esp s₀ + 0#64) 8 := by
    rw [hmem', BitVec.add_zero]
    exact (AgreesOutside.rfl' m_mid (esp s₀) 8).write64 (by bv_omega) (by decide)
  have hm8 : s'.mem.read64 (esp s₀ + 8#64) = s₀.readReg64 .x1 := by
    rw [hA0.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc_mid.m8_eq
  have hm16 : s'.mem.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := by
    rw [hA0.read64_eq (by unfold DisjointRegions; bv_omega)]
    exact hc_mid.m16_eq
  exact ⟨hstat, hsp, hx29, hx27, hx20, hm8, hm16,
    ExpandSaved.of_agreesOutside_low hc_mid.saved hA0 (by decide),
    ExpandFrame.of_agreesOutside_esp hc_mid.frame hA0 (by decide)⟩

theorem HmacStGen.of_memcpy14_counter {m₀ : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key tPrev info : List (BitVec 8)} {i : ℕ}
    (ht_len : tPrev.length = 32)
    (hinfo_len : info.length = 46)
    (hist : m₀.readBytes (esp s₀ + 128#64) 32 =
      shaStateBytes (F (hmacInnerInit F key) (tPrev ++ info.take 32)))
    (hcnt1 : m₀.read64 (esp s₀ + 160#64) = 2#64)
    (hout : m₀.readBytes (esp s₀ + 168#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m₀.read64 (esp s₀ + 200#64) = 1#64) :
    let m₁ := m₀.writeBytes (esp s₀ + 64#64) (info.drop 32)
    let c := BitVec.ofNat 8 (i + 1)
    let m₂ :=
      ((m₁.write8 (esp s₀ + 240#64) c).write8 (esp s₀ + 78#64) c).write8 (esp s₀ + 127#64) 15#8
    HmacStGen m₂ (esp s₀ + 64#64) F key (tPrev ++ info.take 32) (info.drop 32 ++ [c]) := by
  intro m₁ c m₂
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by simp [ht_len, hinfo_len]
  have hdrop_len : (info.drop 32).length = 14 := by simp [hinfo_len]
  have hrem_len : (info.drop 32 ++ [c]).length = 15 := by simp [hdrop_len]
  have hA1 : AgreesOutside m₀ m₁ (esp s₀ + 64#64) 14 :=
    agreesOutside_writeBytes_le m₀ (esp s₀ + 64#64) (info.drop 32) 14 (by rw [hdrop_len])
  have hag_w : AgreesOutside m₁ m₂ (esp s₀ + 78#64) 163 := by
    dsimp only [m₂]
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    refine AgreesOutside.write8 ?_ (by simp only [InRegion]; bv_omega)
    exact AgreesOutside.write8 (AgreesOutside.rfl' _ _ _) (by simp only [InRegion]; bv_omega)
  refine ⟨by rw [hblk_len], by rw [hblk_len]; decide, by rw [hrem_len]; decide,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrem_len, show (15 : ℕ) = 14 + 1 from rfl,
        Bytes.readBytes_add m₂ (esp s₀ + 64#64) 14 1,
        show esp s₀ + 64#64 + BitVec.ofNat 64 14 = esp s₀ + 78#64 by bv_lin]
    have h_drop : m₂.readBytes (esp s₀ + 64#64) 14 = info.drop 32 := by
      refine (hag_w.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
      dsimp only [m₁]
      have h := Bytes.readBytes_writeBytes_same m₀ (esp s₀ + 64#64) (info.drop 32) (by omega)
      rwa [hdrop_len] at h
    have h_c : m₂.readBytes (esp s₀ + 78#64) 1 = [c] := by
      dsimp only [Memory.readBytes, m₂]
      rw [Memory.read8_write8_ne (by bv_omega), Memory.read8_write8_same]
    rw [h_drop, h_c]
  · rw [hrem_len, show esp s₀ + 64#64 + 0x3f#64 = esp s₀ + 127#64 by bv_lin]
    dsimp only [m₂]
    exact Memory.read8_write8_same _ _ _
  · rw [show esp s₀ + 64#64 + 0x40#64 = esp s₀ + 128#64 by bv_lin,
        chunks64_single hblk_len, List.foldl]
    dsimp only [m₂]
    refine ((AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    exact (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hist
  · rw [show esp s₀ + 64#64 + 0x60#64 = esp s₀ + 160#64 by bv_lin, hblk_len]
    dsimp only [m₂]
    refine ((AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hcnt1
  · rw [show esp s₀ + 64#64 + 0x68#64 = esp s₀ + 168#64 by bv_lin]
    dsimp only [m₂]
    refine ((AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).readBytes_eq
      (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    exact (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hout
  · rw [show esp s₀ + 64#64 + 0x88#64 = esp s₀ + 200#64 by bv_lin]
    dsimp only [m₂]
    refine ((AgreesOutside.rfl' _ (esp s₀ + 127#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 78#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    refine ((AgreesOutside.rfl' _ (esp s₀ + 240#64) 1 |>.write8 (by simp [InRegion])).read64_eq
      (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hcnt2

theorem HmacStGen.of_copy_esp_64_240 {m₀ m : Memory} {s₀ : State}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks rem : List (BitVec 8)}
    (hsrc : HmacStGen m₀ (esp s₀ + 64#64) F key blocks rem)
    (h0   : m.read64 (esp s₀ + 240#64) = m₀.read64 (esp s₀ + 64#64))
    (h8   : m.read64 (esp s₀ + 248#64) = m₀.read64 (esp s₀ + 72#64))
    (h16  : m.read64 (esp s₀ + 256#64) = m₀.read64 (esp s₀ + 80#64))
    (h24  : m.read64 (esp s₀ + 264#64) = m₀.read64 (esp s₀ + 88#64))
    (h32  : m.read64 (esp s₀ + 272#64) = m₀.read64 (esp s₀ + 96#64))
    (h40  : m.read64 (esp s₀ + 280#64) = m₀.read64 (esp s₀ + 104#64))
    (h48  : m.read64 (esp s₀ + 288#64) = m₀.read64 (esp s₀ + 112#64))
    (h56  : m.read64 (esp s₀ + 296#64) = m₀.read64 (esp s₀ + 120#64))
    (h64  : m.read64 (esp s₀ + 304#64) = m₀.read64 (esp s₀ + 128#64))
    (h72  : m.read64 (esp s₀ + 312#64) = m₀.read64 (esp s₀ + 136#64))
    (h80  : m.read64 (esp s₀ + 320#64) = m₀.read64 (esp s₀ + 144#64))
    (h88  : m.read64 (esp s₀ + 328#64) = m₀.read64 (esp s₀ + 152#64))
    (h96  : m.read64 (esp s₀ + 336#64) = m₀.read64 (esp s₀ + 160#64))
    (h104 : m.read64 (esp s₀ + 344#64) = m₀.read64 (esp s₀ + 168#64))
    (h112 : m.read64 (esp s₀ + 352#64) = m₀.read64 (esp s₀ + 176#64))
    (h120 : m.read64 (esp s₀ + 360#64) = m₀.read64 (esp s₀ + 184#64))
    (h128 : m.read64 (esp s₀ + 368#64) = m₀.read64 (esp s₀ + 192#64))
    (h136 : m.read64 (esp s₀ + 376#64) = m₀.read64 (esp s₀ + 200#64)) :
    HmacStGen m (esp s₀ + 240#64) F key blocks rem :=
  HmacStGen.of_copy_19 hsrc h0
    (read64_add_off h8)
    (read64_add_off h16)
    (read64_add_off h24)
    (read64_add_off h32)
    (read64_add_off h40)
    (read64_add_off h48)
    (read64_add_off h56)
    (read64_add_off h64)
    (read64_add_off h72)
    (read64_add_off h80)
    (read64_add_off h88)
    (read64_add_off h96)
    (read64_add_off h104)
    (read64_add_off h112)
    (read64_add_off h120)
    (read64_add_off h128)
    (read64_add_off h136)


section Trap
variable {C : Crypto} {abs : String → Option (State → State)}


theorem seg0_96_runsTo_trap {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀) :
    RunsTo (trTrapProgAt b C abs) s₀ (StateX0p b 96 s₀) := by
  have hpc := hpre.pc_eq
  have hrun := hpre.status
  have hx3 := hpre.x3_eq
  have hsp_al := hpre.sp_aligned
  have hesp := esp_aligned hsp_al
  have hrw : s₀.mem.RW (esp s₀) 496 := by
    unfold esp; exact hpre.rw_stack.sub (by bv_omega)
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp only [arm64_norm, hpc],
    by rw [State.status_setMem]; simp only [arm64_norm, hrun],
    by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx3],
    ?_, ?_⟩
  · simp only [mem_setMem]
    exact
      { m400 := by simp (config := { decide := true }) only [arm64_norm]
        m408 := by simp (config := { decide := true }) only [arm64_norm]
        m416 := by simp (config := { decide := true }) only [arm64_norm]
        m424 := by simp (config := { decide := true }) only [arm64_norm]
        m432 := by simp (config := { decide := true }) only [arm64_norm]
        m440 := by simp (config := { decide := true }) only [arm64_norm]
        m448 := by simp (config := { decide := true }) only [arm64_norm]
        m456 := by simp (config := { decide := true }) only [arm64_norm]
        m464 := by simp (config := { decide := true }) only [arm64_norm]
        m472 := by simp (config := { decide := true }) only [arm64_norm]
        m480 := by simp (config := { decide := true }) only [arm64_norm]
        m488 := by simp (config := { decide := true }) only [arm64_norm] }
  · exact ExpandFrame.of_agreesOutside_esp (off := 400#64) (sz := 96)
      (Frame.refl s₀.mem _) (by prove_agrees_esp) (by decide)

theorem seg1_96_runsTo_trap {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX0p b 96 s₀ s) :
    RunsTo (trTrapProgAt b C abs) s (StateX1 b C.F prk info infoPtr 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.status
  have hsp := hx.sp_eq
  have hx29 := hx.x29_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hx3 := hx.x3_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 := hpre.readable_x0 hx.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := hpre.readable_x1 hx.frame
  rcases hpre.read64_x0_write64_esp with ⟨h_x0_w0, h_x0_w⟩
  rcases hpre.read64_x1_write_esp with ⟨h_x1_w0, h_x1_w8, _, _⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr :=
    hpre.info_ptr_eq hx.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 :=
    hpre.info_len_eq_46 hx.frame
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (hpre.hmac_x0 hx.frame).2.2.1
  iterate 40 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ⟨hrun, hsp, hx29, rfl, rfl,
     by simp (config := { decide := true }) only [arm64_norm],
     by simp (config := { decide := true }) only [arm64_norm],
     ExpandSaved.of_agreesOutside_low (off := 8#64) (sz := 312) hx.saved
       (by prove_agrees_esp) (by decide),
     ExpandFrame.of_agreesOutside_esp (off := 8#64) (sz := 312) hx.frame
       (by prove_agrees_esp) (by decide)⟩,
    rfl, rfl, rfl,
    by rw [hpre.info_len_eq]; rfl,
    rfl, rfl, rfl, rfl,
    by rw [hpre.info_len_eq]; rfl,
    ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_empty_esp_64 (hpre.hmac_x0 hx.frame)
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
    (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])

theorem seg2a_96_runsTo_trap {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX1 b C.F prk info infoPtr 96 s₀ s) :
    RunsTo (trTrapProgAt b C abs) s (StateX1b b C.F prk info 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 46#64 := by rw [hx.x26_eq, hpre.info_len_eq]
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 : s.readReg64 .x2 = 46#64 := by rw [hx.x2_eq, hpre.info_len_eq]
  have hlr := hx.lr_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) 46 := hrw_esp.sub (by bv_omega)
  have hread_info : s.mem.readBytes infoPtr 46 = info :=
    hpre.info_bytes_eq hx.common.frame
  have hx2_nat : (s.readReg64 .x2).toNat = 46 := by rw [hx2]; rfl
  refine s2_memcpy_step_trap b C abs hrun hpc hx0 hx1 hx2_nat hlr hread_info hrw_dst ?_
  have hA1 : AgreesOutside s.mem (s.mem.writeBytes (esp s₀ + 64#64) info) (esp s₀ + 64#64) 46 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) info 46 (by rw [hpre.info_len_eq])
  have hrw_wb : (s.mem.writeBytes (esp s₀ + 64#64) info).RW (esp s₀) 496 :=
    rw_of_perm_eq hA1.2 hrw_esp
  iterate 13 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem (s.mem.writeBytes (esp s₀ + 64#64) info)) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  refine ⟨by rw [State.pc_setMem]; simp only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ?_⟩
  rw [mem_setMem]
  exact HmacSt.of_memcpy_counter_64_0_46 hx.hmac_64 hpre.info_len_eq

theorem seg2b_96_runsTo_trap {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX1b b C.F prk info 96 s₀ s) :
    RunsTo (trTrapProgAt b C abs) s (StateX2 b C.F prk info 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  iterate 13 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common
      hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx22, hx23, hx26, ?_⟩
  simp only [mem_setMem]
  exact HmacSt.of_copy_esp_64_240 hx.hmac_64
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])
    (by simp (config := { decide := true }) only [arm64_norm])

theorem fin1_96_runsTo_trap {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX2 b C.F prk info 96 s₀ s) :
    RunsTo (trTrapProgAt b C abs) s (StateX2r b C.F prk info 96 s₀) := by
  rcases hpre.fin_side_conditions hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinalizeFixedProof.FinPre b C.F prk (info ++ [1#8]) s :=
    { pc_eq := hx.pc_eq
      status := hx.common.status
      key_le := hpre.prk_le
      msg_lt := by simp [hpre.info_len_eq]
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (FinalizeFixedProof.finalize_fixed_runsTo_trap hfin_pre).mono
    fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  exact ⟨hpc',
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩

theorem seg3_96_runsTo_trap {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX2r b C.F prk info 96 s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoop b 96 (t1 C.F prk info) (t1 C.F prk info) 1 64 32 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 : s.readReg64 .x26 = 64#64 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2) 32 := hrw_x2.sub (by bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_trap b C abs hrun rfl rfl rfl rfl rfl hx.t1_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2) (t1 C.F prk info)
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 0#64) 32 := by
    rw [BitVec.add_zero]
    exact agreesOutside_writeBytes_le s.mem (s₀.readReg64 .x2) (t1 C.F prk info) 32 (by simp)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 9 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    rfl, ?_, ?_⟩
  · simp only [mem_setMem]
    have ht1_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = t1 C.F prk info := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + 0#64) 32 (esp s₀ + 208#64) 32 := by
        rw [BitVec.add_zero]
        exact (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2) ⟨by decide, by bv_omega⟩).sub_right
          (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans hx.t1_208
    exact readBytes_32_esp_32_of_208 ht1_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 32 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
        ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd (by prove_agrees_esp) (by decide) ?_
    conv_lhs => rw [← t1_length C.F prk info]
    exact Bytes.readBytes_writeBytes_same s.mem (s₀.readReg64 .x2) (t1 C.F prk info) (by simp)

/-! ## Loop Body (`T(2)` and `T(3)`) -/

theorem iter_a1_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop b 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoopA1 b C.F prk tPrev okmSoFar 96 i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hread_x0 : s.mem.Readable (s₀.readReg64 .x0) 0x90 := hpre.readable_x0 hx.common.frame
  rcases hpre.read64_x0_write64_esp with ⟨h_x0_w0, h_x0_w⟩
  have hpos_x0 : s.mem.read8 (s₀.readReg64 .x0 + 63#64) = 0#8 :=
    (hpre.hmac_x0 hx.common.frame).2.2.1
  iterate 26 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm, hpc],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 256) hx.common hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    ?_,
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_, ?_⟩
  · rw [State.readReg64_setMem]
    simp (config := { decide := true }) only [arm64_norm]
    rcases hrem with rfl | rfl <;> rfl
  · simp only [mem_setMem]
    exact HmacSt.of_copy_empty_esp_64 (hpre.hmac_x0 hx.common.frame)
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
      (by simp (config := { decide := true }) only [arm64_norm, h_x0_w0, h_x0_w])
  · dsimp only [mem_setMem]
    exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256
      (by unfold DisjointRegions; bv_omega) (by prove_agrees_esp) (by decide) hx.t_cache
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 64#64) 256 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 256 hd (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_a2_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopA1 b C.F prk tPrev okmSoFar 96 i rem dstOff s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoopA2_96 b C.F prk tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hm8 := hx.common.m8_eq
  have hm16 := hx.common.m16_eq
  have hx8 := hx.x8_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := by rw [hx.x23_eq, hmin]
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hread_x1 : s.mem.Readable (s₀.readReg64 .x1) 16 := hpre.readable_x1 hx.common.frame
  rcases hpre.read64_x1_write_esp with ⟨h_x1_w0, h_x1_w8, h_x1_w8_0, h_x1_w8_8⟩
  have hx1_val0 : s.mem.read64 (s₀.readReg64 .x1) = infoPtr := hpre.info_ptr_eq hx.common.frame
  have hx1_val8 : s.mem.read64 (s₀.readReg64 .x1 + 8#64) = 46#64 :=
    hpre.info_len_eq_46 hx.common.frame
  iterate 19 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_write64_esp0_and_low64 hx.common hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) rfl,
    rfl, rfl, rfl, rfl, hx19, hx22, hx23, hx26, rfl,
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_⟩
  · simp only [mem_setMem]
    exact HmacSt.of_write32_empty hx.hmac_64 hx.t_cache ht_len
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd64 : DisjointRegions (esp s₀ + 64#64) 64 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd0 : DisjointRegions (esp s₀ + 0#64) 8 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 0#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      refine readBytes_eq_of_agreesOutside_esp s₀ _ 0#64 8 hd0
        (by rw [BitVec.add_zero]
            exact (AgreesOutside.rfl' _ (esp s₀) 8).write64 (by bv_omega) (by decide))
        (by omega) ?_
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 64#64 64 hd64 (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_b1_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopA2_96 b C.F prk tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoopB1_96 b C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 96#64) 32 := hrw_esp.sub (by bv_omega)
  have hread_info46 : s.mem.readBytes infoPtr 46 = info := hpre.info_bytes_eq hx.common.frame
  have hread_info32 : s.mem.readBytes infoPtr 32 = info.take 32 := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (by rw [hpre.info_len_eq]; exact hread_info46) 0 32 (by rw [hpre.info_len_eq]; decide)
    simpa using h
  have htake32_len : (info.take 32).length = 32 := by simp [hpre.info_len_eq]
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  refine s2_memcpy_step_trap b C abs hrun hpc hx0 hx1 hx2_nat hlr hread_info32 hrw_dst ?_
  generalize hm1_def : s.mem.writeBytes (esp s₀ + 96#64) (info.take 32) = m₁
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 96#64) 32 := by
    rw [← hm1_def]
    exact agreesOutside_writeBytes_le s.mem (esp s₀ + 96#64) (info.take 32) 32 (by rw [htake32_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hcnt1_m1 : m₁.read64 (esp s₀ + 160#64) = 1#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega)]
    have h := hx.hmac_64.2.2.2.2.1
    rwa [show esp s₀ + 64#64 + 0x60#64 = esp s₀ + 160#64 by bv_lin] at h
  have hx27_96 : esp s₀ + 64#64 + 96#64 = esp s₀ + 160#64 := by bv_lin
  have hx27_64 : esp s₀ + 64#64 + 64#64 = esp s₀ + 128#64 := by bv_lin
  iterate 7 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 : AgreesOutside m₁ (m₁.write64 (esp s₀ + 160#64) 2#64) (esp s₀ + 160#64) 8 :=
    agreesOutside_esp_write64 (AgreesOutside.rfl' _ _ _) (by decide)
  have hm0_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀) = infoPtr + 32#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.m0_eq
  have hblk_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 64#64) 64 =
      tPrev ++ info.take 32 := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    rw [Bytes.readBytes_add m₁ (esp s₀ + 64#64) 32 32,
        show esp s₀ + 64#64 + BitVec.ofNat 64 32 = esp s₀ + 96#64 by bv_lin]
    have hleft : m₁.readBytes (esp s₀ + 64#64) 32 = tPrev := by
      refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
      have h := hx.hmac_64.2.1
      rwa [ht_len] at h
    have hright : m₁.readBytes (esp s₀ + 96#64) 32 = info.take 32 := by
      rw [← hm1_def]
      have h := Bytes.readBytes_writeBytes_same s.mem (esp s₀ + 96#64) (info.take 32) (by omega)
      rwa [htake32_len] at h
    rw [hleft, hright]
  have hist_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 128#64) 32 =
      shaStateBytes (hmacInnerInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    have h := hx.hmac_64.2.2.2.1
    rwa [show esp s₀ + 64#64 + 0x40#64 = esp s₀ + 128#64 by bv_lin] at h
  have hcnt1_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀ + 160#64) = 2#64 := by
    simp (config := { decide := true }) only [arm64_norm]
  have host_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (esp s₀ + 168#64) 32 =
      shaStateBytes (hmacOuterInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    refine (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    have h := hx.hmac_64.2.2.2.2.2.1
    rwa [show esp s₀ + 64#64 + 0x68#64 = esp s₀ + 168#64 by bv_lin] at h
  have hcnt2_m2 : (m₁.write64 (esp s₀ + 160#64) 2#64).read64 (esp s₀ + 200#64) = 1#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    refine (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    have h := hx.hmac_64.2.2.2.2.2.2
    rwa [show esp s₀ + 64#64 + 0x88#64 = esp s₀ + 200#64 by bv_lin] at h
  have hokm_m2 :
      (m₁.write64 (esp s₀ + 160#64) 2#64).readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 96#64) 32 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 96#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 160#64) 8 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 160#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)
  refine ⟨by simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 160#64) (sz := 8) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx27_64],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp (config := { decide := true }) only [arm64_norm, hx28],
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hm0_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hblk_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hist_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt1_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact host_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt2_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hokm_m2⟩

theorem iter_b2_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB1_96 b C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoopB2_96 b C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_128 : s.mem.RW (esp s₀ + 128#64) 32 := hrw_esp.sub (by bv_omega)
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by simp [ht_len, hpre.info_len_eq]
  refine s2_compress256_step_trap b C abs hrun hpc hx0 hx1 hx2 hlr
    hx.ist_128 hx.blk_64 hblk_len hrw_128 ?_
  generalize hist_def : shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32)) = ist'
  have hist'_len : ist'.length = 32 := by rw [← hist_def]; exact shaStateBytes_length _
  generalize hm1_def : s.mem.writeBytes (esp s₀ + 128#64) ist' = m₁
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 128#64) 32 := by
    rw [← hm1_def]
    exact agreesOutside_writeBytes_le s.mem (esp s₀ + 128#64) ist' 32 (by rw [hist'_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hm0_m1 : m₁.read64 (esp s₀) = infoPtr + 32#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega), hx.m0_eq]
  iterate 11 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  have hA2 : AgreesOutside m₁ ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8)
      (esp s₀ + 127#64) 1 := by
    refine agreesOutside_esp_write8 ?_ (by decide)
    exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  have hpos_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read8
      (esp s₀ + 127#64) = 14#8 :=
    Memory.read8_write8_same _ _ _
  have hist_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (esp s₀ + 128#64) 32 =
      shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32)) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    rw [← hm1_def, hist_def]
    have h :=
      Bytes.readBytes_writeBytes_same s.mem (esp s₀ + 128#64) ist' (by rw [hist'_len]; decide)
    rwa [hist'_len] at h
  have hcnt1_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read64
      (esp s₀ + 160#64) = 2#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt1_160
  have host_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (esp s₀ + 168#64) 32 =
      shaStateBytes (hmacOuterInit C.F prk) := by
    refine (hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans ?_
    exact (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hx.ost_168
  have hcnt2_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).read64
      (esp s₀ + 200#64) = 1#64 := by
    refine (hA2.read64_eq (by unfold DisjointRegions; bv_omega)).trans ?_
    exact (hA1.read64_eq (by unfold DisjointRegions; bv_omega)).trans hx.cnt2_200
  have hokm_m2 : ((m₁.write8 (esp s₀ + 127#64) 0#8).write8 (esp s₀ + 127#64) 14#8).readBytes
      (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 128#64) 32 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 128#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 127#64) 1 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 127#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)
  refine ⟨by simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 127#64) (sz := 1) hc1
      (by simp only [arm64_norm, hrun])
      (by simp (config := { decide := true }) only [arm64_norm, hsp])
      (by simp (config := { decide := true }) only [arm64_norm, hx29])
      (by simp (config := { decide := true }) only [arm64_norm, hx27])
      (by simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2) (by decide),
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm, hx19],
    by simp (config := { decide := true }) only [arm64_norm, hx22],
    by simp (config := { decide := true }) only [arm64_norm, hx23],
    by simp (config := { decide := true }) only [arm64_norm, hx26],
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hpos_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hist_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt1_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact host_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hcnt2_m2,
    by simp only [State.mem_setPC, State.mem_advancePC, State.mem_writeReg64, mem_setMem]
       exact hokm_m2⟩

theorem iter_b3_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB2_96 b C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoopB_96 b C.F prk info tPrev okmSoFar i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx0 := hx.x0_eq
  have hx1 := hx.x1_eq
  have hx2 := hx.x2_eq
  have hlr := hx.lr_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx26 := hx.x26_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_esp : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  have hrw_dst : s.mem.RW (esp s₀ + 64#64) 14 := hrw_esp.sub (by bv_omega)
  have hread_info46 : s.mem.readBytes infoPtr 46 = info := hpre.info_bytes_eq hx.common.frame
  have hdrop_len : (info.drop 32).length = 14 := by simp [hpre.info_len_eq]
  have hread_info14 : s.mem.readBytes (infoPtr + 32#64) 14 = info.drop 32 := by
    have h := Bytes.readBytes_slice_of_readBytes_eq s.mem infoPtr info
      (by rw [hpre.info_len_eq]; exact hread_info46) 32 14 (by rw [hpre.info_len_eq])
    have htake : (info.drop 32).take 14 = info.drop 32 :=
      List.take_of_length_le (by rw [hdrop_len])
    exact h.trans htake
  have hx2_nat : (s.readReg64 .x2).toNat = 14 := by rw [hx2]; rfl
  refine s2_memcpy_step_trap b C abs hrun hpc hx0 hx1 hx2_nat hlr hread_info14 hrw_dst ?_
  let m₁ := s.mem.writeBytes (esp s₀ + 64#64) (info.drop 32)
  have hA1 : AgreesOutside s.mem m₁ (esp s₀ + 64#64) 14 :=
    agreesOutside_writeBytes_le s.mem (esp s₀ + 64#64) (info.drop 32) 14 (by rw [hdrop_len])
  have hrw_wb : m₁.RW (esp s₀) 496 := rw_of_perm_eq hA1.2 hrw_esp
  have hpos_m1 : m₁.read8 (esp s₀ + 127#64) = 14#8 := by
    rw [hA1.1 (esp s₀ + 127#64) (by simp only [OutsideRegion]; bv_omega), hx.pos_127]
  dsimp only [m₁] at hrw_wb hpos_m1
  have hi_eq : (BitVec.ofNat 64 i == 255#64) = false := by rcases hi with rfl | rfl <;> rfl
  have hi_ne : (BitVec.ofNat 64 i != 255#64) = true := by rcases hi with rfl | rfl <;> rfl
  have hi_cmp : (AddWithCarry64 (BitVec.ofNat 64 i) 18446744073709551360#64 true).2.z = false := by
    rcases hi with rfl | rfl <;> rfl
  have hi_add1 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 i) + 1#32) =
      BitVec.ofNat 64 (i + 1) := by
    rcases hi with rfl | rfl <;> rfl
  iterate 14 s2_step
  refine RunsTo.refl ?_
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    ExpandCommon.of_agreesOutside_low32 hx.common
      (by rw [State.status_setMem]; exact hrun)
      (by rw [State.sp_setMem]; exact hsp)
      (by rw [State.readReg64_setMem]; exact hx29)
      (by rw [State.readReg64_setMem]; exact hx27)
      (by rw [State.readReg64_setMem]; exact hx20)
      (by rw [mem_setMem]; exact hA1) (by decide)
  let c := BitVec.ofNat 8 (i + 1)
  have hA2 : AgreesOutside m₁
      (((m₁.write8 (esp s₀ + 240#64) c).write8 (esp s₀ + 78#64) c).write8 (esp s₀ + 127#64) 15#8)
      (esp s₀ + 64#64) 177 := by
    refine agreesOutside_esp_write8 ?_ (by decide)
    refine agreesOutside_esp_write8 ?_ (by decide)
    exact agreesOutside_esp_write8 (AgreesOutside.rfl' _ _ _) (by decide)
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 64#64) (sz := 177) hc1
      (by rw [State.status_setMem]; simp only [arm64_norm, hrun])
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by simp only [arm64_norm]; exact hA2)
      (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx19],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx22],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx23],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_⟩
  · rw [mem_setMem]
    exact HmacStGen.of_memcpy14_counter ht_len hpre.info_len_eq
      hx.ist_128 hx.cnt1_160 hx.ost_168 hx.cnt2_200
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd1 : DisjointRegions (esp s₀ + 64#64) 14 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      have hd2 : DisjointRegions (esp s₀ + 64#64) 177 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 64#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      simp only [arm64_norm]
      exact (hA2.readBytes_eq hd2 (by omega)).trans
        ((hA1.readBytes_eq hd1 (by omega)).trans hx.okm_pre)

theorem iter_c_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB_96 b C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoopC_96 b C.F prk info tPrev okmSoFar i rem dstOff s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx22 := hx.x22_eq
  have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  iterate 17 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl,
    ExpandCommon.of_agreesOutside_low32 (off := 240#64) (sz := 0x90) hx.common
      hrun hsp hx29 hx27 hx20
      (by prove_agrees_esp) (by decide),
    rfl, rfl, rfl, hx19,
    by rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
    hx22, hx23, hx24,
    by rcases hrem with rfl | rfl <;> rfl,
    hx28, ?_, ?_⟩
  · simp only [mem_setMem]
    exact HmacStGen.of_copy_esp_64_240 hx.hmac_64
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
      (by simp (config := { decide := true }) only [arm64_norm])
  · by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hd : DisjointRegions (esp s₀ + 240#64) 0x90 (s₀.readReg64 .x2) dstOff :=
        (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 240#64)
          ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2)
          ⟨by omega, by bv_omega⟩
      dsimp only [mem_setMem]
      exact readBytes_eq_of_agreesOutside_esp s₀ s.mem 240#64 0x90 hd (by prove_agrees_esp)
        (by omega) hx.okm_pre

theorem iter_fin_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopC_96 b C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoopFin b C.F prk info tPrev okmSoFar 96 i rem dstOff s₀) := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  rcases hpre.fin_side_conditions hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinGenPre b C.F prk (tPrev ++ info.take 32)
      (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := hx.pc_eq
      status := hx.common.status
      key_le := hpre.prk_le
      rem_lt := by simp [hpre.info_len_eq]
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (finalize_fixed_gen_runsTo_trap hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq, List.append_assoc, ← List.append_assoc (info.take 32),
      List.take_append_drop, ← List.append_assoc] at ht
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (Expand.Frame.readBytes_eq hfr (fun r hr => ?_) (by omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 640#64) 640 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2) ⟨by omega, by bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by simp, by unfold esp; bv_omega⟩
  exact ⟨hpc',
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans (by rw [hmin]; exact hx.x21_eq),
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans (by rw [hmin]; exact hx.x23_eq),
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans (by rw [hmin]; exact hx.x26_eq),
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    ht, hokm'⟩

theorem iter_d_continue_96_runsTo_trap {prk info tPrev okmSoFar tNext : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (htNext : tNext = hmacWith C.F prk (tPrev ++ info ++ [2#8]))
    (hx : StateLoopFin b C.F prk info tPrev okmSoFar 96 1 64 32 s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoop b 96 tNext (okmSoFar ++ tNext) 2 32 64 s₀) := by
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [htNext, length_hmacWith]
  clear htNext
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 32#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + 32#64) 32 := hrw_x2.sub (by bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_trap b C abs hrun rfl rfl rfl rfl rfl ht_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + 32#64) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 32#64) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 6 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx24],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx26],
    by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx28],
    ?_, ?_⟩
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (esp s₀ + 208#64) 32 = tNext := by
      have hd : DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (esp s₀ + 208#64) 32 :=
        (hpre.disj_x2_stack.sub_left (s₀.readReg64 .x2 + 32#64) ⟨by decide, by bv_omega⟩).sub_right
          (esp s₀ + 208#64) ⟨by decide, by unfold esp; bv_omega⟩
      exact (hA1.readBytes_eq hd (by decide)).trans ht_208
    exact readBytes_32_esp_32_of_208 ht_m1
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
      (by simp (config := { decide := true }) only [arm64_norm]; rfl)
  · have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 64 :=
      (hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64)
        ⟨by decide, by unfold esp; bv_omega⟩).sub_right (s₀.readReg64 .x2) ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]
    refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp) (by decide) ?_
    rw [show (64 : ℕ) = 32 + 32 from rfl, Bytes.readBytes_add m₁ (s₀.readReg64 .x2) 32 32]
    have hleft : m₁.readBytes (s₀.readReg64 .x2) 32 = okmSoFar := by
      have hd1 : DisjointRegions (s₀.readReg64 .x2 + 32#64) 32 (s₀.readReg64 .x2) 32 := by
        unfold DisjointRegions; bv_omega
      exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
    have hright : m₁.readBytes (s₀.readReg64 .x2 + 32#64) 32 = tNext := by
      have h := Bytes.readBytes_writeBytes_same s.mem (s₀.readReg64 .x2 + 32#64) tNext (by omega)
      rwa [ht_len] at h
    rw [hleft, hright]

theorem iter_d_done_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hokm : okmSoFar ++ hmacWith C.F prk (tPrev ++ info ++ [3#8]) =
              hkdfExpand C.F prk info 96)
    (hx : StateLoopFin b C.F prk info tPrev okmSoFar 96 2 32 64 s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateDone b C.F prk info 96 s₀) := by
  generalize htNext : hmacWith C.F prk (tPrev ++ info ++ [3#8]) = tNext
  have ht_208 : s.mem.readBytes (esp s₀ + 208#64) 32 = tNext := htNext ▸ hx.t_208
  have ht_len : tNext.length = 32 := by rw [← htNext, length_hmacWith]
  rw [htNext] at hokm
  clear htNext
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hx29 := hx.common.x29_eq
  have hx27 := hx.common.x27_eq
  have hx20 := hx.common.x20_eq
  have hx19 := hx.x19_eq
  have hx21 := hx.x21_eq
  have hx22 := hx.x22_eq
  have hx23 : s.readReg64 .x23 = 32#64 := hx.x23_eq
  have hx24 := hx.x24_eq
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq
  have hx28 := hx.x28_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw_x2 : s.mem.RW (s₀.readReg64 .x2) 96 := hpre.rw_x2_frame hx.common.frame
  have hrw_dst : s.mem.RW (s₀.readReg64 .x2 + 64#64) 32 := hrw_x2.sub (by bv_omega)
  iterate 4 s2_step
  refine s2_memcpy_step_trap b C abs hrun rfl rfl rfl rfl rfl ht_208 hrw_dst ?_
  let m₁ := s.mem.writeBytes (s₀.readReg64 .x2 + 64#64) tNext
  have hA1 : AgreesOutside s.mem m₁ (s₀.readReg64 .x2 + 64#64) 32 :=
    agreesOutside_writeBytes_le s.mem _ tNext 32 (by omega)
  have hc1 : ExpandCommon 96 s₀ (s.setMem m₁) :=
    hpre.common_of_agreesOutside_x2 hx.common hrun hsp hx29 hx27 hx20 hA1 ⟨by decide, by decide⟩
  have hm16_1 : m₁.read64 (esp s₀ + 16#64) = esp s₀ + 32#64 := hc1.m16_eq
  have hrw1_esp : m₁.RW (esp s₀) 496 := hpre.rw_esp hc1.frame
  dsimp only [m₁] at hm16_1 hrw1_esp
  iterate 6 s2_step
  refine RunsTo.refl ?_
  refine ⟨by rw [State.pc_setMem]; simp (config := { decide := true }) only [arm64_norm],
    ExpandCommon.of_agreesOutside_low32 (off := 32#64) (sz := 32) hc1 hrun
      (by rw [State.sp_setMem]; simp (config := { decide := true }) only [arm64_norm, hsp])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx29])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx27])
      (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hx20])
      (by prove_agrees_esp) (by decide),
    ?_⟩
  have hd2 : DisjointRegions (esp s₀ + 32#64) 32 (s₀.readReg64 .x2) 96 :=
    hpre.disj_x2_stack.symm.sub_left (esp s₀ + 32#64) ⟨by decide, by unfold esp; bv_omega⟩
  dsimp only [mem_setMem]
  refine readBytes_eq_of_agreesOutside_esp s₀ m₁ 32#64 32 hd2 (by prove_agrees_esp) (by decide) ?_
  rw [show (96 : ℕ) = 64 + 32 from rfl, Bytes.readBytes_add m₁ (s₀.readReg64 .x2) 64 32]
  have hleft : m₁.readBytes (s₀.readReg64 .x2) 64 = okmSoFar := by
    have hd1 : DisjointRegions (s₀.readReg64 .x2 + 64#64) 32 (s₀.readReg64 .x2) 64 := by
      unfold DisjointRegions; bv_omega
    exact (hA1.readBytes_eq hd1 (by decide)).trans hx.okm_pre
  have hright : m₁.readBytes (s₀.readReg64 .x2 + 64#64) 32 = tNext := by
    have h := Bytes.readBytes_writeBytes_same s.mem (s₀.readReg64 .x2 + 64#64) tNext (by omega)
    rwa [ht_len] at h
  rw [hleft, hright, hokm]

theorem epilogue_96_runsTo_trap {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateDone b C.F prk info 96 s₀ s) :
    RunsTo (trTrapProgAt b C abs) s (ExpandPost C.F prk info 96 s₀) := by
  have hpc := hx.pc_eq
  have hrun := hx.common.status
  have hsp := hx.common.sp_eq
  have hesp := esp_aligned hpre.sp_aligned
  have hrw : s.mem.RW (esp s₀) 496 := hpre.rw_esp hx.common.frame
  rcases hx.common.saved with
    ⟨m400, m408, m416, m424, m432, m440, m448, m456, m464, m472, m480, m488⟩
  iterate 8 s2_step
  refine RunsTo.refl ?_
  refine ⟨rfl, hrun, ⟨(esp_eq_add s₀).symm, ?_⟩, hx.okm_all, hx.common.frame⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem iter_to_fin_96_runsTo_trap {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop b 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (trTrapProgAt b C abs) s
      (StateLoopFin b C.F prk info tPrev okmSoFar 96 i rem dstOff s₀) := by
  refine (iter_a1_96_runsTo_trap hpre hrem hdst hx).trans fun s1 hs1 => ?_
  refine (iter_a2_96_runsTo_trap hpre ht_len hrem hdst hs1).trans fun s2 hs2 => ?_
  refine (iter_b1_96_runsTo_trap hpre ht_len hdst hs2).trans fun s3 hs3 => ?_
  refine (iter_b2_96_runsTo_trap hpre ht_len hdst hs3).trans fun s4 hs4 => ?_
  refine (iter_b3_96_runsTo_trap hpre ht_len hi hdst hs4).trans fun s5 hs5 => ?_
  refine (iter_c_96_runsTo_trap hpre hrem hdst hs5).trans fun s6 hs6 => ?_
  exact iter_fin_96_runsTo_trap hpre ht_len hrem hdst hs6

theorem expand_multi_info_96_46_runsTo_trap {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀) :
    RunsTo (trTrapProgAt b C abs) s₀ (ExpandPost C.F prk info 96 s₀) := by
  refine (seg0_96_runsTo_trap hpre).trans fun s1 hs1 => ?_
  refine (seg1_96_runsTo_trap hpre hs1).trans fun s2 hs2 => ?_
  refine (seg2a_96_runsTo_trap hpre hs2).trans fun s3 hs3 => ?_
  refine (seg2b_96_runsTo_trap hpre hs3).trans fun s4 hs4 => ?_
  refine (fin1_96_runsTo_trap hpre hs4).trans fun s5 hs5 => ?_
  refine (seg3_96_runsTo_trap hpre hs5).trans fun s6 hs6 => ?_
  refine (iter_to_fin_96_runsTo_trap hpre (t1_length C.F prk info)
    (Or.inl rfl) (Or.inl rfl) (by decide) hs6).trans fun s7 hs7 => ?_
  refine (iter_d_continue_96_runsTo_trap hpre (tNext := t2 C.F prk info) rfl hs7).trans fun s8 hs8 => ?_
  refine (iter_to_fin_96_runsTo_trap hpre (t2_length C.F prk info)
    (Or.inr rfl) (Or.inr rfl) (by decide) hs8).trans fun s9 hs9 => ?_
  have hokm96 : (t1 C.F prk info ++ t2 C.F prk info) ++
      hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) =
      hkdfExpand C.F prk info 96 := by
    rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
        hkdfExpand_96_eq]
  refine (iter_d_done_96_runsTo_trap hpre hokm96 hs9).trans fun s10 hs10 => ?_
  exact epilogue_96_runsTo_trap hpre hs10

end Trap

section Kit
variable {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}

private theorem runsTo_kit_of_trap {s : State} {Q : State → Prop}
    (hQ : ∀ sf, Q sf → sf.status = .Running)
    (h : RunsTo (trTrapProgAt b C abs) s Q) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s Q := by
  intro hL
  have hL' : (trTrapProgAt b C abs).CodeLoaded s.mem :=
    (trTrapProgAt_codeLoaded_iff b C ctl abs s.mem).mpr hL
  obtain ⟨sf, hs, htr, hq, _⟩ := h hL'
  have hs' : Steps (tripleRatchetProgAt b C ctl abs) s sf :=
    Steps.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) hs (OutcomeStatus.of_running (hQ sf hq))
  exact ⟨sf, hs', htr, hq, hs'.codeLoaded hL⟩

theorem seg0_96_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s₀ (StateX0p b 96 s₀) := runsTo_kit_of_trap (fun _ h => h.status) (seg0_96_runsTo_trap hpre)

theorem seg1_96_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX0p b 96 s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateX1 b C.F prk info infoPtr 96 s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (seg1_96_runsTo_trap hpre hx)

theorem seg2a_96_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX1 b C.F prk info infoPtr 96 s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateX1b b C.F prk info 96 s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (seg2a_96_runsTo_trap hpre hx)

theorem seg2b_96_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX1b b C.F prk info 96 s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateX2 b C.F prk info 96 s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (seg2b_96_runsTo_trap hpre hx)

theorem fin1_96_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX2 b C.F prk info 96 s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (StateX2r b C.F prk info 96 s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (fin1_96_runsTo_trap hpre hx)

theorem seg3_96_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateX2r b C.F prk info 96 s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoop b 96 (t1 C.F prk info) (t1 C.F prk info) 1 64 32 s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (seg3_96_runsTo_trap hpre hx)

theorem iter_a1_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop b 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoopA1 b C.F prk tPrev okmSoFar 96 i rem dstOff s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_a1_96_runsTo_trap hpre hrem hdst hx)

theorem iter_a2_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopA1 b C.F prk tPrev okmSoFar 96 i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoopA2_96 b C.F prk tPrev okmSoFar infoPtr i rem dstOff s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_a2_96_runsTo_trap hpre ht_len hrem hdst hx)

theorem iter_b1_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopA2_96 b C.F prk tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoopB1_96 b C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_b1_96_runsTo_trap hpre ht_len hdst hx)

theorem iter_b2_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB1_96 b C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoopB2_96 b C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_b2_96_runsTo_trap hpre ht_len hdst hx)

theorem iter_b3_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB2_96 b C.F prk info tPrev okmSoFar infoPtr i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoopB_96 b C.F prk info tPrev okmSoFar i rem dstOff s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_b3_96_runsTo_trap hpre ht_len hi hdst hx)

theorem iter_c_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopB_96 b C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoopC_96 b C.F prk info tPrev okmSoFar i rem dstOff s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_c_96_runsTo_trap hpre hrem hdst hx)

theorem iter_fin_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopC_96 b C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoopFin b C.F prk info tPrev okmSoFar 96 i rem dstOff s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_fin_96_runsTo_trap hpre ht_len hrem hdst hx)

theorem iter_d_continue_96_runsTo {prk info tPrev okmSoFar tNext : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (htNext : tNext = hmacWith C.F prk (tPrev ++ info ++ [2#8]))
    (hx : StateLoopFin b C.F prk info tPrev okmSoFar 96 1 64 32 s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoop b 96 tNext (okmSoFar ++ tNext) 2 32 64 s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_d_continue_96_runsTo_trap hpre htNext hx)

theorem iter_d_done_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hokm : okmSoFar ++ hmacWith C.F prk (tPrev ++ info ++ [3#8]) =
              hkdfExpand C.F prk info 96)
    (hx : StateLoopFin b C.F prk info tPrev okmSoFar 96 2 32 64 s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateDone b C.F prk info 96 s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_d_done_96_runsTo_trap hpre hokm hx)

theorem epilogue_96_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (hx : StateDone b C.F prk info 96 s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s (ExpandPost C.F prk info 96 s₀) := runsTo_kit_of_trap (fun _ h => h.2.1) (epilogue_96_runsTo_trap hpre hx)

theorem iter_to_fin_96_runsTo {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop b 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s
      (StateLoopFin b C.F prk info tPrev okmSoFar 96 i rem dstOff s₀) := runsTo_kit_of_trap (fun _ h => h.common.status) (iter_to_fin_96_runsTo_trap hpre ht_len hi hrem hdst hx)

/-- Full `RunsTo` assembly for `expand_multi_info` (`b + 0x1a874`) when `okmLen = 96` and
`info.length = 46`. -/
theorem expand_multi_info_96_46_runsTo {prk info : List (BitVec 8)} {infoPtr : BitVec 64}
    {s₀ : State}
    (hpre : ExpandPre96_46 b C.F prk info infoPtr s₀) :
    RunsTo (tripleRatchetProgAt b C ctl abs) s₀ (ExpandPost C.F prk info 96 s₀) := runsTo_kit_of_trap (fun _ h => h.2.1) (expand_multi_info_96_46_runsTo_trap hpre)

end Kit

end CryptoVerification.E2E.Pqxdh.ResponderCore
