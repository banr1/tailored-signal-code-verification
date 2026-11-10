/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace CryptoVerification.LibsignalSession.CryptoHmacSha256

open Arm64 ProofLib CryptoGames CryptoGames.HMAC
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/-! ## Saved Callee-Saved Registers (`[hsp + 0x180, hsp + 0x1e0)`) -/

def HmacSaved (s₀ : State) (hsp : BitVec 64) (m : Memory) : Prop :=
  m.read64 (hsp + 384#64) = s₀.readReg64 .x29 ∧
  m.read64 (hsp + 392#64) = s₀.readReg64 .lr ∧
  m.read64 (hsp + 400#64) = s₀.readReg64 .x28 ∧
  m.read64 (hsp + 416#64) = s₀.readReg64 .x26 ∧
  m.read64 (hsp + 424#64) = s₀.readReg64 .x25 ∧
  m.read64 (hsp + 432#64) = s₀.readReg64 .x24 ∧
  m.read64 (hsp + 440#64) = s₀.readReg64 .x23 ∧
  m.read64 (hsp + 448#64) = s₀.readReg64 .x22 ∧
  m.read64 (hsp + 456#64) = s₀.readReg64 .x21 ∧
  m.read64 (hsp + 464#64) = s₀.readReg64 .x20 ∧
  m.read64 (hsp + 472#64) = s₀.readReg64 .x19

theorem HmacSaved.of_agreesOutside {s₀ : State} {hsp : BitVec 64} {m₁ m₂ : Memory}
    {base : BitVec 64} {len : ℕ}
    (hs : HmacSaved s₀ hsp m₁)
    (hag : AgreesOutside m₁ m₂ base len)
    (hd : DisjointRegions base len (hsp + 384#64) 96) :
    HmacSaved s₀ hsp m₂ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have sub8 (off : BitVec 64) (hoff : (off - (hsp + 384#64)).toNat + 8 ≤ 96) :
      DisjointRegions base len off 8 :=
    hd.sub_right off ⟨by decide, hoff⟩
  exact ⟨(hag.read64_eq (sub8 (hsp + 384#64) (by clear * -; bv_omega))).trans h1,
         (hag.read64_eq (sub8 (hsp + 392#64) (by clear * -; bv_omega))).trans h2,
         (hag.read64_eq (sub8 (hsp + 400#64) (by clear * -; bv_omega))).trans h3,
         (hag.read64_eq (sub8 (hsp + 416#64) (by clear * -; bv_omega))).trans h4,
         (hag.read64_eq (sub8 (hsp + 424#64) (by clear * -; bv_omega))).trans h5,
         (hag.read64_eq (sub8 (hsp + 432#64) (by clear * -; bv_omega))).trans h6,
         (hag.read64_eq (sub8 (hsp + 440#64) (by clear * -; bv_omega))).trans h7,
         (hag.read64_eq (sub8 (hsp + 448#64) (by clear * -; bv_omega))).trans h8,
         (hag.read64_eq (sub8 (hsp + 456#64) (by clear * -; bv_omega))).trans h9,
         (hag.read64_eq (sub8 (hsp + 464#64) (by clear * -; bv_omega))).trans h10,
         (hag.read64_eq (sub8 (hsp + 472#64) (by clear * -; bv_omega))).trans h11⟩

theorem HmacSaved.of_frame {s₀ : State} {hsp : BitVec 64} {m₁ m₂ : Memory}
    {rs : List (BitVec 64 × ℕ)}
    (hs : HmacSaved s₀ hsp m₁)
    (hf : Frame m₁ m₂ rs)
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 (hsp + 384#64) 96) :
    HmacSaved s₀ hsp m₂ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have sub8 (off : BitVec 64) (hoff : (off - (hsp + 384#64)).toNat + 8 ≤ 96) :
      ∀ r ∈ rs, DisjointRegions r.1 r.2 off 8 :=
    fun r hr => (hd r hr).sub_right off ⟨by decide, hoff⟩
  exact ⟨(hf.read64_eq (sub8 (hsp + 384#64) (by clear * -; bv_omega))).trans h1,
         (hf.read64_eq (sub8 (hsp + 392#64) (by clear * -; bv_omega))).trans h2,
         (hf.read64_eq (sub8 (hsp + 400#64) (by clear * -; bv_omega))).trans h3,
         (hf.read64_eq (sub8 (hsp + 416#64) (by clear * -; bv_omega))).trans h4,
         (hf.read64_eq (sub8 (hsp + 424#64) (by clear * -; bv_omega))).trans h5,
         (hf.read64_eq (sub8 (hsp + 432#64) (by clear * -; bv_omega))).trans h6,
         (hf.read64_eq (sub8 (hsp + 440#64) (by clear * -; bv_omega))).trans h7,
         (hf.read64_eq (sub8 (hsp + 448#64) (by clear * -; bv_omega))).trans h8,
         (hf.read64_eq (sub8 (hsp + 456#64) (by clear * -; bv_omega))).trans h9,
         (hf.read64_eq (sub8 (hsp + 464#64) (by clear * -; bv_omega))).trans h10,
         (hf.read64_eq (sub8 (hsp + 472#64) (by clear * -; bv_omega))).trans h11⟩

/-! ## Stack Frame and Preconditions (`0x20b88`) -/

def hsp (s₀ : State) : BitVec 64 := s₀.sp - 480#64

theorem hsp_align {s₀ : State} (h : (s₀.sp &&& 0b1111#64) = 0#64) :
    (hsp s₀ &&& 0b1111#64) = 0#64 := by
  unfold hsp; bv_bits

theorem hsp_eq_add (s₀ : State) : s₀.sp = hsp s₀ + 480#64 := by
  unfold hsp; bv_omega

theorem hsp_sub_544_eq (s₀ : State) : hsp s₀ - 544#64 = s₀.sp - 1024#64 := by
  unfold hsp; bv_omega

structure HmacPre (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key inp : List (BitVec 8)) (s₀ : State) : Prop where
  pc_eq          : s₀.pc = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256")
  status         : s₀.status = .Running
  sp_aligned     : (s₀.sp &&& 0b1111#64) = 0#64
  base_aligned   : (b &&& 0xfff#64) = 0#64
  x2_eq          : s₀.readReg64 .x2 = 32#64
  x4_eq          : s₀.readReg64 .x4 = 1#64
  key_len        : key.length = 32
  inp_len        : inp.length = 1
  key_eq         : s₀.mem.readBytes (s₀.readReg64 .x1) 32 = key
  inp_eq         : s₀.mem.readBytes (s₀.readReg64 .x3) 1 = inp
  iv_eq          : s₀.mem.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV
  read_iv        : s₀.mem.Readable (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32
  read_inp       : s₀.mem.Readable (s₀.readReg64 .x3) 1
  rw_out         : RW s₀.mem (s₀.readReg64 .x0) 32
  rw_stack       : RW s₀.mem (s₀.sp - 1024#64) 1024
  disj_iv_stack  : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (s₀.sp - 1024#64) 1024
  disj_out_stack : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.sp - 1024#64) 1024
  disj_key_stack : DisjointRegions (s₀.readReg64 .x1) 32 (s₀.sp - 1024#64) 1024
  disj_inp_stack : DisjointRegions (s₀.readReg64 .x3) 1 (s₀.sp - 1024#64) 1024

structure HmacCommon (s₀ s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x29_eq : s.readReg64 .x29 = hsp s₀ + 384#64
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  saved  : HmacSaved s₀ (hsp s₀) s.mem
  frame  : Frame s₀.mem s.mem [(s₀.sp - 1024#64, 1024)]

structure StateH1 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 52)
  common  : HmacCommon s₀ s
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s₀.readReg64 .x3
  x21_eq  : s.readReg64 .x21 = 1#64
  tag_eq  : s.mem.read64 (hsp s₀ + 144#64) = 0#64
  hmac_st : HmacSt s.mem (hsp s₀ + 152#64) F key []

theorem Frame.of_agreesOutside_stack1024 {sp : BitVec 64} {m₀ m₁ m₂ : Memory}
    {base : BitVec 64} {len : ℕ}
    (hf : Frame m₀ m₁ [(sp - 1024#64, 1024)])
    (hag : AgreesOutside m₁ m₂ base len)
    (hsub : (base - (sp - 1024#64)).toNat + len ≤ 1024 := by clear * -; (try unfold hsp); bv_omega) :
    Frame m₀ m₂ [(sp - 1024#64, 1024)] :=
  hf.trans_agreesOutside_sub (b := sp - 1024#64) (n := 1024) (by simp) hsub hag

theorem Frame.write8_stack1024 {sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(sp - 1024#64, 1024)])
    (a : BitVec 64) (v : BitVec 8)
    (ha : (a - (sp - 1024#64)).toNat + 1 ≤ 1024 := by clear * -; (try unfold hsp); bv_omega) :
    Frame m₀ (m.write8 a v) [(sp - 1024#64, 1024)] :=
  Frame.of_agreesOutside_stack1024 hf (AgreesOutside.write8_self m a v) ha

theorem Frame.write64_stack1024 {sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(sp - 1024#64, 1024)])
    (a v : BitVec 64)
    (ha : (a - (sp - 1024#64)).toNat + 8 ≤ 1024 := by clear * -; (try unfold hsp); bv_omega) :
    Frame m₀ (m.write64 a v) [(sp - 1024#64, 1024)] :=
  Frame.of_agreesOutside_stack1024 hf (AgreesOutside.write64_self m a v) ha

theorem Frame.writeBytes_stack1024 {sp : BitVec 64} {m₀ m : Memory}
    (hf : Frame m₀ m [(sp - 1024#64, 1024)])
    (a : BitVec 64) (bs : List (BitVec 8))
    (ha : (a - (sp - 1024#64)).toNat + bs.length ≤ 1024 := by clear * -; (try unfold hsp); bv_omega) :
    Frame m₀ (m.writeBytes a bs) [(sp - 1024#64, 1024)] :=
  Frame.of_agreesOutside_stack1024 hf (AgreesOutside.writeBytes_self m a bs) ha

theorem Frame.trans_nfs {s₀ : State} {m₀ m₁ m₂ : Memory}
    (hf1 : Frame m₀ m₁ [(s₀.sp - 1024#64, 1024)])
    (hf2 : Frame m₁ m₂ [(hsp s₀ + 144#64, 0x98), (hsp s₀ - 544#64, 544)]) :
    Frame m₀ m₂ [(s₀.sp - 1024#64, 1024)] := by
  refine Frame.trans hf1 (Frame.mono hf2 fun a ha r hr => ?_)
  have h1 := ha (s₀.sp - 1024#64, 1024) (by simp)
  clear * - h1 hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (unfold hsp OutsideRegion at h1 ⊢; bv_omega)

attribute [local arm64_norm]
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds

structure StateH0 (b : BitVec 64) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]")
  common : HmacCommon s₀ s
  x0_eq  : s.readReg64 .x0 = hsp s₀ + 144#64
  x1_eq  : s.readReg64 .x1 = s₀.readReg64 .x1
  x2_eq  : s.readReg64 .x2 = 32#64
  lr_eq  : s.readReg64 .lr = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 52)
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s₀.readReg64 .x3
  x21_eq : s.readReg64 .x21 = 1#64

theorem seg0a_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key inp : List (BitVec 8)} {s₀ : State}
    (hpre : HmacPre b F key inp s₀) :
    RunsTo (P b F alloc) s₀ (StateH0 b s₀) := by
  generalize hPost : StateH0 b s₀ = Post
  have hpc := hpre.pc_eq
  have hstat := hpre.status
  have hal0 := hpre.sp_aligned
  have hal_hsp : ((s₀.sp - 480#64) &&& 0b1111#64) = 0#64 := hsp_align hal0
  have hrw_hsp : s₀.mem.RW (s₀.sp - 480#64) 480 :=
    hpre.rw_stack.sub (by clear * -; bv_omega)
  iterate 13 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine {
    pc_eq := by simp only [arm64_norm, hpc]
    common := {
      status := hstat
      sp_eq := by simp only [arm64_norm, hsp]
      x29_eq := by simp only [arm64_norm, hsp]
      x27_eq := by simp only [arm64_norm]
      saved := by
        dsimp only [HmacSaved, hsp, State.setMem, State.writeReg64, State.setPC, State.advancePC]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
      frame := by
        dsimp only [State.setMem, State.writeReg64, State.setPC, State.advancePC]
        repeat refine Frame.write64_stack1024 ?_ _ _
        exact Frame.refl s₀.mem _
    }
    x0_eq := by simp only [arm64_norm, hsp]
    x1_eq := by simp only [arm64_norm]
    x2_eq := by simp only [arm64_norm, hpre.x2_eq]
    lr_eq := by simp only [arm64_norm, hpc]
    x19_eq := by simp only [arm64_norm]
    x20_eq := by simp only [arm64_norm]
    x21_eq := by simp only [arm64_norm, hpre.x4_eq]
  }

theorem seg0b_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key inp : List (BitVec 8)} {s₀ sc : State}
    (hpre : HmacPre b F key inp s₀)
    (hsc : StateH0 b s₀ sc) :
    RunsTo (P b F alloc) sc (StateH1 b F key s₀) := by
  rcases hsc with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
    hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hkey_c : sc.mem.readBytes (sc.readReg64 .x1) (sc.readReg64 .x2).toNat = key := by
    rw [hx1_c, hx2_c, show (32#64 : BitVec 64).toNat = 32 from rfl]
    rw [hframe_c.readBytes_eq (by simp [hpre.disj_key_stack.symm]) (by decide), hpre.key_eq]
  have hiv_c : sc.mem.readBytes (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV := by
    rw [hframe_c.readBytes_eq (by simp [hpre.disj_iv_stack.symm]) (by decide), hpre.iv_eq]
  have hread_iv_c : sc.mem.Readable (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 :=
    (hframe_c.readable_iff _ _).mpr hpre.read_iv
  have hrw_stack_c : RW sc.mem (s₀.sp - 1024#64) 1024 :=
    (hframe_c.rw_iff _ _).mpr hpre.rw_stack
  have hdisj_iv_nfs : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (sc.sp - 544#64) 544 := by
    rw [hsp_c, hsp_sub_544_eq]
    exact hpre.disj_iv_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hrw_out_nfs : RW sc.mem (sc.readReg64 .x0) 0x98 := by
    rw [hx0_c]
    exact hrw_stack_c.sub (by clear * -; unfold hsp; bv_omega)
  have hrw_stack_nfs : RW sc.mem (sc.sp - 544#64) 544 := by
    rw [hsp_c, hsp_sub_544_eq]
    exact hrw_stack_c.sub (by clear * -; bv_omega)
  have hdisj_out_nfs : DisjointRegions (sc.readReg64 .x0) 0x98 (sc.sp - 544#64) 544 := by
    rw [hx0_c, hsp_c]
    clear * -; unfold hsp DisjointRegions; bv_omega
  have hdisj_key_nfs : DisjointRegions (sc.readReg64 .x1) (sc.readReg64 .x2).toNat (sc.sp - 544#64) 544 := by
    rw [hx1_c, hx2_c, hsp_c, hsp_sub_544_eq, show (32#64 : BitVec 64).toNat = 32 from rfl]
    exact hpre.disj_key_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  refine (new_from_slice_run hpc_c hstat_c (by rw [hx2_c]; decide) hiv_c hpre.base_aligned
    hread_iv_c hdisj_iv_nfs hrw_out_nfs hrw_stack_nfs hdisj_out_nfs (Or.inr hdisj_key_nfs)
    (by rw [hsp_c]; exact hal_hsp)).mono fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩
  rw [hlr_c] at hpc1
  rw [hx0_c] at htag1 hhmac1 hframe1
  rw [hsp_c] at hframe1
  rw [hkey_c] at hhmac1
  have h19 : s₁.readReg64 .x19 = sc.readReg64 .x19 := hcs1.2 .x19 (by simp)
  have h20 : s₁.readReg64 .x20 = sc.readReg64 .x20 := hcs1.2 .x20 (by simp)
  have h21 : s₁.readReg64 .x21 = sc.readReg64 .x21 := hcs1.2 .x21 (by simp)
  have h27 : s₁.readReg64 .x27 = sc.readReg64 .x27 := hcs1.2 .x27 (by simp)
  have h29 : s₁.readReg64 .x29 = sc.readReg64 .x29 := hcs1.2 .x29 (by simp)
  have hhmac_addr : hsp s₀ + 144#64 + 8#64 = hsp s₀ + 152#64 := by clear * -; bv_omega
  rw [hhmac_addr] at hhmac1
  refine {
    pc_eq := hpc1
    common := {
      status := hstat1
      sp_eq := hcs1.1.trans hsp_c
      x29_eq := h29.trans hx29_c
      x27_eq := h27.trans hx27_c
      saved := HmacSaved.of_frame hsaved_c hframe1 (by
        intro r hr
        clear * - hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; bv_omega))
      frame := Frame.trans_nfs hframe_c hframe1
    }
    x19_eq := h19.trans hx19_c
    x20_eq := h20.trans hx20_c
    x21_eq := h21.trans hx21_c
    tag_eq := htag1
    hmac_st := hhmac1
  }

theorem seg0_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key inp : List (BitVec 8)} {s₀ : State}
    (hpre : HmacPre b F key inp s₀) :
    RunsTo (P b F alloc) s₀ (StateH1 b F key s₀) :=
  (seg0a_runsTo hpre).trans (fun _ hsc => seg0b_runsTo hpre hsc)

/-! ## Post-`new_from_slice` Copy Segment (`0x20bbc → 0x20c28`) -/

private theorem extractLsb'_read64_all (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 0 8 = m.read8 a ∧
    (m.read64 a).extractLsb' 8 8 = m.read8 (a + 1#64) ∧
    (m.read64 a).extractLsb' 16 8 = m.read8 (a + 2#64) ∧
    (m.read64 a).extractLsb' 24 8 = m.read8 (a + 3#64) ∧
    (m.read64 a).extractLsb' 32 8 = m.read8 (a + 4#64) ∧
    (m.read64 a).extractLsb' 40 8 = m.read8 (a + 5#64) ∧
    (m.read64 a).extractLsb' 48 8 = m.read8 (a + 6#64) ∧
    (m.read64 a).extractLsb' 56 8 = m.read8 (a + 7#64) := by
  have h := toLEBytes_8_read64_eq m a
  rw [toLEBytes_8_eq_list, readBytes_8_eq] at h
  simpa only [List.cons.injEq, and_true] using h

@[scoped simp, arm64_norm]
theorem extractLsb'_0_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 0 8 = m.read8 a :=
  (extractLsb'_read64_all m a).1

@[scoped simp, arm64_norm]
theorem extractLsb'_8_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 8 8 = m.read8 (a + 1#64) :=
  (extractLsb'_read64_all m a).2.1

@[scoped simp, arm64_norm]
theorem extractLsb'_16_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 16 8 = m.read8 (a + 2#64) :=
  (extractLsb'_read64_all m a).2.2.1

@[scoped simp, arm64_norm]
theorem extractLsb'_24_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 24 8 = m.read8 (a + 3#64) :=
  (extractLsb'_read64_all m a).2.2.2.1

@[scoped simp, arm64_norm]
theorem extractLsb'_32_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 32 8 = m.read8 (a + 4#64) :=
  (extractLsb'_read64_all m a).2.2.2.2.1

@[scoped simp, arm64_norm]
theorem extractLsb'_40_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 40 8 = m.read8 (a + 5#64) :=
  (extractLsb'_read64_all m a).2.2.2.2.2.1

@[scoped simp, arm64_norm]
theorem extractLsb'_48_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 48 8 = m.read8 (a + 6#64) :=
  (extractLsb'_read64_all m a).2.2.2.2.2.2.1

@[scoped simp, arm64_norm]
theorem extractLsb'_56_8_read64 (m : Memory) (a : BitVec 64) :
    (m.read64 a).extractLsb' 56 8 = m.read8 (a + 7#64) :=
  (extractLsb'_read64_all m a).2.2.2.2.2.2.2

theorem readBytes_16_eq_read64 (m : Memory) (a : BitVec 64) :
    m.readBytes a 16 =
      toLEBytes 8 (m.read64 a) ++ toLEBytes 8 (m.read64 (a + 8#64)) := by
  rw [toLEBytes_8_read64_eq, toLEBytes_8_read64_eq]
  exact LibsignalAesCbc.Run.Bytes.readBytes_add m a 8 8

theorem readBytes_32_eq_read64 (m : Memory) (a : BitVec 64) :
    m.readBytes a 32 =
      toLEBytes 8 (m.read64 a) ++ toLEBytes 8 (m.read64 (a + 8#64)) ++
      toLEBytes 8 (m.read64 (a + 16#64)) ++ toLEBytes 8 (m.read64 (a + 24#64)) := by
  have h24 : (a + 16#64) + 8#64 = a + 24#64 := by clear * -; bv_omega
  rw [← h24, List.append_assoc (toLEBytes 8 (m.read64 a) ++ toLEBytes 8 (m.read64 (a + 8#64))),
      ← readBytes_16_eq_read64, ← readBytes_16_eq_read64]
  exact LibsignalAesCbc.Run.Bytes.readBytes_add m a 16 16

theorem readBytes_32_off_eq_read64 (m : Memory) (base off : BitVec 64) :
    m.readBytes (base + off) 32 =
      toLEBytes 8 (m.read64 (base + off)) ++
      toLEBytes 8 (m.read64 (base + (off + 8#64))) ++
      toLEBytes 8 (m.read64 (base + (off + 16#64))) ++
      toLEBytes 8 (m.read64 (base + (off + 24#64))) := by
  rw [readBytes_32_eq_read64]
  simp only [BitVec.add_assoc]

theorem readBytes_64_eq_read64 (m : Memory) (a : BitVec 64) :
    m.readBytes a 64 =
      toLEBytes 8 (m.read64 a) ++ toLEBytes 8 (m.read64 (a + 8#64)) ++
      toLEBytes 8 (m.read64 (a + 16#64)) ++ toLEBytes 8 (m.read64 (a + 24#64)) ++
      toLEBytes 8 (m.read64 (a + 32#64)) ++ toLEBytes 8 (m.read64 (a + 40#64)) ++
      toLEBytes 8 (m.read64 (a + 48#64)) ++ toLEBytes 8 (m.read64 (a + 56#64)) := by
  have h64 : m.readBytes a 64 = m.readBytes a 32 ++ m.readBytes (a + 32#64) 32 :=
    LibsignalAesCbc.Run.Bytes.readBytes_add m a 32 32
  have h1 : (a + 32#64) + 8#64 = a + 40#64 := by clear * -; bv_omega
  have h2 : (a + 32#64) + 16#64 = a + 48#64 := by clear * -; bv_omega
  have h3 : (a + 32#64) + 24#64 = a + 56#64 := by clear * -; bv_omega
  rw [h64, readBytes_32_eq_read64 m a, readBytes_32_eq_read64 m (a + 32#64), h1, h2, h3]
  simp only [List.append_assoc]

theorem readBytes_64_off_eq_read64 (m : Memory) (base off : BitVec 64) :
    m.readBytes (base + off) 64 =
      toLEBytes 8 (m.read64 (base + off)) ++
      toLEBytes 8 (m.read64 (base + (off + 8#64))) ++
      toLEBytes 8 (m.read64 (base + (off + 16#64))) ++
      toLEBytes 8 (m.read64 (base + (off + 24#64))) ++
      toLEBytes 8 (m.read64 (base + (off + 32#64))) ++
      toLEBytes 8 (m.read64 (base + (off + 40#64))) ++
      toLEBytes 8 (m.read64 (base + (off + 48#64))) ++
      toLEBytes 8 (m.read64 (base + (off + 56#64))) := by
  rw [readBytes_64_eq_read64]
  simp only [BitVec.add_assoc]

structure StateH1m (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memcpy")
  common  : HmacCommon s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀
  x1_eq   : s.readReg64 .x1 = s₀.readReg64 .x3
  x2_eq   : s.readReg64 .x2 = 1#64
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 164)
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x21_eq  : s.readReg64 .x21 = 1#64
  x22_eq  : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq  : s.readReg64 .x23 = hsp s₀
  x25_eq  : s.readReg64 .x25 = 0#64
  ist_eq  : s.mem.readBytes (hsp s₀ + 64#64) 32 = shaStateBytes (innerState F key)
  ibl_eq  : s.mem.read64 (hsp s₀ + 96#64) = 1#64
  ost_eq  : s.mem.readBytes (hsp s₀ + 104#64) 32 = shaStateBytes (outerState F key)
  obl_eq  : s.mem.read64 (hsp s₀ + 136#64) = 1#64

theorem seg1a_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key inp : List (BitVec 8)} {s₀ s : State}
    (hpre : HmacPre b F key inp s₀)
    (hs : StateH1 b F key s₀ s) :
    RunsTo (P b F alloc) s (StateH1m b F key s₀) := by
  generalize hPost : StateH1m b F key s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩, hx19, hx20, hx21, htag, hhmac⟩
  rcases hhmac with ⟨_, _, hpos, hin, hibl, hout, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hpos' : s.mem.read8 (hsp s₀ + 215#64) = 0#8 := by
    have ha : hsp s₀ + 152#64 + 0x3f#64 = hsp s₀ + 215#64 := by clear * -; bv_omega
    rw [← ha]; exact hpos
  have hin' : s.mem.readBytes (hsp s₀ + 216#64) 32 = shaStateBytes (innerState F key) := by
    have ha : hsp s₀ + 152#64 + 0x40#64 = hsp s₀ + 216#64 := by clear * -; bv_omega
    rw [← ha]; exact hin
  have hibl' : s.mem.read64 (hsp s₀ + 248#64) = 1#64 := by
    have ha : hsp s₀ + 152#64 + 0x60#64 = hsp s₀ + 248#64 := by clear * -; bv_omega
    rw [← ha]; exact hibl
  have hout' : s.mem.readBytes (hsp s₀ + 256#64) 32 = shaStateBytes (outerState F key) := by
    have ha : hsp s₀ + 152#64 + 0x68#64 = hsp s₀ + 256#64 := by clear * -; bv_omega
    rw [← ha]; exact hout
  have hobl' : s.mem.read64 (hsp s₀ + 288#64) = 1#64 := by
    have ha : hsp s₀ + 152#64 + 0x88#64 = hsp s₀ + 288#64 := by clear * -; bv_omega
    rw [← ha]; exact hobl
  iterate 28 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine {
    pc_eq := by simp only [arm64_norm, hpc]
    common := {
      status := hstat
      sp_eq := by simp only [arm64_norm, hsp_eq]
      x29_eq := by simp only [arm64_norm, hx29]
      x27_eq := by simp only [arm64_norm, hx27]
      saved := by
        rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
        dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32,
          State.writeVReg128, State.setPState, State.setPC, State.advancePC]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm,
            s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
      frame := by
        dsimp only [State.setMem, State.writeReg64, State.writeReg32,
          State.writeVReg128, State.setPState, State.setPC, State.advancePC]
        repeat refine Frame.write64_stack1024 ?_ _ _
        exact hframe
    }
    x0_eq := by simp only [arm64_norm]
    x1_eq := by simp only [arm64_norm, hx20]
    x2_eq := by simp only [arm64_norm, hx21]
    lr_eq := by simp only [arm64_norm, hpc]
    x19_eq := by simp only [arm64_norm, hx19]
    x21_eq := by simp only [arm64_norm, hx21]
    x22_eq := by simp only [arm64_norm]
    x23_eq := by simp only [arm64_norm]
    x25_eq := by simp only [arm64_norm]
    ist_eq := by
      dsimp only [State.setMem, State.writeReg64, State.writeReg32,
        State.writeVReg128, State.setPState, State.setPC, State.advancePC]
      rw [← hin']
      refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 64#64) (hsp s₀ + 216#64)
        ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
    ibl_eq := by
      dsimp only [State.setMem, State.writeReg64, State.writeReg32,
        State.writeVReg128, State.setPState, State.setPC, State.advancePC]
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hibl']
    ost_eq := by
      dsimp only [State.setMem, State.writeReg64, State.writeReg32,
        State.writeVReg128, State.setPState, State.setPC, State.advancePC]
      rw [← hout']
      refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 104#64) (hsp s₀ + 256#64)
        ?_ ?_ ?_ ?_ <;>
        simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
    obl_eq := by
      dsimp only [State.setMem, State.writeReg64, State.writeReg32,
        State.writeVReg128, State.setPState, State.setPC, State.advancePC]
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl']
  }

/-! ## `memcpy`, Input Absorption, and `memset` (`0x20c2c → 0x20d0c`) -/

private theorem add_sub_add_left_bv (a b c : BitVec 64) : (a + b) - (a + c) = b - c := by
  have h : a + b = (b - c) + (a + c) := by
    rw [BitVec.add_comm (b - c) (a + c), BitVec.add_assoc,
        BitVec.add_comm c (b - c), BitVec.sub_add_cancel]
  rw [h, BitVec.add_sub_cancel]

private theorem add_sub_cancel_bv (base off1 off2 : BitVec 64) :
    base + off2 = (base + off1) + BitVec.ofNat 64 (off2 - off1).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc,
      BitVec.add_comm off1 (off2 - off1), BitVec.sub_add_cancel]

private theorem add_off_k_bv (base off1 off2 : BitVec 64) (k : ℕ) :
    (base + off2) + BitVec.ofNat 64 k =
      (base + off1) + BitVec.ofNat 64 ((off2 - off1).toNat + k) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← add_sub_cancel_bv]

theorem writeBytes_singleton (m : Memory) (a : BitVec 64) (b : BitVec 8) :
    m.writeBytes a [b] = m.write8 a b := rfl

theorem read8_writeBytes_off_outside (m : Memory) (base off1 off2 : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length ≤ (off2 - off1).toNat := by decide) :
    (m.writeBytes (base + off1) bs).read8 (base + off2) = m.read8 (base + off2) := by
  apply ProofLib.read8_writeBytes_outside
  unfold OutsideRegion
  rw [add_sub_add_left_bv]; exact h

theorem read8_writeBytes_replicate_off (m : Memory) (base off1 off2 : BitVec 64) (n : ℕ) (v : BitVec 8)
    (h : (off2 - off1).toNat < n ∧ n ≤ 2 ^ 64 := by decide) :
    (m.writeBytes (base + off1) (List.replicate n v)).read8 (base + off2) = v := by
  rw [add_sub_cancel_bv base off1 off2, ProofLib.read8_writeBytes_inbounds m (base + off1) (List.replicate n v)
    (off2 - off1).toNat (by rw [List.length_replicate]; exact h.1)
    (by rw [List.length_replicate]; exact h.2), List.getElem_replicate]

theorem read64_writeBytes_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (bs : List (BitVec 8))
    (hd : 8 ≤ (off1 - off2).toNat ∧ bs.length ≤ (off2 - off1).toNat := by decide) :
    (m.writeBytes (base + off1) bs).read64 (base + off2) = m.read64 (base + off2) := by
  apply ProofLib.read64_writeBytes_disjoint
  unfold DisjointRegions
  rw [add_sub_add_left_bv base off2 off1, add_sub_add_left_bv base off1 off2]
  exact hd

theorem read64_writeBytes_replicate_zero_off (m : Memory) (base off1 off2 : BitVec 64) (n : ℕ)
    (h : (off2 - off1).toNat + 8 ≤ n ∧ n ≤ 2 ^ 64 := by decide) :
    (m.writeBytes (base + off1) (List.replicate n 0#8)).read64 (base + off2) = 0#64 := by
  have hbyte : ∀ k : ℕ, k < 8 →
      (m.writeBytes (base + off1) (List.replicate n 0#8)).read8 ((base + off2) + BitVec.ofNat 64 k) = 0#8 := by
    intro k hk
    rw [add_off_k_bv base off1 off2 k, ProofLib.read8_writeBytes_inbounds m (base + off1) (List.replicate n 0#8)
      ((off2 - off1).toNat + k) (by rw [List.length_replicate]; have := h.1; omega)
      (by rw [List.length_replicate]; exact h.2), List.getElem_replicate]
  have e0 := hbyte 0 (by decide)
  have e1 := hbyte 1 (by decide)
  have e2 := hbyte 2 (by decide)
  have e3 := hbyte 3 (by decide)
  have e4 := hbyte 4 (by decide)
  have e5 := hbyte 5 (by decide)
  have e6 := hbyte 6 (by decide)
  have e7 := hbyte 7 (by decide)
  simp only [BitVec.add_zero] at e0
  dsimp only [Memory.read64]
  simp only [BitVec.add_zero, e0, e1, e2, e3, e4, e5, e6, e7]
  rfl

theorem readBytes_writeBytes_off_disjoint (m : Memory) (base off1 off2 : BitVec 64) (n : ℕ)
    (bs : List (BitVec 8))
    (hd : n ≤ (off1 - off2).toNat ∧ bs.length ≤ (off2 - off1).toNat := by decide) :
    (m.writeBytes (base + off1) bs).readBytes (base + off2) n = m.readBytes (base + off2) n := by
  apply ProofLib.readBytes_writeBytes_disjoint
  unfold DisjointRegions
  rw [add_sub_add_left_bv base off2 off1, add_sub_add_left_bv base off1 off2]; exact hd

theorem read64_writeBytes_replicate_off_disjoint (m : Memory) (base off1 off2 : BitVec 64)
    (n : ℕ) (v : BitVec 8)
    (hd : 8 ≤ (off1 - off2).toNat ∧ n ≤ (off2 - off1).toNat := by decide) :
    (m.writeBytes (base + off1) (List.replicate n v)).read64 (base + off2) = m.read64 (base + off2) :=
  read64_writeBytes_off_disjoint m base off1 off2 (List.replicate n v) (by simpa using hd)

theorem readBytes_writeBytes_replicate_off_disjoint (m : Memory) (base off1 off2 : BitVec 64)
    (n mlen : ℕ) (v : BitVec 8)
    (hd : n ≤ (off1 - off2).toNat ∧ mlen ≤ (off2 - off1).toNat := by decide) :
    (m.writeBytes (base + off1) (List.replicate mlen v)).readBytes (base + off2) n =
      m.readBytes (base + off2) n :=
  readBytes_writeBytes_off_disjoint m base off1 off2 n (List.replicate mlen v) (by simpa using hd)

theorem toLEBytes_8_read64_writeBytes_146_62 (m : Memory) (base : BitVec 64) :
    toLEBytes 8 ((m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read64 (base + 144#64)) =
      [m.read8 (base + 144#64), m.read8 (base + 145#64), 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] := by
  rw [toLEBytes_8_read64_eq, readBytes_8_eq]
  simp only [BitVec.add_assoc]
  change [(m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read8 (base + 144#64),
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read8 (base + 145#64),
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read8 (base + 146#64),
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read8 (base + 147#64),
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read8 (base + 148#64),
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read8 (base + 149#64),
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read8 (base + 150#64),
      (m.writeBytes (base + 146#64) (List.replicate 62 0#8)).read8 (base + 151#64)] = _
  rw [read8_writeBytes_off_outside m base 146#64 144#64 (List.replicate 62 0#8),
      read8_writeBytes_off_outside m base 146#64 145#64 (List.replicate 62 0#8),
      read8_writeBytes_replicate_off m base 146#64 146#64 62 0#8,
      read8_writeBytes_replicate_off m base 146#64 147#64 62 0#8,
      read8_writeBytes_replicate_off m base 146#64 148#64 62 0#8,
      read8_writeBytes_replicate_off m base 146#64 149#64 62 0#8,
      read8_writeBytes_replicate_off m base 146#64 150#64 62 0#8,
      read8_writeBytes_replicate_off m base 146#64 151#64 62 0#8]

structure StateH1p (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = b + bv% (ls_off% "memset")
  common  : HmacCommon s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 146#64
  x1_eq   : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq   : s.readReg64 .x2 = 62#64
  lr_eq   : s.readReg64 .lr = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 388)
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq  : s.readReg64 .x23 = 128#64
  x24_eq  : s.readReg64 .x24 = 1#64
  x25_eq  : s.readReg64 .x25 = 1#64
  x26_eq  : s.readReg64 .x26 = 62#64
  m144_0  : s.mem.read8 (hsp s₀ + 144#64) = byte
  m144_1  : s.mem.read8 (hsp s₀ + 145#64) = 0x80#8
  ist_eq  : s.mem.readBytes (hsp s₀ + 208#64) 32 = shaStateBytes (innerState F key)
  ibl_eq  : s.mem.read64 (hsp s₀ + 240#64) = 1#64
  ost_eq  : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq  : s.mem.read64 (hsp s₀ + 280#64) = 1#64

structure StateH2 (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 388)
  common : HmacCommon s₀ s
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

theorem seg1b1_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPre b F key [byte] s₀)
    (hs : StateH1m b F key s₀ s) :
    RunsTo (P b F alloc) s (StateH1p b F key byte s₀) := by
  generalize hPost : StateH1p b F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx21, hx22, hx23, hx25, hist, hibl, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hinp_s : s.mem.readBytes (s₀.readReg64 .x3) 1 = [byte] := by
    rw [hframe.readBytes_eq (by simp [hpre.disj_inp_stack.symm]) (by decide), hpre.inp_eq]
  refine RunsTo.sess_memcpy_step
    (hrun := hstat)
    (hpc := hpc)
    (hx0 := hx0)
    (hx1 := hx1)
    (hx2 := by rw [hx2]; rfl)
    (hlr := hlr)
    (hmem := rfl)
    (hread := hinp_s)
    (hrw := hrw_hsp.sub (by clear * -; bv_omega))
    ?_
  rw [writeBytes_singleton]
  iterate 25 sess_step
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    refine Frame.write8_stack1024 ?_ _ _
    iterate 18 refine Frame.write64_stack1024 ?_ _ _
    iterate 2 refine Frame.write8_stack1024 ?_ _ _
    exact hframe
  · simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · simp only [arm64_norm, hx19]
  · simp only [arm64_norm]
  · simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · simp only [arm64_norm, hx22]
  · simp only [arm64_norm]
  · simp only [arm64_norm]
  · simp only [arm64_norm, hibl]
  · simp (config := { decide := true }) only [arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← hist]
    refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 208#64) (hsp s₀ + 64#64)
      ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hibl]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← host]
    refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 248#64) (hsp s₀ + 104#64)
      ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32,
      State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl]

theorem seg1b2_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPre b F key [byte] s₀)
    (hs : StateH1p b F key byte s₀ s) :
    RunsTo (P b F alloc) s (StateH2 b F key byte s₀) := by
  generalize hPost : StateH2 b F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26,
    hm144_0, hm144_1, hist, hibl, host, hobl⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  refine RunsTo.sess_memset_step
    (dst := hsp s₀ + 146#64)
    (lr := b + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 388))
    (val := 0#8)
    (len := 62)
    (hrun := hstat)
    (hpc := hpc)
    (hx0 := hx0)
    (hx1 := hx1)
    (hx2 := by rw [hx2]; rfl)
    (hlr := hlr)
    (hmem := rfl)
    (hrw := hrw_hsp.sub (by clear * -; bv_omega))
    ?_
  subst hPost
  refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm], ⟨by simp only [arm64_norm, hstat], ?_, ?_, ?_, ?_, ?_⟩,
    by simp only [arm64_norm, hx19],
    by simp only [arm64_norm, hx20],
    by simp only [arm64_norm, hx21],
    by simp only [arm64_norm, hx22],
    by simp only [arm64_norm, hx23],
    by simp only [arm64_norm, hx24],
    by simp only [arm64_norm, hx25],
    by simp only [arm64_norm, hx26],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [arm64_norm, hsp_eq]
  · simp only [arm64_norm, hx29]
  · simp only [arm64_norm, hx27]
  · dsimp only [State.setMem, State.setPC]
    exact hsaved.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by clear * -; simp only [List.length_replicate, DisjointRegions]; bv_omega)
  · dsimp only [State.setMem, State.setPC]
    exact Frame.writeBytes_stack1024 hframe _ _ (by clear * -; simp only [List.length_replicate]; unfold hsp; bv_omega)
  · dsimp only [State.setMem, State.setPC]
    rw [toLEBytes_8_read64_writeBytes_146_62 s.mem (hsp s₀), hm144_0, hm144_1]
    rfl
  · dsimp only [State.setMem, State.setPC]
    exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 152#64 62
  · dsimp only [State.setMem, State.setPC]
    exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 160#64 62
  · dsimp only [State.setMem, State.setPC]
    exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 168#64 62
  · dsimp only [State.setMem, State.setPC]
    exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 176#64 62
  · dsimp only [State.setMem, State.setPC]
    exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 184#64 62
  · dsimp only [State.setMem, State.setPC]
    exact read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 192#64 62
  · dsimp only [State.setMem, State.setPC]
    rw [readBytes_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 208#64 32 62 0#8]
    exact hist
  · dsimp only [State.setMem, State.setPC]
    rw [read64_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 240#64 62 0#8]
    exact hibl
  · dsimp only [State.setMem, State.setPC]
    rw [readBytes_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 248#64 32 62 0#8]
    exact host
  · dsimp only [State.setMem, State.setPC]
    rw [read64_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 280#64 62 0#8]
    exact hobl

theorem seg1b_runsTo {b : BitVec 64} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPre b F key [byte] s₀)
    (hs : StateH1m b F key s₀ s) :
    RunsTo (P b F alloc) s (StateH2 b F key byte s₀) :=
  (seg1b1_runsTo hpre hs).trans (fun _ h1p => seg1b2_runsTo hpre h1p)

/-! ## Relocatable `[LibsignalPlacement]` Entry and Key Block (Block 73) -/

@[simp, arm64_norm]
theorem lsmpl_base_136 [LibsignalPlacement] : lsmpl.base 114 = (blkPl_114).base := rfl

@[simp, arm64_norm]
theorem lsmpl_base_92 [LibsignalPlacement] : lsmpl.base 73 = (blkPl_73).base := rfl

structure HmacPlacedPre [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key inp : List (BitVec 8)) (s₀ : State) : Prop where
  pc_eq          : s₀.pc = (blkPl_73).base
  status         : s₀.status = .Running
  sp_aligned     : (s₀.sp &&& 0b1111#64) = 0#64
  x2_eq          : s₀.readReg64 .x2 = 32#64
  x4_eq          : s₀.readReg64 .x4 = 1#64
  key_len        : key.length = 32
  inp_len        : inp.length = 1
  key_eq         : s₀.mem.readBytes (s₀.readReg64 .x1) 32 = key
  inp_eq         : s₀.mem.readBytes (s₀.readReg64 .x3) 1 = inp
  iv_eq          : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV
  read_iv        : s₀.mem.Readable lsSha256IVAddr 32
  read_inp       : s₀.mem.Readable (s₀.readReg64 .x3) 1
  rw_out         : RW s₀.mem (s₀.readReg64 .x0) 32
  rw_stack       : RW s₀.mem (s₀.sp - 1024#64) 1024
  disj_iv_stack  : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 1024#64) 1024
  disj_out_stack : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.sp - 1024#64) 1024
  disj_key_stack : DisjointRegions (s₀.readReg64 .x1) 32 (s₀.sp - 1024#64) 1024
  disj_inp_stack : DisjointRegions (s₀.readReg64 .x3) 1 (s₀.sp - 1024#64) 1024

structure StateH1Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq   : s.pc = (blkPl_73).base + 52#64
  common  : HmacCommon s₀ s
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s₀.readReg64 .x3
  x21_eq  : s.readReg64 .x21 = 1#64
  tag_eq  : s.mem.read64 (hsp s₀ + 144#64) = 0#64
  hmac_st : HmacSt s.mem (hsp s₀ + 152#64) F key []

structure StateH0Placed [LibsignalPlacement] (s₀ s : State) : Prop where
  pc_eq  : s.pc = (blkPl_114).base
  common : HmacCommon s₀ s
  x0_eq  : s.readReg64 .x0 = hsp s₀ + 144#64
  x1_eq  : s.readReg64 .x1 = s₀.readReg64 .x1
  x2_eq  : s.readReg64 .x2 = 32#64
  lr_eq  : s.readReg64 .lr = (blkPl_73).base + 52#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s₀.readReg64 .x3
  x21_eq : s.readReg64 .x21 = 1#64

theorem seg0a_placed_runsTo [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key inp : List (BitVec 8)} {s₀ : State}
    (hpre : HmacPlacedPre F key inp s₀) :
    RunsTo (lsProg_73 H) s₀ (StateH0Placed s₀) := by
  generalize hPost : StateH0Placed s₀ = Post
  have hpc := hpre.pc_eq; have hstat := hpre.status
  have hal_hsp : ((s₀.sp - 480#64) &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s₀.mem.RW (s₀.sp - 480#64) 480 := hpre.rw_stack.sub (by clear * -; bv_omega)
  iterate 13 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc], ⟨hstat, by simp only [arm64_norm, hsp],
    by simp only [arm64_norm, hsp], by simp only [arm64_norm], ?_, ?_⟩,
    by simp only [arm64_norm, hsp], by simp only [arm64_norm], by simp only [arm64_norm, hpre.x2_eq],
    by simp only [arm64_norm, hpc], by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm, hpre.x4_eq]⟩
  · dsimp only [HmacSaved, hsp, State.setMem, State.writeReg64, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.setPC, State.advancePC]
    repeat refine Frame.write64_stack1024 ?_ _ _
    exact Frame.refl s₀.mem _

theorem seg0b_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {key inp : List (BitVec 8)} {s₀ sc : State}
    (hcl : LibsignalCodeLoaded lsmpl sc.mem) (hpre : HmacPlacedPre F key inp s₀)
    (hsc : StateH0Placed s₀ sc) : RunsTo (lsProg_73 H) sc (StateH1Placed F key s₀) := by
  rcases hsc with ⟨hpc_c, ⟨hstat_c, hsp_c, hx29_c, hx27_c, hsaved_c, hframe_c⟩,
    hx0_c, hx1_c, hx2_c, hlr_c, hx19_c, hx20_c, hx21_c⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hkey_c : sc.mem.readBytes (sc.readReg64 .x1) (sc.readReg64 .x2).toNat = key := by
    rw [hx1_c, hx2_c, show (32#64 : BitVec 64).toNat = 32 from rfl,
      hframe_c.readBytes_eq (by simp [hpre.disj_key_stack.symm]) (by decide), hpre.key_eq]
  have hiv_c : sc.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV := by
    rw [hframe_c.readBytes_eq (by simp [hpre.disj_iv_stack.symm]) (by decide), hpre.iv_eq]
  have hread_iv_c : sc.mem.Readable lsSha256IVAddr 32 := (hframe_c.readable_iff _ _).mpr hpre.read_iv
  have hrw_stack_c : RW sc.mem (s₀.sp - 1024#64) 1024 := (hframe_c.rw_iff _ _).mpr hpre.rw_stack
  have hdisj_iv_nfs : DisjointRegions lsSha256IVAddr 32 (sc.sp - 544#64) 544 := by
    rw [hsp_c, hsp_sub_544_eq]; exact hpre.disj_iv_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  have hrw_out_nfs : RW sc.mem (sc.readReg64 .x0) 0x98 := by
    rw [hx0_c]; exact hrw_stack_c.sub (by clear * -; unfold hsp; bv_omega)
  have hrw_stack_nfs : RW sc.mem (sc.sp - 544#64) 544 := by
    rw [hsp_c, hsp_sub_544_eq]; exact hrw_stack_c.sub (by clear * -; bv_omega)
  have hdisj_out_nfs : DisjointRegions (sc.readReg64 .x0) 0x98 (sc.sp - 544#64) 544 := by
    rw [hx0_c, hsp_c]; clear * -; unfold hsp DisjointRegions; bv_omega
  have hdisj_key_nfs : DisjointRegions (sc.readReg64 .x1) (sc.readReg64 .x2).toNat (sc.sp - 544#64) 544 := by
    rw [hx1_c, hx2_c, hsp_c, hsp_sub_544_eq, show (32#64 : BitVec 64).toNat = 32 from rfl]
    exact hpre.disj_key_stack.sub_right _ ⟨by decide, by clear * -; bv_omega⟩
  refine (RunsTo.of_other_block hcl
    (new_from_slice_placed_run h_memcpy h_compress hpc_c hstat_c (by rw [hx2_c]; decide)
      hiv_c hread_iv_c hdisj_iv_nfs hrw_out_nfs hrw_stack_nfs hdisj_out_nfs (Or.inr hdisj_key_nfs)
      (by rw [hsp_c]; exact hal_hsp))).mono fun s₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc1, hstat1, hcs1, htag1, hhmac1, hframe1⟩
  rw [hlr_c] at hpc1; rw [hx0_c] at htag1 hhmac1 hframe1; rw [hsp_c] at hframe1; rw [hkey_c] at hhmac1
  have hhmac_addr : hsp s₀ + 144#64 + 8#64 = hsp s₀ + 152#64 := by clear * -; bv_omega
  rw [hhmac_addr] at hhmac1
  refine ⟨hpc1, ⟨hstat1, hcs1.1.trans hsp_c, (hcs1.2 .x29 (by simp)).trans hx29_c,
    (hcs1.2 .x27 (by simp)).trans hx27_c, HmacSaved.of_frame hsaved_c hframe1 (by
      intro r hr; clear * - hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold hsp DisjointRegions; bv_omega)),
    Frame.trans_nfs hframe_c hframe1⟩,
    (hcs1.2 .x19 (by simp)).trans hx19_c, (hcs1.2 .x20 (by simp)).trans hx20_c,
    (hcs1.2 .x21 (by simp)).trans hx21_c, htag1, hhmac1⟩

theorem seg0_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {key inp : List (BitVec 8)} {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem) (hpre : HmacPlacedPre F key inp s₀) :
    RunsTo (lsProg_73 H) s₀ (StateH1Placed F key s₀) :=
  RunsTo.trans_keepsFrozen (seg0a_placed_runsTo hpre) (fun _ hsc hkf =>
    seg0b_placed_runsTo h_memcpy h_compress (hcl.of_keepsFrozen hkf) hpre hsc)

structure StateH1mPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq  : s.pc = lsρ lsMemcpySym
  common : HmacCommon s₀ s
  x0_eq  : s.readReg64 .x0 = hsp s₀
  x1_eq  : s.readReg64 .x1 = s₀.readReg64 .x3
  x2_eq  : s.readReg64 .x2 = 1#64
  lr_eq  : s.readReg64 .lr = (blkPl_73).base + 164#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x21_eq : s.readReg64 .x21 = 1#64
  x22_eq : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq : s.readReg64 .x23 = hsp s₀
  x25_eq : s.readReg64 .x25 = 0#64
  ist_eq : s.mem.readBytes (hsp s₀ + 64#64) 32 = shaStateBytes (innerState F key)
  ibl_eq : s.mem.read64 (hsp s₀ + 96#64) = 1#64
  ost_eq : s.mem.readBytes (hsp s₀ + 104#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (hsp s₀ + 136#64) = 1#64

theorem seg1a_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} {key inp : List (BitVec 8)} {s₀ s : State}
    (hpre : HmacPlacedPre F key inp s₀) (hs : StateH1Placed F key s₀ s) :
    RunsTo (lsProg_73 H) s (StateH1mPlaced F key s₀) := by
  generalize hPost : StateH1mPlaced F key s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩, hx19, hx20, hx21, htag, hhmac⟩
  rcases hhmac with ⟨_, _, hpos, hin, hibl, hout, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hpos' : s.mem.read8 (hsp s₀ + 215#64) = 0#8 := by
    rw [← (by clear * -; bv_omega : hsp s₀ + 152#64 + 0x3f#64 = hsp s₀ + 215#64)]; exact hpos
  have hin' : s.mem.readBytes (hsp s₀ + 216#64) 32 = shaStateBytes (innerState F key) := by
    rw [← (by clear * -; bv_omega : hsp s₀ + 152#64 + 0x40#64 = hsp s₀ + 216#64)]; exact hin
  have hibl' : s.mem.read64 (hsp s₀ + 248#64) = 1#64 := by
    rw [← (by clear * -; bv_omega : hsp s₀ + 152#64 + 0x60#64 = hsp s₀ + 248#64)]; exact hibl
  have hout' : s.mem.readBytes (hsp s₀ + 256#64) 32 = shaStateBytes (outerState F key) := by
    rw [← (by clear * -; bv_omega : hsp s₀ + 152#64 + 0x68#64 = hsp s₀ + 256#64)]; exact hout
  have hobl' : s.mem.read64 (hsp s₀ + 288#64) = 1#64 := by
    rw [← (by clear * -; bv_omega : hsp s₀ + 152#64 + 0x88#64 = hsp s₀ + 288#64)]; exact hobl
  iterate 28 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm, hpc, lsMemcpySym],
    ⟨hstat, by simp only [arm64_norm, hsp_eq], by simp only [arm64_norm, hx29],
     by simp only [arm64_norm, hx27], ?_, ?_⟩,
    by simp only [arm64_norm], by simp only [arm64_norm, hx20], by simp only [arm64_norm, hx21],
    by simp only [arm64_norm, hpc], by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx21],
    by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], ?_, ?_, ?_, ?_⟩
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    repeat refine Frame.write64_stack1024 ?_ _ _
    exact hframe
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← hin']; refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 64#64) (hsp s₀ + 216#64) ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hibl']
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← hout']; refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 104#64) (hsp s₀ + 256#64) ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl']

structure StateH1pPlaced [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq : s.pc = lsρ lsMemsetSym
  common : HmacCommon s₀ s
  x0_eq : s.readReg64 .x0 = hsp s₀ + 146#64
  x1_eq : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq : s.readReg64 .x2 = 62#64
  lr_eq : s.readReg64 .lr = (blkPl_73).base + 388#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq : s.readReg64 .x23 = 128#64
  x24_eq : s.readReg64 .x24 = 1#64
  x25_eq : s.readReg64 .x25 = 1#64
  x26_eq : s.readReg64 .x26 = 62#64
  m144_0 : s.mem.read8 (hsp s₀ + 144#64) = byte
  m144_1 : s.mem.read8 (hsp s₀ + 145#64) = 0x80#8
  ist_eq : s.mem.readBytes (hsp s₀ + 208#64) 32 = shaStateBytes (innerState F key)
  ibl_eq : s.mem.read64 (hsp s₀ + 240#64) = 1#64
  ost_eq : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (hsp s₀ + 280#64) = 1#64

structure StateH2Placed [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq : s.pc = (blkPl_73).base + 388#64
  common : HmacCommon s₀ s
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq : s.readReg64 .x23 = 128#64
  x24_eq : s.readReg64 .x24 = 1#64
  x25_eq : s.readReg64 .x25 = 1#64
  x26_eq : s.readReg64 .x26 = 62#64
  m144 : toLEBytes 8 (s.mem.read64 (hsp s₀ + 144#64)) = [byte, 0x80#8, 0, 0, 0, 0, 0, 0]
  m152 : s.mem.read64 (hsp s₀ + 152#64) = 0#64
  m160 : s.mem.read64 (hsp s₀ + 160#64) = 0#64
  m168 : s.mem.read64 (hsp s₀ + 168#64) = 0#64
  m176 : s.mem.read64 (hsp s₀ + 176#64) = 0#64
  m184 : s.mem.read64 (hsp s₀ + 184#64) = 0#64
  m192 : s.mem.read64 (hsp s₀ + 192#64) = 0#64
  ist_eq : s.mem.readBytes (hsp s₀ + 208#64) 32 = shaStateBytes (innerState F key)
  ibl_eq : s.mem.read64 (hsp s₀ + 240#64) = 1#64
  ost_eq : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (hsp s₀ + 280#64) = 1#64

theorem seg1b1_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH1mPlaced F key s₀ s) :
    RunsTo (lsProg_73 H) s (StateH1pPlaced F key byte s₀) := by
  generalize hPost : StateH1pPlaced F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx21, hx22, hx23, hx25, hist, hibl, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  have hinp_s : s.mem.readBytes (s₀.readReg64 .x3) 1 = [byte] := by
    rw [hframe.readBytes_eq (by simp [hpre.disj_inp_stack.symm]) (by decide), hpre.inp_eq]
  refine RunsTo.placed_memcpy_step h_memcpy
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := by rw [hx2]; rfl)
    (hlr := hlr) (hmem := rfl) (hread := hinp_s) (hrw := hrw_hsp.sub (by clear * -; bv_omega)) ?_
  rw [writeBytes_singleton]
  iterate 25 sess_step
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, lsMemsetSym],
    ⟨by simp only [arm64_norm, hstat], by simp only [arm64_norm, hsp_eq],
     by simp only [arm64_norm, hx29], by simp only [arm64_norm, hx27], ?_, ?_⟩,
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hx19], by simp only [arm64_norm],
    by simp only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm],
    by simp only [arm64_norm, hx22], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm, hibl],
    by simp (config := { decide := true }) only [arm64_norm], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hsaved with ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
    dsimp only [HmacSaved, State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    refine Frame.write8_stack1024 ?_ _ _; iterate 18 refine Frame.write64_stack1024 ?_ _ _
    (iterate 2 refine Frame.write8_stack1024 ?_ _ _); exact hframe
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← hist]; refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 208#64) (hsp s₀ + 64#64) ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hibl]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    rw [← host]; refine readBytes_32_eq_of_read64_eq _ s.mem (hsp s₀ + 248#64) (hsp s₀ + 104#64) ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm]
  · dsimp only [State.setMem, State.writeReg64, State.writeReg32, State.writeVReg128, State.setPState, State.setPC, State.advancePC]
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hobl]

theorem seg1b2_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memset : H lsMemsetSym = some memsetHook)
    {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH1pPlaced F key byte s₀ s) :
    RunsTo (lsProg_73 H) s (StateH2Placed F key byte s₀) := by
  generalize hPost : StateH2Placed F key byte s₀ = Post
  rcases hs with ⟨hpc, ⟨hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26,
    hm144_0, hm144_1, hist, hibl, host, hobl⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    ((hframe.rw_iff _ _).mpr hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  refine RunsTo.placed_memset_step h_memset
    (dst := hsp s₀ + 146#64) (lr := (blkPl_73).base + 388#64) (val := 0#8) (len := 62)
    (hrun := hstat) (hpc := hpc) (hx0 := hx0) (hx1 := hx1) (hx2 := by rw [hx2]; rfl)
    (hlr := hlr) (hmem := rfl) (hrw := hrw_hsp.sub (by clear * -; bv_omega)) ?_
  subst hPost; refine RunsTo.refl ?_
  refine ⟨by simp only [arm64_norm],
    ⟨by simp only [arm64_norm, hstat], by simp only [arm64_norm, hsp_eq],
     by simp only [arm64_norm, hx29], by simp only [arm64_norm, hx27], ?_, ?_⟩,
    by simp only [arm64_norm, hx19], by simp only [arm64_norm, hx20],
    by simp only [arm64_norm, hx21], by simp only [arm64_norm, hx22],
    by simp only [arm64_norm, hx23], by simp only [arm64_norm, hx24],
    by simp only [arm64_norm, hx25], by simp only [arm64_norm, hx26],
    ?_, read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 152#64 62,
    read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 160#64 62,
    read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 168#64 62,
    read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 176#64 62,
    read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 184#64 62,
    read64_writeBytes_replicate_zero_off s.mem (hsp s₀) 146#64 192#64 62, ?_, ?_, ?_, ?_⟩
  · exact hsaved.of_agreesOutside (AgreesOutside.writeBytes_self _ _ _)
      (by clear * -; simp only [List.length_replicate, DisjointRegions]; bv_omega)
  · exact Frame.writeBytes_stack1024 hframe _ _ (by clear * -; simp only [List.length_replicate]; unfold hsp; bv_omega)
  · dsimp only [State.setMem, State.setPC]; rw [toLEBytes_8_read64_writeBytes_146_62 s.mem (hsp s₀), hm144_0, hm144_1]; rfl
  · dsimp only [State.setMem, State.setPC]; rw [readBytes_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 208#64 32 62 0#8]; exact hist
  · dsimp only [State.setMem, State.setPC]; rw [read64_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 240#64 62 0#8]; exact hibl
  · dsimp only [State.setMem, State.setPC]; rw [readBytes_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 248#64 32 62 0#8]; exact host
  · dsimp only [State.setMem, State.setPC]; rw [read64_writeBytes_replicate_off_disjoint s.mem (hsp s₀) 146#64 280#64 62 0#8]; exact hobl

theorem seg1b_placed_runsTo [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memcpy : H lsMemcpySym = some memcpyHook)
    (h_memset : H lsMemsetSym = some memsetHook) {key : List (BitVec 8)} {byte : BitVec 8} {s₀ s : State}
    (hpre : HmacPlacedPre F key [byte] s₀) (hs : StateH1mPlaced F key s₀ s) :
    RunsTo (lsProg_73 H) s (StateH2Placed F key byte s₀) :=
  (seg1b1_placed_runsTo h_memcpy hpre hs).trans (fun _ h1p => seg1b2_placed_runsTo h_memset hpre h1p)

end CryptoVerification.LibsignalSession.CryptoHmacSha256
