/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt

/-!
# `crypto::hmac_sha256` Symbolic-Offset Segments (`seg0a` through `seg1b1_post`)

Part A of the `RunsToE (tripleRatchetProgAtExt img.base ext)` segment proofs for
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
   memcpy_subroutine_runsTo memset_subroutine_runsTo compress256_subroutine_runsTo)
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff

theorem runsToE_mono_with_inv
    {prog : Program} {img : Obj.Image} {s : State}
    {P Q : State → Prop} (h : RunsToE prog s P)
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hPQ : ∀ s', img.FrozenLoaded s' → s'.symtab = img.symtab → P s' → Q s') :
    RunsToE prog s Q := by
  intro hL
  obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
  exact ⟨sf, hst, htr, hPQ sf (hfrz.of_keepsFrozen hst.keepsFrozen) (hst.symtab_eq.trans hsym) hP, hLf⟩

theorem runsToE_hmac {prog : Program} {s : State} {P : State → Prop}
    (h : _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo prog s P) : RunsToE prog s P := by
  intro hL
  obtain ⟨sf, hst, htr, hvregs, hP, hLf⟩ := h hL
  exact ⟨sf, hst, ⟨htr, hvregs⟩, hP, hLf⟩

theorem runsToE_of_runsTo_with_inv
    (prog : Program) {img : Obj.Image} {s : State} {Q : State → Prop}
    (hfrz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo prog s (fun s' => img.FrozenLoaded s' → s'.symtab = img.symtab → Q s')) :
    RunsToE prog s Q :=
  runsToE_mono_with_inv (runsToE_hmac h) hfrz hsym (fun _ hfrz' hsym' hQ => hQ hfrz' hsym')

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

theorem hmacSaved_of_s2Frame {s₀ : State} {hsp : BitVec 64} {m₁ m₂ : Memory}
    {rs : List (BitVec 64 × ℕ)}
    (hs : HmacSaved s₀ hsp m₁)
    (hrw : RW m₁ (hsp + 384#64) 96)
    (hf : S2Frame m₁ m₂ rs)
    (hd : ∀ r ∈ rs, DisjointRegions r.1 r.2 (hsp + 384#64) 96) :
    HmacSaved s₀ hsp m₂ := by
  rcases hs with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have sub8 (off : BitVec 64) (hoff : (off - (hsp + 384#64)).toNat + 8 ≤ 96) :
      m₂.read64 off = m₁.read64 off := by
    have hd_off : ∀ r ∈ rs, DisjointRegions r.1 r.2 off 8 :=
      fun r hr => (hd r hr).sub_right off ⟨by decide, hoff⟩
    exact hf.read64_eq (hrw.sub hoff) hd_off
  exact ⟨(sub8 (hsp + 384#64) (by clear * -; bv_omega)).trans h1,
         (sub8 (hsp + 392#64) (by clear * -; bv_omega)).trans h2,
         (sub8 (hsp + 400#64) (by clear * -; bv_omega)).trans h3,
         (sub8 (hsp + 416#64) (by clear * -; bv_omega)).trans h4,
         (sub8 (hsp + 424#64) (by clear * -; bv_omega)).trans h5,
         (sub8 (hsp + 432#64) (by clear * -; bv_omega)).trans h6,
         (sub8 (hsp + 440#64) (by clear * -; bv_omega)).trans h7,
         (sub8 (hsp + 448#64) (by clear * -; bv_omega)).trans h8,
         (sub8 (hsp + 456#64) (by clear * -; bv_omega)).trans h9,
         (sub8 (hsp + 464#64) (by clear * -; bv_omega)).trans h10,
         (sub8 (hsp + 472#64) (by clear * -; bv_omega)).trans h11⟩

theorem s2Frame_trans_r7b_stack1024 {sp : BitVec 64} {m₀ m₁ m₂ : Memory}
    (hf1 : S2Frame m₀ m₁ [(sp - 17408#64, 17408)])
    (hf2 : Frame m₁ m₂ [(sp - 1024#64, 1024)]) :
    S2Frame m₀ m₂ [(sp - 17408#64, 17408)] := by
  refine hf1.trans ((S2Frame.of_frame hf2).mono fun a ha r hr => ?_)
  have h1 := ha (sp - 17408#64, 17408) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  unfold OutsideRegion at h1 ⊢
  clear * - h1; bv_omega

theorem s2Frame_trans_pair_stk17408 {sp : BitVec 64} {m₀ m₁ m₂ : Memory}
    {a₁ : BitVec 64} {n₁ : ℕ} {a₂ : BitVec 64} {n₂ : ℕ}
    (hf1 : S2Frame m₀ m₁ [(sp - 17408#64, 17408)])
    (hf2 : S2Frame m₁ m₂ [(a₁, n₁), (a₂, n₂)])
    (hsub₁ : (a₁ - (sp - 17408#64)).toNat + n₁ ≤ 17408)
    (hsub₂ : (a₂ - (sp - 17408#64)).toNat + n₂ ≤ 17408) :
    S2Frame m₀ m₂ [(sp - 17408#64, 17408)] := by
  refine hf1.trans (hf2.mono fun a ha => ?_)
  have h1 := ha (sp - 17408#64, 17408) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  unfold OutsideRegion at h1 ⊢
  refine ⟨by clear * - h1 hsub₁; bv_omega, by clear * - h1 hsub₂; bv_omega⟩

theorem s2Frame_writeBytes_out_stk17408 {out sp : BitVec 64} {m₀ m : Memory}
    (hf : S2Frame m₀ m [(sp - 17408#64, 17408)])
    (bs : List (BitVec 8)) (hlen : bs.length = 32) :
    S2Frame m₀ (m.writeBytes out bs) [(out, 32), (sp - 17408#64, 17408)] := by
  have hag : AgreesOutside m (m.writeBytes out bs) out 32 :=
    hlen ▸ ProofLib.AgreesOutside.writeBytes_self m out bs
  refine (hf.mono fun a ha r hr => ha r (List.mem_cons_of_mem _ hr)).trans ?_
  exact S2Frame.of_frame (Frame.trans_agreesOutside (Frame.refl m _) hag)

structure HmacPreX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key inp : List (BitVec 8)) (s₀ : State) : Prop where
  frz            : img.FrozenLoaded s₀
  sym            : s₀.symtab = img.symtab
  pc_eq          : s₀.pc = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256")
  status         : s₀.status = .Running
  sp_aligned     : (s₀.sp &&& 0b1111#64) = 0#64
  base_aligned   : (img.base &&& 0xfff#64) = 0#64
  x2_eq          : s₀.readReg64 .x2 = 32#64
  x4_eq          : s₀.readReg64 .x4 = 1#64
  key_len        : key.length = 32
  inp_len        : inp.length = 1
  key_eq         : s₀.mem.readBytes (s₀.readReg64 .x1) 32 = key
  inp_eq         : s₀.mem.readBytes (s₀.readReg64 .x3) 1 = inp
  iv_eq          : s₀.mem.readBytes (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 = shaStateBytes sha256IV
  read_iv        : s₀.mem.Readable (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32
  rw_key         : RW s₀.mem (s₀.readReg64 .x1) 32
  rw_inp         : RW s₀.mem (s₀.readReg64 .x3) 1
  rw_out         : RW s₀.mem (s₀.readReg64 .x0) 32
  rw_stack       : RW s₀.mem (s₀.sp - 17408#64) 17408
  disj_iv_stack  : DisjointRegions (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (s₀.sp - 17408#64) 17408
  disj_out_stack : DisjointRegions (s₀.readReg64 .x0) 32 (s₀.sp - 17408#64) 17408
  disj_key_stack : DisjointRegions (s₀.readReg64 .x1) 32 (s₀.sp - 17408#64) 17408
  disj_inp_stack : DisjointRegions (s₀.readReg64 .x3) 1 (s₀.sp - 17408#64) 17408

structure HmacCommonX (img : Obj.Image) (s₀ s : State) : Prop where
  frz    : img.FrozenLoaded s
  sym    : s.symtab = img.symtab
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x29_eq : s.readReg64 .x29 = hsp s₀ + 384#64
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  saved  : HmacSaved s₀ (hsp s₀) s.mem
  frame  : S2Frame s₀.mem s.mem [(s₀.sp - 17408#64, 17408)]

structure StateH0X (img : Obj.Image) (s₀ s : State) : Prop where
  pc_eq  : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]")
  common : HmacCommonX img s₀ s
  x0_eq  : s.readReg64 .x0 = hsp s₀ + 144#64
  x1_eq  : s.readReg64 .x1 = s₀.readReg64 .x1
  x2_eq  : s.readReg64 .x2 = 32#64
  lr_eq  : s.readReg64 .lr = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 52)
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s₀.readReg64 .x3
  x21_eq : s.readReg64 .x21 = 1#64

structure StateH1X (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 52)
  common  : HmacCommonX img s₀ s
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s₀.readReg64 .x3
  x21_eq  : s.readReg64 .x21 = 1#64
  tag_eq  : s.mem.read64 (hsp s₀ + 144#64) = 0#64
  hmac_st : HmacSt s.mem (hsp s₀ + 152#64) F key []

structure StateH1mX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% "memcpy")
  common  : HmacCommonX img s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀
  x1_eq   : s.readReg64 .x1 = s₀.readReg64 .x3
  x2_eq   : s.readReg64 .x2 = 1#64
  lr_eq   : s.readReg64 .lr = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 164)
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x21_eq  : s.readReg64 .x21 = 1#64
  x22_eq  : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq  : s.readReg64 .x23 = hsp s₀
  x25_eq  : s.readReg64 .x25 = 0#64
  ist_eq  : s.mem.readBytes (hsp s₀ + 64#64) 32 = shaStateBytes (innerState F key)
  ibl_eq  : s.mem.read64 (hsp s₀ + 96#64) = 1#64
  ost_eq  : s.mem.readBytes (hsp s₀ + 104#64) 32 = shaStateBytes (outerState F key)
  obl_eq  : s.mem.read64 (hsp s₀ + 136#64) = 1#64

structure StateH1cX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 164)
  common  : HmacCommonX img s₀ s
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x21_eq  : s.readReg64 .x21 = 1#64
  x22_eq  : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq  : s.readReg64 .x23 = hsp s₀
  x25_eq  : s.readReg64 .x25 = 0#64
  b0_eq   : s.mem.read8 (hsp s₀) = byte
  ist_eq  : s.mem.readBytes (hsp s₀ + 64#64) 32 = shaStateBytes (innerState F key)
  ibl_eq  : s.mem.read64 (hsp s₀ + 96#64) = 1#64
  ost_eq  : s.mem.readBytes (hsp s₀ + 104#64) 32 = shaStateBytes (outerState F key)
  obl_eq  : s.mem.read64 (hsp s₀ + 136#64) = 1#64

structure StateH1pX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% "memset")
  common  : HmacCommonX img s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 146#64
  x1_eq   : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq   : s.readReg64 .x2 = 62#64
  lr_eq   : s.readReg64 .lr = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 388)
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

structure StateH2X (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 388)
  common : HmacCommonX img s₀ s
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

structure StateH2cX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% "sha2::sha256::compress256")
  common  : HmacCommonX img s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 208#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 304#64
  x2_eq   : s.readReg64 .x2 = 1#64
  lr_eq   : s.readReg64 .lr = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 492)
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq  : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq  : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq  : s.readReg64 .x23 = 128#64
  ist_eq  : s.mem.readBytes (hsp s₀ + 208#64) 32 = shaStateBytes (innerState F key)
  iblk_eq : s.mem.readBytes (hsp s₀ + 304#64) 64 = innerLastBlock [byte]
  ost_eq  : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq  : s.mem.read64 (hsp s₀ + 280#64) = 1#64

structure StateH3X (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 492)
  common : HmacCommonX img s₀ s
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  x21_eq : s.readReg64 .x21 = hsp s₀ + 208#64
  x22_eq : s.readReg64 .x22 = hsp s₀ + 144#64
  x23_eq : s.readReg64 .x23 = 128#64
  hi0    : s.mem.read32 (hsp s₀ + 208#64) = (innerDigest F key byte).get 0
  hi1    : s.mem.read32 (hsp s₀ + 212#64) = (innerDigest F key byte).get 1
  hi2    : s.mem.read32 (hsp s₀ + 216#64) = (innerDigest F key byte).get 2
  hi3    : s.mem.read32 (hsp s₀ + 220#64) = (innerDigest F key byte).get 3
  hi4    : s.mem.read32 (hsp s₀ + 224#64) = (innerDigest F key byte).get 4
  hi5    : s.mem.read32 (hsp s₀ + 228#64) = (innerDigest F key byte).get 5
  hi6    : s.mem.read32 (hsp s₀ + 232#64) = (innerDigest F key byte).get 6
  hi7    : s.mem.read32 (hsp s₀ + 236#64) = (innerDigest F key byte).get 7
  ost_eq : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  obl_eq : s.mem.read64 (hsp s₀ + 280#64) = 1#64

structure StateH3cX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = img.base + bv% (ls_off% "sha2::sha256::compress256")
  common  : HmacCommonX img s₀ s
  x0_eq   : s.readReg64 .x0 = hsp s₀ + 248#64
  x1_eq   : s.readReg64 .x1 = hsp s₀ + 304#64
  x2_eq   : s.readReg64 .x2 = 1#64
  lr_eq   : s.readReg64 .lr = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 620)
  x19_eq  : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = hsp s₀ + 144#64
  ost_eq  : s.mem.readBytes (hsp s₀ + 248#64) 32 = shaStateBytes (outerState F key)
  oblk_eq : s.mem.readBytes (hsp s₀ + 304#64) 64 = outerBlock (digestBytes (innerDigest F key byte))

structure StateH4X (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq  : s.pc = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 620)
  common : HmacCommonX img s₀ s
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x20_eq : s.readReg64 .x20 = hsp s₀ + 144#64
  ho0    : s.mem.read32 (hsp s₀ + 248#64) = (outerDigest F key byte).get 0
  ho1    : s.mem.read32 (hsp s₀ + 252#64) = (outerDigest F key byte).get 1
  ho2    : s.mem.read32 (hsp s₀ + 256#64) = (outerDigest F key byte).get 2
  ho3    : s.mem.read32 (hsp s₀ + 260#64) = (outerDigest F key byte).get 3
  ho4    : s.mem.read32 (hsp s₀ + 264#64) = (outerDigest F key byte).get 4
  ho5    : s.mem.read32 (hsp s₀ + 268#64) = (outerDigest F key byte).get 5
  ho6    : s.mem.read32 (hsp s₀ + 272#64) = (outerDigest F key byte).get 6
  ho7    : s.mem.read32 (hsp s₀ + 276#64) = (outerDigest F key byte).get 7

structure StateH4bX (img : Obj.Image) (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  frz    : img.FrozenLoaded s
  sym    : s.symtab = img.symtab
  pc_eq  : s.pc = img.base + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" + 744)
  status : s.status = .Running
  sp_eq  : s.sp = hsp s₀
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  saved  : HmacSaved s₀ (hsp s₀) s.mem
  out_eq : s.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key [byte]
  frame  : S2Frame s₀.mem s.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 17408#64, 17408)]

structure StateH5X (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (byte : BitVec 8) (s₀ s : State) : Prop where
  pc_eq   : s.pc = s₀.readReg64 .lr
  status  : s.status = .Running
  callee  : CalleeSaved s₀ s
  out_eq  : s.mem.readBytes (s₀.readReg64 .x0) 32 = hmacWith F key [byte]
  frame   : S2Frame s₀.mem s.mem [(s₀.readReg64 .x0, 32), (s₀.sp - 17408#64, 17408)]

theorem seg0a_runsTo_ext {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key inp : List (BitVec 8)} {s₀ : State}
    (hpre : HmacPreX img F key inp s₀) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀ (StateH0X img s₀) := by
  have hfrz := hpre.frz
  have hsym := hpre.sym
  refine runsToE_of_runsTo_with_inv (tripleRatchetProgAtExt img.base ext) hfrz hsym ?_
  generalize hPost : (fun s' => img.FrozenLoaded s' → s'.symtab = img.symtab → StateH0X img s₀ s') = Post
  have hpc := hpre.pc_eq
  have hstat := hpre.status
  have hal0 := hpre.sp_aligned
  have hal_hsp : ((s₀.sp - 480#64) &&& 0b1111#64) = 0#64 := hsp_align hal0
  have hrw_hsp : s₀.mem.RW (s₀.sp - 480#64) 480 :=
    hpre.rw_stack.sub (by clear * -; bv_omega)
  iterate 13 sess_step
  subst hPost
  refine _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo.refl ?_
  intro hfrz' hsym'
  refine {
    pc_eq := by simp only [arm64_norm, hpc]
    common := {
      frz := hfrz'
      sym := hsym'
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
        refine s2Frame_trans_r7b_stack1024 (S2Frame.refl s₀.mem _) ?_
        repeat refine Frame.write64_stack1024 ?_ _ _ (by clear * -; bv_omega)
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

theorem seg1a_runsTo_ext {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key inp : List (BitVec 8)} {s₀ s : State}
    (hpre : HmacPreX img F key inp s₀)
    (hs : StateH1X img F key s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH1mX img F key s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx20, hx21, htag, hhmac⟩
  refine runsToE_of_runsTo_with_inv (tripleRatchetProgAtExt img.base ext) hfrz hsym ?_
  generalize hPost : (fun s' => img.FrozenLoaded s' → s'.symtab = img.symtab → StateH1mX img F key s₀ s') = Post
  rcases hhmac with ⟨_, _, hpos, hin, hibl, hout, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    (hframe.rw_of_rw _ _ hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
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
  refine _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo.refl ?_
  intro hfrz' hsym'
  refine {
    pc_eq := by simp only [arm64_norm, hpc]
    common := {
      frz := hfrz'
      sym := hsym'
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
        refine s2Frame_trans_r7b_stack1024 hframe ?_
        repeat refine Frame.write64_stack1024 ?_ _ _
        exact Frame.refl s.mem _
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

theorem seg1b1_pre_runsTo_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH1mX img F key s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH1cX img F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx0, hx1, hx2, hlr, hx19, hx21, hx22, hx23, hx25, hist, hibl, host, hobl⟩
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_stack : RW s.mem (s₀.sp - 17408#64) 17408 :=
    hframe.rw_of_rw _ _ hpre.rw_stack
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    hrw_stack.sub (by unfold hsp; clear * -; bv_omega)
  have hinp_s : s.mem.readBytes (s₀.readReg64 .x3) 1 = [byte] := by
    rw [hframe.readBytes_eq hpre.rw_inp (by simp [hpre.disj_inp_stack.symm]) (by decide), hpre.inp_eq]
  have hrw_inp_s : RW s.mem (s₀.readReg64 .x3) 1 :=
    hframe.rw_of_rw _ _ hpre.rw_inp
  have hsp_ext_eq : s.sp - BitVec.ofNat 64 extHookStack = hsp s₀ - 16384#64 := by
    rw [hsp_eq]; rfl
  have hrw_stk_ext : RW s.mem (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]
    exact hrw_stack.sub (by unfold hsp extHookStack; clear * -; bv_omega)
  have hd_dst_src : DisjointRegions (hsp s₀) 1 (s₀.readReg64 .x3) 1 :=
    (hpre.disj_inp_stack.sub_right (hsp s₀) ⟨by decide, by unfold hsp; clear * -; bv_omega⟩).symm
  have hd_dst_stk : DisjointRegions (hsp s₀) 1 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega
  have hd_src_stk : DisjointRegions (s₀.readReg64 .x3) 1 (s.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp_ext_eq]
    exact hpre.disj_inp_stack.sub_right (hsp s₀ - 16384#64)
      ⟨by decide, by unfold hsp extHookStack; clear * -; bv_omega⟩
  have hrun := memcpy_subroutine_runsTo hMemcpy
    (bs := [byte]) hfrz hsym hpc hstat hx0 hx1 (by rw [hx2]; rfl) hinp_s
    (hrw_hsp.sub (by clear * -; simp)) hrw_inp_s hrw_stk_ext
    hd_dst_src hd_dst_stk hd_src_stk (by rw [hsp_eq]; exact hal_hsp)
  refine runsToE_mono_with_inv hrun hfrz hsym fun s₁ hfrz₁ hsym₁ hs₁ => ?_
  rcases hs₁ with ⟨hpc₁, hstat₁, hcc₁, _, hdst₁, _, hfr_mc⟩
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at hfr_mc
  rw [hlr] at hpc₁
  have hb0 : s₁.mem.read8 (hsp s₀) = byte := by
    have h1 : s₁.mem.readBytes (hsp s₀) 1 = [s₁.mem.read8 (hsp s₀)] := by
      simp [Memory.readBytes, BitVec.add_zero]
    exact List.head_eq_of_cons_eq (h1.symm.trans hdst₁)
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
      saved := hmacSaved_of_s2Frame hsaved (hrw_hsp.sub (by clear * -; bv_omega)) hfr_mc (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · unfold hsp DisjointRegions; clear * -; bv_omega
        · rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega)
      frame := s2Frame_trans_pair_stk17408 hframe hfr_mc
        (by unfold hsp; clear * -; bv_omega)
        (by rw [hsp_ext_eq]; unfold hsp extHookStack; clear * -; bv_omega)
    }
    x19_eq := hcc₁.2.1.trans hx19
    x21_eq := hcc₁.2.2.2.1.trans hx21
    x22_eq := hcc₁.2.2.2.2.1.trans hx22
    x23_eq := hcc₁.2.2.2.2.2.1.trans hx23
    x25_eq := hcc₁.2.2.2.2.2.2.2.1.trans hx25
    b0_eq := hb0
    ist_eq := (hfr_mc.readBytes_eq (hread_hsp 64#64 32 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold hsp DisjointRegions; clear * -; bv_omega
      · rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega) (by decide)).trans hist
    ibl_eq := (hfr_mc.read64_eq (hread_hsp 96#64 8 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold hsp DisjointRegions; clear * -; bv_omega
      · rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega)).trans hibl
    ost_eq := (hfr_mc.readBytes_eq (hread_hsp 104#64 32 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold hsp DisjointRegions; clear * -; bv_omega
      · rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega) (by decide)).trans host
    obl_eq := (hfr_mc.read64_eq (hread_hsp 136#64 8 (by decide)) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · unfold hsp DisjointRegions; clear * -; bv_omega
      · rw [hsp_ext_eq]; unfold hsp extHookStack DisjointRegions; clear * -; bv_omega)).trans hobl
  }

theorem seg1b1_post_runsTo_ext {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {ext : String → Option (State → State)} {key : List (BitVec 8)} {byte : BitVec 8}
    {s₀ s : State}
    (hpre : HmacPreX img F key [byte] s₀)
    (hs : StateH1cX img F key byte s₀ s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (StateH1pX img F key byte s₀) := by
  rcases hs with ⟨hpc, ⟨hfrz, hsym, hstat, hsp_eq, hx29, hx27, hsaved, hframe⟩,
    hx19, hx21, hx22, hx23, hx25, hb0, hist, hibl, host, hobl⟩
  refine runsToE_of_runsTo_with_inv (tripleRatchetProgAtExt img.base ext) hfrz hsym ?_
  generalize hPost : (fun s' => img.FrozenLoaded s' → s'.symtab = img.symtab → StateH1pX img F key byte s₀ s') = Post
  have hal_hsp : (hsp s₀ &&& 0b1111#64) = 0#64 := hsp_align hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 480 :=
    (hframe.rw_of_rw _ _ hpre.rw_stack).sub (by clear * -; unfold hsp; bv_omega)
  iterate 25 sess_step
  subst hPost
  refine _root_.CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo.refl ?_
  intro hfrz' hsym'
  refine ⟨?_, ⟨hfrz', hsym', ?_, ?_, ?_, ?_, ?_, ?_⟩,
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
    refine s2Frame_trans_r7b_stack1024 hframe ?_
    refine Frame.write8_stack1024 ?_ _ _
    iterate 18 refine Frame.write64_stack1024 ?_ _ _
    refine Frame.write8_stack1024 ?_ _ _
    exact Frame.refl s.mem _
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
    simp (config := { decide := true }) only [BitVec.add_assoc, BitVec.reduceAdd, arm64_norm, hb0]
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

end CryptoVerification.Cli.LibsignalTripleRatchet.ExtHmacX
