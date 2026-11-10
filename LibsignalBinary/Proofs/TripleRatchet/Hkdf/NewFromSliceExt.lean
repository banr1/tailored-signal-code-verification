/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.NewFromSliceStepsExt
import ProofLib.SepLogic.HeapIntro

/-!
# Extended-Stack Verification of `Hmac<Sha256>::new_from_slice`

Proves `NewFromSliceOkExt'` for `<Hmac<Sha256> as KeyInit>::new_from_slice` on
`tripleRatchetProgAtExt` from `memcpy` and `compress256` contracts, along with `RunsToE`
call bridges for HKDF `extract`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsExt

section BlSteps

open Arm64 ProofLib CryptoVerification.LibsignalTripleRatchet

theorem nfs_bl_compress1_ext {b : BitVec 64} {ext : String → Option (State → State)} {s : State}
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260))
    (hstat : s.status = .Running) :
    LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1 = (s.writeReg64 .lr (b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1264))).setPC (b + bv% (ls_off% "sha2::sha256::compress256"))) := by
  s2_step
  exact LibsignalTripleRatchet.RunsTo.refl rfl

theorem nfs_bl_compress2_ext {b : BitVec 64} {ext : String → Option (State → State)} {s : State}
    (hpc : s.pc = b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 2060))
    (hstat : s.status = .Running) :
    LibsignalTripleRatchet.RunsTo (tripleRatchetProgAtExt b ext) s (fun s1 =>
      s1 = (s.writeReg64 .lr (b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 2064))).setPC (b + bv% (ls_off% "sha2::sha256::compress256"))) := by
  s2_step
  exact LibsignalTripleRatchet.RunsTo.refl rfl

end BlSteps

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.CBC
open CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsSteps
open ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

theorem RunsToE.of_runsTo {prog : Program} {s₀ : State} {P : State → Prop}
    (h : CryptoHmacSha256.RunsTo prog s₀ P) : RunsToE prog s₀ P := by
  intro hL
  obtain ⟨sf, hst, htr, hvregs, hP, hLf⟩ := h hL
  exact ⟨sf, hst, ⟨htr, hvregs⟩, hP, hLf⟩

theorem RunsToE.mono_traceEq {prog : Program} {s₀ : State} {P Q : State → Prop}
    (h : RunsToE prog s₀ P)
    (hPQ : ∀ sf, LibsignalTripleRatchet.TraceEq s₀ sf → P sf → Q sf) :
    RunsToE prog s₀ Q := by
  intro hL
  obtain ⟨sf, hst, htr, hP, hLf⟩ := h hL
  exact ⟨sf, hst, htr, hPQ sf htr hP, hLf⟩

theorem S2Frame.readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (h : S2Frame m₁ m₂ regs) {a : BitVec 64} {n : ℕ} (hread : m₁.Readable a n)
    (hd : ∀ r ∈ regs, DisjointRegions r.1 r.2 a n) (hn : n ≤ 2 ^ 64 := by decide) :
    m₂.readBytes a n = m₁.readBytes a n := by
  refine Memory.readBytes_congr_region hn fun b hb => ?_
  exact h.1 b (hread b hb).1 (hread b hb).2 fun r hr_mem => (hd r hr_mem).outside hb hn

theorem s2Frame_of_r7b_frame_16928 {out sp : BitVec 64} {m₁ m₂ : Memory}
    (hf : Frame m₁ m₂ [(out, 0x98), (sp - 544#64, 544)]) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  refine (S2Frame.of_frame hf).mono fun a ha r hr => ?_
  have hout := ha (out, 0x98) (by simp)
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hout
  · clear * - hstk
    simp only [OutsideRegion] at hstk ⊢
    bv_omega

theorem s2Frame_of_r7b_stack_frame_16928 {out sp : BitVec 64} {m₁ m₂ : Memory}
    (hf : Frame m₁ m₂ [(sp - 544#64, 544)]) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  refine (S2Frame.of_frame hf).mono fun a ha r hr => ?_
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_singleton] at hr
  subst hr
  clear * - hstk
  simp only [OutsideRegion] at hstk ⊢
  bv_omega

theorem s2Frame_of_hook_frame_16928 {out sp nfsSp_sp off : BitVec 64} {sz : ℕ} {m₁ m₂ : Memory}
    (hf : S2Frame m₁ m₂ [(nfsSp_sp + off, sz), (nfsSp_sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hsp : nfsSp_sp = sp - 544#64)
    (hoff : off.toNat + sz ≤ 544) :
    S2Frame m₁ m₂ [(out, 0x98), (sp - 16928#64, 16928)] := by
  subst hsp
  refine hf.mono fun a ha r hr => ?_
  have hstk := ha (sp - 16928#64, 16928) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · clear * - hstk hoff
    simp only [OutsideRegion] at hstk ⊢
    bv_omega
  · clear * - hstk
    simp only [OutsideRegion, extHookStack] at hstk ⊢
    bv_omega

theorem s2Frame_hook_readBytes_stack_eq {sp off k : BitVec 64} {sz n : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : 0 < n ∧ k.toNat + n ≤ 544)
    (hd_off_k : sz ≤ (k - off).toNat ∧ n ≤ (off - k).toNat) :
    m'.readBytes (sp + k) n = m.readBytes (sp + k) n := by
  have hrw_k : RW m (sp + k) n := hrw_stk.sub (by have := hk.2; clear * - this; bv_omega)
  refine hf.readBytes_eq hrw_k (fun r hr => ?_) (by have := hk.2; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases hd_off_k with ⟨h1, h2⟩
    clear * - h1 h2
    simp only [DisjointRegions]
    bv_omega
  · exact (hd_stk_ext.sub_left (sp + k) ⟨hk.1, by have := hk.2; clear * - this; bv_omega⟩).symm

theorem s2Frame_hook_read64_stack_eq {sp off k : BitVec 64} {sz : ℕ} {m m' : Memory}
    (hf : S2Frame m m' [(sp + off, sz), (sp - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hrw_stk : m.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hk : k.toNat + 8 ≤ 544)
    (hd_off_k : sz = 0 ∨ (sz ≤ (k - off).toNat ∧ 8 ≤ (off - k).toNat)) :
    m'.read64 (sp + k) = m.read64 (sp + k) := by
  have hrw_k : RW m (sp + k) 8 := hrw_stk.sub (by clear * - hk; bv_omega)
  refine Memory.read64_congr fun b hb => ?_
  obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_k b hb)
  have hr : (m.perm b).r = true := by rw [hp]; rfl
  refine hf.1 b hr hlf fun r hr_mem => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
  rcases hr_mem with rfl | rfl
  · rcases hd_off_k with rfl | ⟨h1, h2⟩
    · simp [OutsideRegion]
    · have hd : DisjointRegions (sp + off) sz (sp + k) 8 := by
        clear * - h1 h2; simp only [DisjointRegions]; bv_omega
      exact hd.outside hb (by decide)
  · exact (hd_stk_ext.sub_left (sp + k) ⟨by decide, by clear * - hk; bv_omega⟩).symm.outside hb (by decide)

theorem NfsSavedStack.of_s2Frame_low {s₀ : State} {m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hs : NfsSavedStack s₀ m)
    (hrw_stk : m.RW (nfsSp s₀) 544)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hf : S2Frame m m' [(nfsSp s₀ + off, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hoff : off.toNat + sz ≤ 432) :
    NfsSavedStack s₀ m' := by
  have hread (k : BitVec 64) (hk : 432 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      m'.read64 (nfsSp s₀ + k) = m.read64 (nfsSp s₀ + k) :=
    s2Frame_hook_read64_stack_eq hf hrw_stk hd_stk_ext hk.2
      (by
        by_cases hsz : sz = 0
        · exact Or.inl hsz
        · refine Or.inr ?_
          rcases hk with ⟨h1, h2⟩
          clear * - hsz hoff h1 h2
          constructor <;> bv_omega)
  exact {
    m432 := (hread 432#64 (by decide)).trans hs.m432
    m464 := (hread 464#64 (by decide)).trans hs.m464
    m472 := (hread 472#64 (by decide)).trans hs.m472
    m480 := (hread 480#64 (by decide)).trans hs.m480
    m496 := (hread 496#64 (by decide)).trans hs.m496
    m504 := (hread 504#64 (by decide)).trans hs.m504
    m512 := (hread 512#64 (by decide)).trans hs.m512
    m520 := (hread 520#64 (by decide)).trans hs.m520
    m528 := (hread 528#64 (by decide)).trans hs.m528
    m536 := (hread 536#64 (by decide)).trans hs.m536
  }

theorem nfsSavedStack_write64_432_of_s2Frame {s₀ : State} {m m' : Memory} {sz : ℕ}
    (hs : NfsSavedStack s₀ (m.write64 (nfsSp s₀ + 432#64) 1#64))
    (hrw_stk : m.RW (nfsSp s₀) 544)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hf : S2Frame m m' [(nfsSp s₀ + 112#64, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hsz : sz ≤ 64) :
    NfsSavedStack s₀ (m'.write64 (nfsSp s₀ + 432#64) 1#64) := by
  have hread (k : BitVec 64) (hk : 464 ≤ k.toNat ∧ k.toNat + 8 ≤ 544) :
      (m'.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) =
      (m.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) := by
    have h1 : (m'.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) = m'.read64 (nfsSp s₀ + k) := by
      refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m' (nfsSp s₀ + 432#64) 1#64)) ?_
      rcases hk with ⟨hk1, hk2⟩
      clear * - hk1 hk2; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega
    have h2 : (m.write64 (nfsSp s₀ + 432#64) 1#64).read64 (nfsSp s₀ + k) = m.read64 (nfsSp s₀ + k) := by
      refine Frame.read64_eq (agreesOutside_toFrame (AgreesOutside.write64_self m (nfsSp s₀ + 432#64) 1#64)) ?_
      rcases hk with ⟨hk1, hk2⟩
      clear * - hk1 hk2; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega
    rw [h1, h2]
    exact s2Frame_hook_read64_stack_eq hf hrw_stk hd_stk_ext hk.2
      (by
        by_cases h0 : sz = 0
        · exact Or.inl h0
        · refine Or.inr ?_
          rcases hk with ⟨hk1, hk2⟩
          clear * - h0 hsz hk1 hk2
          constructor <;> bv_omega)
  exact {
    m432 := Memory.read64_write64_same m' (nfsSp s₀ + 432#64) 1#64
    m464 := (hread 464#64 (by decide)).trans hs.m464
    m472 := (hread 472#64 (by decide)).trans hs.m472
    m480 := (hread 480#64 (by decide)).trans hs.m480
    m496 := (hread 496#64 (by decide)).trans hs.m496
    m504 := (hread 504#64 (by decide)).trans hs.m504
    m512 := (hread 512#64 (by decide)).trans hs.m512
    m520 := (hread 520#64 (by decide)).trans hs.m520
    m528 := (hread 528#64 (by decide)).trans hs.m528
    m536 := (hread 536#64 (by decide)).trans hs.m536
  }

theorem NfsMemInv.of_s2Frame_low {b : BitVec 64} {s₀ : State} {m₀ m m' : Memory}
    {off : BitVec 64} {sz : ℕ}
    (hM : NfsMemInv b (s₀.setMem m₀) m)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀ - 16384#64) 16384)
    (hf : S2Frame m m' [(nfsSp s₀ + off, sz), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)])
    (hoff : 0 < sz ∧ off.toNat + sz ≤ 432) :
    NfsMemInv b (s₀.setMem m') m' := by
  have hrw_stk : m.RW (nfsSp s₀) 544 := hM.rw_stack
  have hrw_out : m.RW (s₀.readReg64 .x0) 0x98 := hM.rw_out
  have hdisj_iv : DisjointRegions (nfsSp s₀ + off) sz (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
    have hd_iv_stk : DisjointRegions (b + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀) 544 := hM.disj_iv_stack
    refine hd_iv_stk.symm.sub_left (nfsSp s₀ + off) ⟨hoff.1, ?_⟩
    have := hoff.2
    clear * - this
    bv_omega
  exact {
    rw_stack := hf.rw_of_rw _ _ hrw_stk
    rw_out := hf.rw_of_rw _ _ hrw_out
    readable_iv := fun a ha => hf.2.2 a (hM.readable_iv a ha).1 (hM.readable_iv a ha).2
    iv_bytes := (S2Frame.readBytes_eq_of_readable hf hM.readable_iv (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdisj_iv
      · exact hd_iv_ext.symm) (by decide)).trans hM.iv_bytes
    disj_iv_stack := hM.disj_iv_stack
    disj_out_stack := hM.disj_out_stack
    saved := NfsSavedStack_setMem_iff.mpr
      (NfsSavedStack.of_s2Frame_low (NfsSavedStack_setMem_iff.mp hM.saved) hrw_stk hd_stk_ext hf hoff.2)
    frame := Frame.refl m' _
  }

theorem readBytes_64_eq_keyBlock_of_s2Frame {sp : BitVec 64} {m1 m2 : Memory} {key : List (BitVec 8)}
    (hlen : key.length ≤ 64)
    (hrw_stk1 : m1.RW sp 544)
    (hd_stk_ext : DisjointRegions sp 544 (sp - 16384#64) 16384)
    (hzero1 : m1.readBytes (sp + 112#64) 64 = List.replicate 64 0#8)
    (hkey2 : m2.readBytes (sp + 112#64) key.length = key)
    (hf12 : S2Frame m1 m2 [(sp + 112#64, key.length), (sp - BitVec.ofNat 64 extHookStack, extHookStack)]) :
    m2.readBytes (sp + 112#64) 64 = keyBlock key := by
  have h64 : 64 = key.length + (64 - key.length) := (Nat.add_sub_of_le hlen).symm
  have hsplit2 : m2.readBytes (sp + 112#64) 64 =
      m2.readBytes (sp + 112#64) key.length ++
        m2.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
    (congrArg (m2.readBytes (sp + 112#64)) h64).trans
      (LibsignalAesCbc.Run.Bytes.readBytes_add m2 (sp + 112#64) key.length (64 - key.length))
  have hsplit1 : m1.readBytes (sp + 112#64) 64 =
      m1.readBytes (sp + 112#64) key.length ++
        m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
    (congrArg (m1.readBytes (sp + 112#64)) h64).trans
      (LibsignalAesCbc.Run.Bytes.readBytes_add m1 (sp + 112#64) key.length (64 - key.length))
  have htail1 : m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) =
      List.replicate (64 - key.length) 0#8 := by
    have hd := congrArg (List.drop key.length) (hsplit1.symm.trans hzero1)
    rwa [List.drop_left' (Memory.readBytes_length _ _ _), List.drop_replicate] at hd
  have htail2 : m2.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) =
      m1.readBytes ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) := by
    have hrw_tail : RW m1 ((sp + 112#64) + BitVec.ofNat 64 key.length) (64 - key.length) :=
      hrw_stk1.sub (by clear * - hlen; bv_omega)
    refine Memory.readBytes_congr_region (by omega) fun b hb => ?_
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hrw_tail b hb)
    have hr : (m1.perm b).r = true := by rw [hp]; rfl
    refine hf12.1 b hr hlf fun r hr_mem => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_mem
    rcases hr_mem with rfl | rfl
    · clear * - hlen hb
      simp only [InRegion, OutsideRegion] at hb ⊢
      bv_omega
    · have hb_stk : InRegion sp 544 b := by
        clear * - hlen hb
        simp only [InRegion] at hb ⊢
        bv_omega
      exact hd_stk_ext.symm.outside hb_stk (by decide)
  rw [hsplit2, hkey2, htail2, htail1]
  rfl

theorem nfs_compress1_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec F extHookStack).inImage img))
    {s₀ s : State} {m₀ : Memory} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀ - 16384#64) 16384)
    (hrw_extstk : RW s.mem (nfsSp s₀ - 16384#64) 16384)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1260))
    (hstat : s.status = .Running)
    (hR : NfsRegInv img.base (s₀.setMem m₀) s)
    (hM : NfsMemInv img.base (s₀.setMem m₀) s.mem)
    (hx0 : s.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1 : s.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hist : s.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV)
    (hblk : s.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8))
    (hivsw : s.mem.readBytes (nfsSp s₀) 32 =
      (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      NfsOpadPostHook img.base F (s₀.setMem s'.mem) key s' ∧
      RW s'.mem (nfsSp s₀ - 16384#64) 16384 ∧
      S2Frame s.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  have hbl : RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s1 =>
      s1 = (s.writeReg64 .lr (img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 1264))).setPC (img.base + bv% (ls_off% "sha2::sha256::compress256"))) :=
    Extract.RunsTo.toE (nfs_bl_compress1_ext hpc hstat)
  refine hbl.trans_full fun s1 hs1 hkf1 hsym1 => ?_
  have hfrz1 : img.FrozenLoaded s1 := hfrz.of_keepsFrozen hkf1
  have hsym1' : s1.symtab = img.symtab := hsym1.trans hsym
  have hmem1 : s1.mem = s.mem := by rw [hs1]; rfl
  have hsp1 : s1.sp = nfsSp s₀ := by rw [hs1]; exact hR.sp_eq
  have hpc1 : s1.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") := by rw [hs1]; rfl
  have hstat1 : s1.status = .Running := by rw [hs1]; exact hstat
  have hx0_1 : s1.readReg64 .x0 = nfsSp s₀ + 400#64 := by rw [hs1]; exact hx0
  have hx1_1 : s1.readReg64 .x1 = nfsSp s₀ + 288#64 := by rw [hs1]; exact hx1
  have hx2_1 : s1.readReg64 .x2 = 1#64 := by rw [hs1]; exact hx2
  have hist1 : s1.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV := by
    rw [hmem1]; exact hist
  have hblk1 : s1.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) := by
    rw [hmem1]; exact hblk
  have hal1 : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact hR.sp_align
  have hrw_stk : RW s.mem (nfsSp s₀) 544 := hM.rw_stack
  have hrw_st : RW s1.mem (nfsSp s₀ + 400#64) 32 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hrw_blk : RW s1.mem (nfsSp s₀ + 288#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hd_st_blk : DisjointRegions (nfsSp s₀ + 400#64) 32 (nfsSp s₀ + 288#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_stk : DisjointRegions (nfsSp s₀ + 400#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 400#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_stk : DisjointRegions (nfsSp s₀ + 288#64) 64
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 288#64) ⟨by decide, by clear * -; bv_omega⟩
  have hcomp := compress256_one_subroutine_runsTo hComp (by decide)
    hfrz1 hsym1' hpc1 hstat1 hx0_1 hx1_1 hx2_1 hist1 hblk1
    hrw_st hrw_blk (by rw [hmem1, hsp1]; exact hrw_extstk)
    hd_st_blk hd_st_stk hd_blk_stk hal1
  refine hcomp.mono fun s' ⟨hpc', hstat', hcc, hist', hblk', hfr⟩ => ?_
  have hfr' : S2Frame s.mem s'.mem [(nfsSp s₀ + 400#64, 32),
      (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hmem1, hsp1] at hfr
  subst hs1
  refine ⟨{
    pc_eq := hpc'
    status := hstat'
    regInv := NfsRegInv_setMem_iff.mpr (nfsRegInv_of_cc (NfsRegInv_setMem_iff.mp hR) hcc)
    memInv := NfsMemInv.of_s2Frame_low hM hd_stk_ext hd_iv_ext hfr' ⟨by decide, by decide⟩
    ist_eq := hist'
    blk_eq := hblk'
    ivsw_eq := by
      have h0 : s'.mem.readBytes (nfsSp s₀ + 0#64) 32 = s.mem.readBytes (nfsSp s₀ + 0#64) 32 :=
        s2Frame_hook_readBytes_stack_eq hfr' hrw_stk hd_stk_ext ⟨by decide, by decide⟩ (by decide)
      rw [BitVec.add_zero] at h0
      exact h0.trans hivsw
  }, hfr'.rw_of_rw _ _ hrw_extstk, s2Frame_of_hook_frame_16928 hfr' rfl (by decide)⟩

theorem nfs_compress2_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec F extHookStack).inImage img))
    {s₀ s : State} {m₀ : Memory} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hd_stk_ext : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384)
    (hd_iv_ext : DisjointRegions (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀ - 16384#64) 16384)
    (hrw_extstk : RW s.mem (nfsSp s₀ - 16384#64) 16384)
    (hs : NfsPreCompress2 img.base F (s₀.setMem m₀) key s) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      NfsPostCompress2 img.base F (s₀.setMem s'.mem) key s' ∧
      S2Frame s.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  have hR := hs.regInv
  have hM := hs.memInv
  have hrw_stk : RW s.mem (nfsSp s₀) 544 := hM.rw_stack
  have hbl : RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s1 =>
      s1 = (s.writeReg64 .lr (img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]" + 2064))).setPC (img.base + bv% (ls_off% "sha2::sha256::compress256"))) :=
    Extract.RunsTo.toE (nfs_bl_compress2_ext hs.pc_eq hs.status)
  refine hbl.trans_full fun s1 hs1 hkf1 hsym1 => ?_
  have hfrz1 : img.FrozenLoaded s1 := hfrz.of_keepsFrozen hkf1
  have hsym1' : s1.symtab = img.symtab := hsym1.trans hsym
  have hmem1 : s1.mem = s.mem := by rw [hs1]; rfl
  have hsp1 : s1.sp = nfsSp s₀ := by rw [hs1]; exact hR.sp_eq
  have hpc1 : s1.pc = img.base + bv% (ls_off% "sha2::sha256::compress256") := by rw [hs1]; rfl
  have hstat1 : s1.status = .Running := by rw [hs1]; exact hs.status
  have hx0_1 : s1.readReg64 .x0 = nfsSp s₀ + 176#64 := by rw [hs1]; exact hs.x0_eq
  have hx1_1 : s1.readReg64 .x1 = nfsSp s₀ + 288#64 := by rw [hs1]; exact hs.x1_eq
  have hx2_1 : s1.readReg64 .x2 = 1#64 := by rw [hs1]; exact hs.x2_eq
  have host1 : s1.mem.readBytes (nfsSp s₀ + 176#64) 32 = shaStateBytes sha256IV := by
    rw [hmem1]; exact hs.ost_eq
  have hblk1 : s1.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x5c#8) := by
    rw [hmem1]; exact hs.blk_eq
  have hal1 : (s1.sp &&& 15#64) = 0#64 := by rw [hsp1]; exact hR.sp_align
  have hrw_st : RW s1.mem (nfsSp s₀ + 176#64) 32 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hrw_blk : RW s1.mem (nfsSp s₀ + 288#64) 64 := by
    rw [hmem1]; exact hrw_stk.sub (by clear * -; bv_omega)
  have hd_st_blk : DisjointRegions (nfsSp s₀ + 176#64) 32 (nfsSp s₀ + 288#64) 64 := by
    clear * -; simp only [DisjointRegions]; bv_omega
  have hd_st_stk : DisjointRegions (nfsSp s₀ + 176#64) 32
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 176#64) ⟨by decide, by clear * -; bv_omega⟩
  have hd_blk_stk : DisjointRegions (nfsSp s₀ + 288#64) 64
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    exact hd_stk_ext.sub_left (nfsSp s₀ + 288#64) ⟨by decide, by clear * -; bv_omega⟩
  have hcomp := compress256_one_subroutine_runsTo hComp (by decide)
    hfrz1 hsym1' hpc1 hstat1 hx0_1 hx1_1 hx2_1 host1 hblk1
    hrw_st hrw_blk (by rw [hmem1, hsp1]; exact hrw_extstk)
    hd_st_blk hd_st_stk hd_blk_stk hal1
  refine hcomp.mono fun s' ⟨hpc', hstat', hcc, host', hblk', hfr⟩ => ?_
  have hfr' : S2Frame s.mem s'.mem [(nfsSp s₀ + 176#64, 32),
      (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hmem1, hsp1] at hfr
  subst hs1
  refine ⟨{
    pc_eq := hpc'
    status := hstat'
    regInv := NfsRegInv_setMem_iff.mpr (nfsRegInv_of_cc (NfsRegInv_setMem_iff.mp hR) hcc)
    memInv := NfsMemInv.of_s2Frame_low hM hd_stk_ext hd_iv_ext hfr' ⟨by decide, by decide⟩
    ist_eq := (s2Frame_hook_readBytes_stack_eq hfr' hrw_stk hd_stk_ext
      ⟨by decide, by decide⟩ (by decide)).trans hs.ist_eq
    ost_eq := host'
    obl_eq := (s2Frame_hook_read64_stack_eq hfr' hrw_stk hd_stk_ext
      (by decide) (by decide)).trans hs.obl_eq
  }, s2Frame_of_hook_frame_16928 hfr' rfl (by decide)⟩

/-- Full `new_from_slice` execution on `tripleRatchetProgAtExt img.base ext` from `subroutine_ok`
contracts for `memcpy` and `compress256` at `extHookStack = 16384`. -/
theorem new_from_slice_runsToE_ext {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((compress256ExternShaSpec F extHookStack).inImage img))
    {s₀ : State}
    (hfrz : img.FrozenLoaded s₀)
    (hsym : s₀.symtab = img.symtab)
    (hpc : s₀.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_key : RW s₀.mem (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hrw_stk : RW s₀.mem (s₀.sp - 544#64) 544)
    (hrw_extstk : RW s₀.mem (nfsSp s₀ - 16384#64) 16384)
    (hdisj_out_stk : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hdisj_stk_extstk : DisjointRegions (s₀.sp - 544#64) 544 (nfsSp s₀ - 16384#64) 16384)
    (hdisj_key_stk : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hdisj_key_extstk : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (nfsSp s₀ - 16384#64) 16384)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsToE (tripleRatchetProgAtExt img.base ext) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) := by
  intro key
  have hkey_len_eq : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_len : key.length ≤ 64 := hkey_len_eq ▸ hlen
  have hb : (img.base &&& 0xfff#64) = 0#64 := ProofLib.base_aligned_of_loads himg
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV himg hfrz.roData
  have hdisj_iv_stk : DisjointRegions (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀) 544 :=
    disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
  have hdisj_iv_extstk : DisjointRegions (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 (nfsSp s₀ - 16384#64) 16384 :=
    disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_extstk
  refine RunsToE.mono_traceEq (P := fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CryptoHmacSha256.CalleeSaved s₀ sf ∧
      sf.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt sf.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      S2Frame s₀.mem sf.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)]) ?_
    fun sf htr ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, hfr0f⟩ =>
      ⟨hpc_sf, hstat_sf, CryptoHmacSha256.CallingConventionPreserved_of_calleeSaved hcs_sf htr.2,
        hret_sf, hhm_sf, hfr0f⟩
  have hseg0a : RunsToE (tripleRatchetProgAtExt img.base ext) s₀ _ :=
    RunsToE.of_runsTo (nfs_seg0a_ext hpc hstat hlen hb hrw_stk hal)
  refine hseg0a.trans_full fun s1 h1 hkf1 hsym1 => ?_
  rcases h1 with ⟨hpc1, hstat1, hsp1, hal1, hx29_1, hx19_1, hx22_1, hx25_1, hx26_1, hx27_1,
    hx0_1, hx1_1, hx2_1, hlr_1, hzero1, hsaved1, hfr1_r7b⟩
  have hfrz1 : img.FrozenLoaded s1 := hfrz.of_keepsFrozen hkf1
  have hsym1' : s1.symtab = img.symtab := hsym1.trans hsym
  have hfr01 : S2Frame s₀.mem s1.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    s2Frame_of_r7b_stack_frame_16928 hfr1_r7b
  have hrw_stk1 : RW s1.mem (nfsSp s₀) 544 :=
    (Frame.rw_iff hfr1_r7b _ _).mpr hrw_stk
  have hrw_out1 : RW s1.mem (s₀.readReg64 .x0) 0x98 :=
    (Frame.rw_iff hfr1_r7b _ _).mpr hrw_out
  have hrw_extstk1 : RW s1.mem (nfsSp s₀ - 16384#64) 16384 :=
    (Frame.rw_iff hfr1_r7b _ _).mpr hrw_extstk
  have hrw_key1 : RW s1.mem (s₀.readReg64 .x1) key.length :=
    (Frame.rw_iff hfr1_r7b _ _).mpr (hkey_len_eq ▸ hrw_key)
  have hkey_s1 : s1.mem.readBytes (s₀.readReg64 .x1) key.length = key := by
    rw [hkey_len_eq]
    rcases hdisj_key_stk with h0 | hd
    · dsimp only [key]
      rw [h0]
      rfl
    · have hd' : DisjointRegions (nfsSp s₀) 544 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := hd.symm
      exact hfr1_r7b.readBytes_eq (by simp [hd']) (by omega)
  have hd_dst_src1 : key.length = 0 ∨ DisjointRegions (nfsSp s₀ + 112#64) key.length (s₀.readReg64 .x1) key.length := by
    rw [hkey_len_eq]
    rcases hdisj_key_stk with h0 | hd
    · exact Or.inl h0
    · by_cases hkn0 : (s₀.readReg64 .x2).toNat = 0
      · exact Or.inl hkn0
      · have hd' : DisjointRegions (nfsSp s₀) 544 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := hd.symm
        exact Or.inr (hd'.sub_left (nfsSp s₀ + 112#64) ⟨by omega, by clear * - hlen; bv_omega⟩)
  have hd_dst_stk1 : key.length = 0 ∨ DisjointRegions (nfsSp s₀ + 112#64) key.length
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1]
    by_cases hkn0 : key.length = 0
    · exact Or.inl hkn0
    · have hd' : DisjointRegions (nfsSp s₀) 544 (nfsSp s₀ - 16384#64) 16384 := hdisj_stk_extstk
      exact Or.inr (hd'.sub_left (nfsSp s₀ + 112#64) ⟨by omega, by clear * - hkey_len; bv_omega⟩)
  have hd_src_stk1 : key.length = 0 ∨ DisjointRegions (s₀.readReg64 .x1) key.length
      (s1.sp - BitVec.ofNat 64 extHookStack) extHookStack := by
    rw [hsp1, hkey_len_eq]
    exact hdisj_key_extstk
  have hmemcpy1 := memcpy_opt_subroutine_runsTo hMemcpy hfrz1 hsym1' hpc1 hstat1
    hx0_1 hx1_1 (by rw [hx2_1, hkey_len_eq]) hkey_s1
    (hrw_stk1.sub (by clear * - hkey_len; bv_omega)) hrw_key1
    (by rw [hsp1]; exact hrw_extstk1)
    hd_dst_src1 hd_dst_stk1 hd_src_stk1 (by rw [hsp1]; exact hal1)
  refine hmemcpy1.trans_full fun s2 ⟨hpc2, hstat2, hcc12, hx0_2, hdst2, _, hfr12⟩ hkf2 hsym2 => ?_
  rw [hlr_1] at hpc2
  have hfrz2 : img.FrozenLoaded s2 := hfrz1.of_keepsFrozen hkf2
  have hsym2' : s2.symtab = img.symtab := hsym2.trans hsym1'
  have hfr12_stk : S2Frame s1.mem s2.mem
      [(nfsSp s₀ + 112#64, key.length), (nfsSp s₀ - BitVec.ofNat 64 extHookStack, extHookStack)] := by
    rwa [hsp1] at hfr12
  have hfr02 : S2Frame s₀.mem s2.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr01.trans (s2Frame_of_hook_frame_16928 hfr12_stk rfl (by clear * - hkey_len; bv_omega))
  have hkb2 : s2.mem.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    readBytes_64_eq_keyBlock_of_s2Frame hkey_len hrw_stk1 hdisj_stk_extstk hzero1 hdst2 hfr12_stk
  have hsaved2_432 : NfsSavedStack s₀ (s2.mem.write64 (nfsSp s₀ + 432#64) 1#64) :=
    nfsSavedStack_write64_432_of_s2Frame hsaved1 hrw_stk1 hdisj_stk_extstk hfr12_stk hkey_len
  obtain ⟨hro_iv2, hiv_eq2⟩ := rodata_sha256IV himg hfrz2.roData
  have hread_iv2 : s2.mem.Readable (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 :=
    fun a ha => ⟨by rw [(hro_iv2 a ha).1]; rfl, (hro_iv2 a ha).2⟩
  have hA2_432 : AgreesOutside s2.mem (s2.mem.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self s2.mem (nfsSp s₀ + 432#64) 1#64
  have hf2_432 : Frame s2.mem (s2.mem.write64 (nfsSp s₀ + 432#64) 1#64) [(nfsSp s₀ + 432#64, 8)] :=
    agreesOutside_toFrame hA2_432
  have hM2_432 : NfsMemInv img.base (s₀.setMem s2.mem) (s2.mem.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf2_432 _ _).mpr (hfr12_stk.rw_of_rw _ _ hrw_stk1)
    rw_out := (Frame.rw_iff hf2_432 _ _).mpr (hfr12_stk.rw_of_rw _ _ hrw_out1)
    readable_iv := (Frame.readable_iff hf2_432 _ _).mpr hread_iv2
    iv_bytes := by
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8
          (img.base + bv% (ls_str% "kyber_pre_key_pu" + 256)) 32 := by
        clear * - hdisj_iv_stk; simp only [DisjointRegions, nfsSp] at hdisj_iv_stk ⊢; bv_omega
      exact (hf2_432.readBytes_eq (by simp [hd432]) (by decide)).trans hiv_eq2
    disj_iv_stack := hdisj_iv_stk
    disj_out_stack := hdisj_out_stk
    saved := NfsSavedStack_setMem_iff.mpr hsaved2_432
    frame := Frame.of_agreesOutside_stack (Frame.refl s2.mem _) hA2_432 (by decide)
  }
  have hrw_extstk2 : RW s2.mem (nfsSp s₀ - 16384#64) 16384 :=
    hfr12_stk.rw_of_rw _ _ hrw_extstk1
  have hto_c1 : RunsToE (tripleRatchetProgAtExt img.base ext) s2 _ :=
    RunsToE.of_runsTo (nfs_after_memcpy_to_compress1_ext hkey_len hal hb hpc2 hstat2
      (hcc12.1.trans hsp1) hal1
      (hcc12.2.2.2.2.2.2.2.2.2.2.2.1.trans hx29_1)
      (hcc12.2.1.trans hx19_1)
      (hcc12.2.2.2.2.1.trans hx22_1)
      (hcc12.2.2.2.2.2.2.2.1.trans hx25_1)
      (hcc12.2.2.2.2.2.2.2.2.1.trans hx26_1)
      (hcc12.2.2.2.2.2.2.2.2.2.1.trans hx27_1)
      hM2_432 hkb2)
  refine hto_c1.trans_full fun s3 ⟨hpc3, hstat3, hR3, hM3, hx0_3, hx1_3, hx2_3, hist3, hblk3, hivsw3⟩ hkf3 hsym3 => ?_
  have hfrz3 : img.FrozenLoaded s3 := hfrz2.of_keepsFrozen hkf3
  have hsym3' : s3.symtab = img.symtab := hsym3.trans hsym2'
  have hfr23 : S2Frame s2.mem s3.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    s2Frame_of_r7b_frame_16928 hM3.frame
  have hfr03 : S2Frame s₀.mem s3.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr02.trans hfr23
  have hrw_extstk3 : RW s3.mem (nfsSp s₀ - 16384#64) 16384 :=
    (Frame.rw_iff hM3.frame _ _).mpr hrw_extstk2
  have hc1 := nfs_compress1_ext hComp hfrz3 hsym3' hdisj_stk_extstk hdisj_iv_extstk hrw_extstk3
    hpc3 hstat3 hR3 hM3 hx0_3 hx1_3 hx2_3 hist3 hblk3 hivsw3
  refine hc1.trans_full fun s4 ⟨hpost4, hrw_extstk4, hfr34⟩ hkf4 hsym4 => ?_
  have hfrz4 : img.FrozenLoaded s4 := hfrz3.of_keepsFrozen hkf4
  have hsym4' : s4.symtab = img.symtab := hsym4.trans hsym3'
  have hfr04 : S2Frame s₀.mem s4.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr03.trans hfr34
  have hopad : RunsToE (tripleRatchetProgAtExt img.base ext) s4 _ :=
    RunsToE.of_runsTo (nfs_opad_after_compress1_ext hkey_len hpost4)
  refine hopad.trans_full fun s5 hpre5 hkf5 hsym5 => ?_
  have hfrz5 : img.FrozenLoaded s5 := hfrz4.of_keepsFrozen hkf5
  have hsym5' : s5.symtab = img.symtab := hsym5.trans hsym4'
  have hfr45 : S2Frame s4.mem s5.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    s2Frame_of_r7b_frame_16928 hpre5.memInv.frame
  have hfr05 : S2Frame s₀.mem s5.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr04.trans hfr45
  have hrw_extstk5 : RW s5.mem (nfsSp s₀ - 16384#64) 16384 :=
    (Frame.rw_iff hpre5.memInv.frame _ _).mpr hrw_extstk4
  have hc2 := nfs_compress2_ext hComp hfrz5 hsym5' hdisj_stk_extstk hdisj_iv_extstk hrw_extstk5 hpre5
  refine hc2.trans_full fun s6 ⟨hpost6, hfr56⟩ _ _ => ?_
  have hfr06 : S2Frame s₀.mem s6.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 16928#64, 16928)] :=
    hfr05.trans hfr56
  have hep : RunsToE (tripleRatchetProgAtExt img.base ext) s6 _ :=
    RunsToE.of_runsTo (nfs_epilogue_ext (s₀ := s₀.setMem s6.mem) hal hpost6)
  refine hep.mono fun sf ⟨hpc_sf, hstat_sf, hcs_sf, hret_sf, hhm_sf, hfr6f⟩ => ?_
  exact ⟨hpc_sf, hstat_sf,
    ⟨hcs_sf.1, hcs_sf.2⟩,
    hret_sf, hhm_sf, hfr06.trans (s2Frame_of_r7b_frame_16928 hfr6f)⟩

end CryptoVerification.LibsignalTripleRatchet.HkdfExt.NfsExt

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (RW nfsSp HmacSt)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Extract

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

private theorem trExt_fnAddr_newFromSlice (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr newFromSliceName =
      b + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") := by
  unfold tripleRatchetProgAtExt newFromSliceName
  rw [Program.fnAddr_rebase, (ls_lemma% fnOff "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]")]

private theorem hmacInnerInit_eq_innerState_nfs (F : ShaCompress) (key : List (BitVec 8)) :
    hmacInnerInit F key = CryptoHmacSha256.innerState F key := rfl

private theorem hmacOuterInit_eq_outerState_nfs (F : ShaCompress) (key : List (BitVec 8)) :
    hmacOuterInit F key = CryptoHmacSha256.outerState F key := rfl

private theorem isBlock_hmacCoreAt_nil_nfs (F : ShaCompress) (a : BitVec 64) (key : List (BitVec 8)) :
    IsBlock (hmacCoreAt F a key []) a 0x90
      (fun m => HmacSt m a F key []) := by
  have hlen := HkdfExt.shaStateBytes_length
  have b88 := IsBlock.pointsTo64 (a + 0x88#64) 1#64
  have b68 := (IsBlock.pointsToBytes_len (a := a + 0x68#64)
    (hlen (hmacOuterInit F key))).sepConj b88 (by bv_arith) (by decide)
  have b60 := (IsBlock.pointsTo64 (a + 0x60#64) (BitVec.ofNat 64 1)).sepConj b68
    (by bv_arith) (by decide)
  have b40 := (IsBlock.pointsToBytes_len (a := a + 0x40#64)
    (hlen (hmacInnerInit F key))).sepConj b60 (by bv_arith) (by decide)
  have b3f := (IsBlock.pointsTo8 (a + 0x3f#64) (BitVec.ofNat 8 0)).sepConj b40
    (by bv_arith) (by decide)
  have bpad := (IsBlock.memRegion (a + BitVec.ofNat 64 0) 63).sepConj b3f
    (by bv_arith) (by decide)
  have bnil := (IsBlock.pointsToBytes a []).sepConj bpad (by simp) (by decide)
  have b := IsBlock.pure_sepConj (φ := ([] : List (BitVec 8)).length < 64) fun _ => bnil
  refine b.cast rfl fun m => ?_
  simp [HmacSt, hlen, hmacInnerInit_eq_innerState_nfs, hmacOuterInit_eq_outerState_nfs]

private theorem isBlock_nfsResult (F : ShaCompress) (ret : BitVec 64) (key : List (BitVec 8)) :
    IsBlock ((ret ↦₆₄ 0#64) ∗ hmacCoreAt F (ret + 8#64) key []) ret 0x98
      (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) F key []) :=
  (IsBlock.pointsTo64 ret 0#64).sepConj (isBlock_hmacCoreAt_nil_nfs F (ret + 8#64) key) rfl
    (by decide)

private theorem satisfies_three_blocks_nfs {P1 P2 P3 : SepProp} {b1 b2 b3 : BitVec 64} {n1 n2 n3 : ℕ}
    {Φ1 Φ2 Φ3 : Memory → Prop} {m : Memory}
    (hb1 : IsBlock P1 b1 n1 Φ1) (hb2 : IsBlock P2 b2 n2 Φ2) (hb3 : IsBlock P3 b3 n3 Φ3)
    (hΦ1 : Φ1 m) (hΦ2 : Φ2 m) (hΦ3 : Φ3 m)
    (hrw1 : RW m b1 n1) (hrw2 : RW m b2 n2) (hrw3 : RW m b3 n3)
    (hd12 : DisjointRegions b1 n1 b2 n2)
    (hd13 : DisjointRegions b1 n1 b3 n3)
    (hd23 : DisjointRegions b2 n2 b3 n3)
    (hn2 : n2 ≤ 2 ^ 64) (hn3 : n3 ≤ 2 ^ 64) :
    m ⊨ P1 ∗ P2 ∗ P3 :=
  HkdfExt.satisfies_three_blocks_opt hb1 hb2 hb3 hΦ1 hΦ2 hΦ3 hrw1 hrw2 hrw3
    (Or.inr (Or.inr hd12)) (Or.inr (Or.inr hd13)) (Or.inr (Or.inr hd23)) hn2 hn3

/-- `Hmac<Sha256>::new_from_slice` satisfies `NewFromSliceOkExt' img C ext` from `subroutine_ok`
contracts for `memcpy` and `compress256`. -/
theorem new_from_slice_ok_ext'_of_stubs {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hMemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "memcpy"))
      ((sessionMemcpySpec extHookStack).inImage img))
    (hComp : subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + bv% (ls_off% "sha2::sha256::compress256"))
      ((HkdfExt.compress256ExternShaSpec C.F extHookStack).inImage img)) :
    NewFromSliceOkExt' img C ext := by
  unfold NewFromSliceOkExt'
  rw [trExt_fnAddr_newFromSlice]
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, newFromSliceSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, hpre⟩
  dsimp only at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hsplit_stk : stackAt s0.sp newFromSliceStackExt =
      memRegion (nfsSp s0 - 16384#64) 16384 ∗ memRegion (s0.sp - 544#64) 544 := by
    have h1 := stackAt_split_bottom s0.sp 544 16384 (by decide)
    have hsub : s0.sp - BitVec.ofNat 64 (544 + 16384) = nfsSp s0 - 16384#64 := by
      change s0.sp - 16928#64 = (s0.sp - 544#64) - 16384#64
      bv_omega
    rw [hsub] at h1
    exact h1
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk16928 := IsBlock.memRegion (s0.sp - 16928#64) 16928
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hb_extstk := IsBlock.memRegion (nfsSp s0 - 16384#64) 16384
  have hsep_out16928 : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 16928#64) 16928 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStackExt, stackAt] at hsep
    ac_nf at hsep ⊢
  have hsep_split : s0.mem ⊨ memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗
      (memRegion (nfsSp s0 - 16384#64) 16384 ∗ memRegion (s0.sp - 544#64) 544) ∗ R := by
    rw [hsplit_stk] at hsep
    ac_nf at hsep ⊢
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion (nfsSp s0 - 16384#64) 16384 ∗ ((keyA ↦ₛ key) ∗ R))) := by
    ac_nf at hsep_split ⊢
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion (nfsSp s0 - 16384#64) 16384 ∗ (memRegion ret 0x98 ∗ R))) := by
    ac_nf at hsep_split ⊢
  have hsep_key_ext : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (nfsSp s0 - 16384#64) 16384 ∗
      (memRegion (s0.sp - 544#64) 544 ∗ (memRegion ret 0x98 ∗ R))) := by
    ac_nf at hsep_split ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion (nfsSp s0 - 16384#64) 16384 ∗ (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R)) := by
    ac_nf at hsep_split ⊢
  have hsep_extstk : s0.mem ⊨ memRegion (nfsSp s0 - 16384#64) 16384 ∗
      (memRegion (s0.sp - 544#64) 544 ∗ (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R)) := by
    ac_nf at hsep_split ⊢
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_key : s0.mem.RW keyA key.length := fun a ha => hb_key.permNoLazy_rw hsep_key ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hrw_extstk : s0.mem.RW (nfsSp s0 - 16384#64) 16384 :=
    fun a ha => hb_extstk.permNoLazy_rw hsep_extstk ha
  have hdisj_key_stk : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hdisj_key_extstk : key.length = 0 ∨ DisjointRegions keyA key.length (nfsSp s0 - 16384#64) 16384 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_extstk (by simp) (by decide) hsep_key_ext)
  have hrunsTo := HkdfExt.NfsExt.new_from_slice_runsToE_ext himg hMemcpy hComp
    hF hsym hpc hrun (by rw [hx2_nat]; exact hkey_len)
    (by rw [hx0]; exact hrw_out)
    (by rw [hx1, hx2_nat]; exact hrw_key)
    hrw_stk hrw_extstk
    (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
    (hb_stk.disjoint hb_extstk (by decide) (by decide) hsep_stk)
    (by rw [hx1, hx2_nat]; exact hdisj_key_stk)
    (by rw [hx1, hx2_nat]; exact hdisj_key_extstk)
    (by simpa [State.spAligned] using hsp)
  dsimp only at hrunsTo
  rw [hx1, hx2_nat, hkey_eq] at hrunsTo
  refine hrunsTo.to_reaches_pc fun sf hpost_sf _ _ htr => ?_
  rcases hpost_sf with ⟨hpc_sf, hstat_sf, hcc_sf, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, hcc_sf⟩
  rw [Spec.inImage, newFromSliceSpecExt]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := S2Frame.update_two_blocks hb_out
    (isBlock_nfsResult C.F ret key)
    hb_stk16928 hb_stk16928 hsep_out16928 hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStackExt, stackAt]
  ac_nf at hpost ⊢

theorem new_from_slice_ok_ext' (img : Obj.Image) (C : Crypto)
    (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hHkdf : HkdfContractsExt img C.F ext) :
    NewFromSliceOkExt' img C ext :=
  new_from_slice_ok_ext'_of_stubs himg hHkdf.memcpy hHkdf.compress256

/-- Bridge turning `NewFromSliceOkExt' img C ext` into a `RunsToE` transition on
`tripleRatchetProgAtExt img.base ext` for a `≤ 32`-byte key slice at `keyRegA`. -/
theorem nfs_runsTo_ext_x {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hNfs : NewFromSliceOkExt' img C ext)
    {s : State} {ret keyRegA keyA : BitVec 64} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyRegA)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 key.length)
    (hkey_len : key.length ≤ 32)
    (hkey_pts : (keyRegA ↦ₛ key) = (keyA ↦ₛ key))
    (hkey_mem : s.mem.readBytes keyA key.length = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 16928#64) 16928)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 16928#64) 16928)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 16928#64) 16928)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 16928#64, 16928)]) := by
  intro hL
  have hfn : (tripleRatchetProgAtExt img.base ext).fnAddr newFromSliceName =
      img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]") :=
    trExt_fnAddr_newFromSlice img.base ext
  let xg : NewFromSliceGhost := { ret := ret, keyA := keyRegA, key := key }
  let P1 : SepProp := memRegion ret 0x98
  let P2 : SepProp := (keyA ↦ₛ key)
  let P3 : SepProp := stackAt s.sp newFromSliceStackExt
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 : IsBlock P1 ret 0x98 (fun _ => True) := IsBlock.memRegion ret 0x98
  have hb2 : IsBlock P2 keyA key.length
      (fun m => key.length ≤ 2 ^ 64 ∧ m.readBytes keyA key.length = key) :=
    IsBlock.pointsToBytes keyA key
  have hb3 : IsBlock P3 (s.sp - 16928#64) 16928 (fun _ => True) :=
    IsBlock.memRegion (s.sp - 16928#64) 16928
  have hkey_le64 : key.length ≤ 64 := by omega
  have hkey_le264 : key.length ≤ 2 ^ 64 := by omega
  have hrw_key' : RW s.mem keyA key.length :=
    fun a ha => hrw_key a (by simp only [InRegion] at ha ⊢; omega)
  have hd_ret_key' : DisjointRegions ret 0x98 keyA key.length :=
    ⟨hd_ret_key.1, Nat.le_trans hkey_len hd_ret_key.2⟩
  have hd_key_stk' : DisjointRegions keyA key.length (s.sp - 16928#64) 16928 :=
    ⟨Nat.le_trans hkey_len hd_key_stk.1, hd_key_stk.2⟩
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks_nfs hb1 hb2 hb3 trivial ⟨hkey_le264, hkey_mem⟩ trivial
      hrw_ret hrw_key' hrw_stk hd_ret_key' hd_ret_stk hd_key_stk' hkey_le264 (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx2_nat : (s.readReg64 .x2).toNat = key.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpre_sat : s.mem ⊨ ((newFromSliceSpecExt C.F).inImage img).pre xg s ∗ R := by
    rw [Spec.inImage, newFromSliceSpecExt]
    dsimp only [xg]
    rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrz, hsym⟩, ⟨hx0, hx1, hx2_nat, hkey_le64⟩, ?_⟩
    simpa [P, P1, P2, P3, sepConj_assoc] using hsatPR
  have hsp_aligned : s.spAligned = true := by
    simpa [State.spAligned] using hsp_al
  have hcall := subroutine_ok_apply_full (oom := fun _ => False) hNfs xg R (hpc.trans hfn.symm) hstat hpre_sat hsp_aligned
    (by intro _ _ hp; dsimp only [Spec.inImage, newFromSliceSpecExt] at hp; rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [Spec.inImage, newFromSliceSpecExt] at he; rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [Spec.inImage, newFromSliceSpecExt] at ho; rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, hoom⟩⟩
  swap; · exact False.elim hoom
  rw [Spec.inImage, newFromSliceSpecExt] at hpost_sat
  dsimp only [xg] at hpost_sat
  rw [hkey_pts, sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  let P1' : SepProp := (ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key []
  have hb1' : IsBlock P1' ret 0x98
      (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) C.F key []) :=
    isBlock_nfsResult C.F ret key
  change s'.mem ⊨ ((ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key [] ∗ P2 ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by
    dsimp only [P1']; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by
    ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by
    ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by
    ac_nf at hpost_1 ⊢
  obtain ⟨hok, hhm⟩ := hb1'.read hpost_1
  have hkey_s' : s'.mem.readBytes keyA key.length = key := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'
    exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 16928#64, 16928)] :=
    isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP hpost_1 hpost_2 hpost_3
      hkey_le264 (hkey_s'.trans hkey_mem.symm) hmc.1 hmc.2.2
  exact ⟨s', hsteps, ⟨htr, hcc.2.2.2.2.2.2.2.2.2.2.2.2⟩, ⟨hpc', hstat', hcc, hok, hhm, hframe⟩,
    hsteps.codeLoaded hL⟩

/-- 32-byte key specialization of `nfs_runsTo_ext_x` for HKDF `extract`. -/
theorem nfs32_runsTo_ext_x {img : Obj.Image} {C : Crypto}
    {ext : String → Option (State → State)}
    (hNfs : NewFromSliceOkExt' img C ext)
    {s : State} {ret keyA : BitVec 64} {key : List (BitVec 8)}
    (hfrz : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hpc : s.pc = img.base + bv% (ls_off% "<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice [local#1]"))
    (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret)
    (hx1 : s.readReg64 .x1 = keyA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_len : key.length = 32)
    (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : RW s.mem ret 0x98)
    (hrw_key : RW s.mem keyA 32)
    (hrw_stk : RW s.mem (s.sp - 16928#64) 16928)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 16928#64) 16928)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 16928#64) 16928)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToE (tripleRatchetProgAtExt img.base ext) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧
      s'.status = .Running ∧
      CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧
      HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 16928#64, 16928)]) :=
  nfs_runsTo_ext_x hNfs hfrz hsym hpc hstat hx0 hx1 (by rw [hx2, hkey_len])
    (by omega) rfl (by rwa [hkey_len]) hrw_ret hrw_key hrw_stk hd_ret_key hd_ret_stk hd_key_stk hsp_al

end CryptoVerification.LibsignalTripleRatchet
