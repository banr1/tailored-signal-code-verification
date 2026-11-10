/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSegsExact

/-!
# `HookSat` Placed Contracts for `Hmac<Sha256>::new_from_slice [local#3]`

Relocatable `[LibsignalPlacement]` contracts for Block `402` (`new_from_slice [local#3]`) under
specification-backed `[HkdfPlacedHooksExactSat C.F H]` `memset`/`memcpy` contracts.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState chunks64 sha256IV sha256With)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement blkPC_402 blkPl_402 lsmpl
   lsProg_402)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (CalleeSaved Frame RW RunsTo agreesOutside_nfsPrologueMem agreesOutside_toFrame
   lsCompress256Sym lsMemcpySym lsMemsetSym nfsPrologueMem nfsSp sha256With_length)
open CryptoVerification.LibsignalTripleRatchet
  (HmacSt sessionMemsetRegionSpec)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt (AgreesOn AgreesOn.readBytes_eq)
open CryptoVerification.SpqrV1.Kdf
  (agreesOutside_pad_memset_lt64 effectiveHmacKey effectiveHmacKey_of_le innerPadBlock1
   readBytes_64_after_pad_memset_lt64)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3GenProof
  (NfsGt64Common StateG1 StateG2 StateG2a agreesOutside_nfsZeroMem agreesOutside_sub_176_288
   nfs3CodeFakeB nfs_chunks_1_to_4_of_G4_placed nfs_seg0_pro_gt64_placed
   nfs_seg0b1_gt64_placed nfs_seg0c_gt64_placed nfs_seg0d1_gt64_placed nfsZeroMem)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
  (NfsMemInv3 NfsRegInv3 nfs3PlacedFakeB nfs3PlacedFakeB_add_iv
   nfs_second_half_placed spqrSha256IVAddr)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
  (placed_memset_step_sat s2Frame_of_hmacFrame s2Frame_readBytes_eq_of_readable
   s2Frame_readable_of_readable)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSegsExact
  (new_from_slice3_placed_run_exact nfs_seg0a_gt64_placed_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 CallingConventionPreserved.x28 HkdfPlacedHooksExactSat)

/-! ## Fixed-Write Memory Idempotence & `nfsZeroMem` Ghost-State Bridge -/

private structure FixedWriteAt (sp : BitVec 64) (x : BitVec 64) (g : Memory → Memory) : Prop where
  idem : (∀ m, (g m).read8 x = m.read8 x) ∨ (∃ b, ∀ m, (g m).read8 x = b)
  perm_eq : ∀ m, (g m).perm = m.perm
  lf_out : OutsideRegion sp 544 x → ∀ m, (g m).isLazyFree x = m.isLazyFree x
  lf_false : ∀ m, m.isLazyFree x = false → (g m).isLazyFree x = false
  anon_eq : ∀ m, (g m).isAnon x = m.isAnon x

private theorem fixedWriteAt_id (sp x : BitVec 64) : FixedWriteAt sp x id :=
  ⟨Or.inl (fun _ => rfl), fun _ => rfl, fun _ _ => rfl, fun _ h => h, fun _ => rfl⟩

private theorem fixedWriteAt_write8 {sp x a : BitVec 64} {v : BitVec 8} {g : Memory → Memory}
    (hg : FixedWriteAt sp x g) (hin_a : InRegion sp 544 a) :
    FixedWriteAt sp x (fun m => (g m).write8 a v) := by
  have h_idem : (∀ m, ((g m).write8 a v).read8 x = m.read8 x) ∨
      (∃ b, ∀ m, ((g m).write8 a v).read8 x = b) := by
    by_cases hxa : x = a
    · subst hxa; exact Or.inr ⟨v, fun m => by simp⟩
    · rcases hg.idem with hid | ⟨b, hb⟩
      · exact Or.inl fun m => (Memory.read8_write8_ne hxa).trans (hid m)
      · exact Or.inr ⟨b, fun m => (Memory.read8_write8_ne hxa).trans (hb m)⟩
  refine ⟨h_idem,
    fun m => (Memory.perm_write8 (g m) a v).trans (hg.perm_eq m),
    fun hout m => ?_,
    fun m h => Memory.isLazyFree_write8_of_false a v (hg.lf_false m h),
    fun m => by rw [Memory.isAnon_write8_apply]; exact hg.anon_eq m⟩
  have hne : x ≠ a := by
    intro h; subst h
    dsimp only [InRegion, OutsideRegion] at hin_a hout
    omega
  exact (Memory.isLazyFree_write8_ne hne).trans (hg.lf_out hout m)

private theorem fixedWriteAt_write64 {sp x a : BitVec 64} {w : BitVec 64} {g : Memory → Memory}
    (hg : FixedWriteAt sp x g)
    (hoff : (a - sp).toNat + 8 ≤ 544) :
    FixedWriteAt sp x (fun m => (g m).write64 a w) := by
  unfold Memory.write64
  have hin (k : BitVec 64) (hk : k.toNat < 8) : InRegion sp 544 (a + k) := by
    dsimp only [InRegion]; bv_omega
  exact fixedWriteAt_write8 (fixedWriteAt_write8 (fixedWriteAt_write8 (fixedWriteAt_write8
    (fixedWriteAt_write8 (fixedWriteAt_write8 (fixedWriteAt_write8 (fixedWriteAt_write8 hg
      (hin 0#64 (by decide))) (hin 1#64 (by decide))) (hin 2#64 (by decide))) (hin 3#64 (by decide)))
      (hin 4#64 (by decide))) (hin 5#64 (by decide))) (hin 6#64 (by decide))) (hin 7#64 (by decide))

private theorem fixedWriteAt_writeBytes {sp x : BitVec 64} :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64) {g : Memory → Memory},
      FixedWriteAt sp x g →
      (a - sp).toNat + bs.length ≤ 544 →
      FixedWriteAt sp x (fun m => (g m).writeBytes a bs)
  | [], _, _, hg, _ => hg
  | b :: rest, a, g, hg, hoff => by
    simp only [Memory.writeBytes]
    have hin : InRegion sp 544 a := by
      simp only [List.length_cons] at hoff; dsimp only [InRegion]; omega
    have hoff' : ((a + 1#64) - sp).toNat + rest.length ≤ 544 := by
      simp only [List.length_cons] at hoff; bv_omega
    exact fixedWriteAt_writeBytes rest (a + 1#64) (fixedWriteAt_write8 hg hin) hoff'

private theorem fixedWriteAt_nfsZeroMem (s₀ : State) (x : BitVec 64) :
    FixedWriteAt (nfsSp s₀) x (fun m => nfsZeroMem (s₀.setMem m)) := by
  have hsub (off : BitVec 64) (sz : Nat) (h : off.toNat + sz ≤ 544) :
      ((nfsSp s₀ + off) - nfsSp s₀).toNat + sz ≤ 544 := by
    have heq : (nfsSp s₀ + off) - nfsSp s₀ = off := by bv_omega
    rwa [heq]
  have h0 : FixedWriteAt (nfsSp s₀) x (fun m => (s₀.setMem m).mem) := fixedWriteAt_id (nfsSp s₀) x
  have h1 := fixedWriteAt_write64 (a := nfsSp s₀ + 464#64) (w := s₀.readReg64 .x29) h0 (hsub 464#64 8 (by decide))
  have h2 := fixedWriteAt_write64 (a := nfsSp s₀ + 472#64) (w := s₀.readReg64 .lr) h1 (hsub 472#64 8 (by decide))
  have h3 := fixedWriteAt_write64 (a := nfsSp s₀ + 480#64) (w := s₀.readReg64 .x28) h2 (hsub 480#64 8 (by decide))
  have h4 := fixedWriteAt_write64 (a := nfsSp s₀ + 496#64) (w := s₀.readReg64 .x24) h3 (hsub 496#64 8 (by decide))
  have h5 := fixedWriteAt_write64 (a := nfsSp s₀ + 504#64) (w := s₀.readReg64 .x23) h4 (hsub 504#64 8 (by decide))
  have h6 := fixedWriteAt_write64 (a := nfsSp s₀ + 512#64) (w := s₀.readReg64 .x22) h5 (hsub 512#64 8 (by decide))
  have h7 := fixedWriteAt_write64 (a := nfsSp s₀ + 520#64) (w := s₀.readReg64 .x21) h6 (hsub 520#64 8 (by decide))
  have h8 := fixedWriteAt_write64 (a := nfsSp s₀ + 528#64) (w := s₀.readReg64 .x20) h7 (hsub 528#64 8 (by decide))
  have h9 := fixedWriteAt_write64 (a := nfsSp s₀ + 536#64) (w := s₀.readReg64 .x19) h8 (hsub 536#64 8 (by decide))
  exact fixedWriteAt_writeBytes (List.replicate 64 0#8) (nfsSp s₀ + 112#64) h9
    (by rw [List.length_replicate]; exact hsub 112#64 64 (by decide))

private theorem agreesOutside_nfsZeroMem_setMem {s₀ : State} {m' m_end : Memory}
    (hag_end : AgreesOutside (nfsZeroMem s₀) m_end (nfsSp s₀ + 176#64) 288)
    (hag_on : ∀ a, InRegion (nfsSp s₀) 544 a → m'.read8 a = m_end.read8 a)
    (hrw_m' : m'.RW (nfsSp s₀) 544) :
    AgreesOutside (nfsZeroMem (s₀.setMem m')) m' (nfsSp (s₀.setMem m') + 176#64) 288 := by
  have hsp_set : nfsSp (s₀.setMem m') = nfsSp s₀ := rfl
  rw [hsp_set]
  refine ⟨fun x hx => ?_, ((fixedWriteAt_nfsZeroMem s₀ 0#64).perm_eq m').symm,
    fun x _ => ?_,
    fun x hlf => ?_,
    fun x han => ((fixedWriteAt_nfsZeroMem s₀ x).anon_eq m').symm.trans han⟩
  · have hfw := fixedWriteAt_nfsZeroMem s₀ x
    by_cases hin : InRegion (nfsSp s₀) 544 x
    · have hm'_eq : m'.read8 x = (nfsZeroMem s₀).read8 x :=
        (hag_on x hin).trans (hag_end.1 x hx)
      rcases hfw.idem with hid | ⟨b, hb⟩
      · exact (hid m').symm
      · have hset_self : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
        have hb0 : (nfsZeroMem s₀).read8 x = b := hset_self ▸ hb s₀.mem
        rw [hb m', hm'_eq, hb0]
    · have hout : OutsideRegion (nfsSp s₀) 544 x := by
        dsimp only [InRegion, OutsideRegion] at hin ⊢; omega
      have hag_pro := agreesOutside_nfsPrologueMem (s₀.setMem m')
      have hag_z := agreesOutside_nfsZeroMem (s₀.setMem m')
      rw [hsp_set] at hag_pro hag_z
      have hout112 : OutsideRegion (nfsSp s₀ + 112#64) 64 x := by
        dsimp only [OutsideRegion] at hout ⊢; bv_omega
      have hout464 : OutsideRegion (nfsSp s₀ + 464#64) 80 x := by
        dsimp only [OutsideRegion] at hout ⊢; bv_omega
      exact ((hag_z.1 x hout112).trans (hag_pro.1 x hout464)).symm
  · by_cases hin : InRegion (nfsSp s₀) 544 x
    · have hlf_m' : m'.isLazyFree x = false :=
        (Memory.permNoLazy_eq_some_rw_iff.mp (hrw_m' x hin)).2
      have hlf_z : (nfsZeroMem (s₀.setMem m')).isLazyFree x = false :=
        (fixedWriteAt_nfsZeroMem s₀ x).lf_false m' hlf_m'
      rw [hlf_m', hlf_z]
    · have hout : OutsideRegion (nfsSp s₀) 544 x := by
        dsimp only [InRegion, OutsideRegion] at hin ⊢; omega
      exact ((fixedWriteAt_nfsZeroMem s₀ x).lf_out hout m').symm
  · by_cases hin : InRegion (nfsSp s₀) 544 x
    · exact (Memory.permNoLazy_eq_some_rw_iff.mp (hrw_m' x hin)).2
    · have hout : OutsideRegion (nfsSp s₀) 544 x := by
        dsimp only [InRegion, OutsideRegion] at hin ⊢; omega
      exact ((fixedWriteAt_nfsZeroMem s₀ x).lf_out hout m').symm.trans hlf

private theorem s2Frame_stack_of_g2a {s₀ s : State}
    (hag_zero : AgreesOutside (nfsZeroMem s₀) s.mem (nfsSp s₀ + 176#64) 288) :
    S2Frame s₀.mem s.mem [(s₀.sp - 544#64, 544)] := by
  have hf1 : Frame s₀.mem (nfsPrologueMem s₀) [(s₀.sp - 544#64, 544)] :=
    Frame.mono (agreesOutside_toFrame (agreesOutside_nfsPrologueMem s₀)) fun a ha r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have ha' := ha (s₀.sp - 544#64, 544) (by simp)
      dsimp only [nfsSp, OutsideRegion] at ha' ⊢; bv_omega
  have hf2 : Frame (nfsPrologueMem s₀) (nfsZeroMem s₀) [(s₀.sp - 544#64, 544)] :=
    Frame.mono (agreesOutside_toFrame (agreesOutside_nfsZeroMem s₀)) fun a ha r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have ha' := ha (s₀.sp - 544#64, 544) (by simp)
      dsimp only [nfsSp, OutsideRegion] at ha' ⊢; bv_omega
  have hf3 : Frame (nfsZeroMem s₀) s.mem [(s₀.sp - 544#64, 544)] :=
    Frame.mono (agreesOutside_toFrame hag_zero) fun a ha r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have ha' := ha (s₀.sp - 544#64, 544) (by simp)
      dsimp only [nfsSp, OutsideRegion] at ha' ⊢; bv_omega
  exact s2Frame_of_hmacFrame ((hf1.trans hf2).trans hf3)

/-! ## `HookSat` Sub-Segment `0b2` (`memset`) & Ghost-State Reset at `G2` -/

/-- Sub-segment `0b2` (`memset`) on the `> 64` path under `HookSat H lsMemsetSym sessionMemsetRegionSpec`, anchoring `StateG2` at `s₀.setMem s'.mem`. -/
public theorem nfs_seg0b2_gt64_placed_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2a nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB (lsmpl.ρ lsMemsetSym))
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (fun s' =>
      S2Frame s₀.mem s'.mem [(s₀.sp - 544#64, 544)] ∧
      StateG2 nfs3CodeFakeB F key (s₀.setMem s'.mem) s' nfs3PlacedFakeB) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hlr, hx20, hx21, hx23, hx24,
    ⟨m_copy, hmem_s, htail_copy, hst0_copy⟩⟩
  have hRW_s : s.mem.RW (nfsSp s₀) 544 := hcom.rw_stack hrw_stack
  rcases hcom with ⟨hstat, hsp, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27, hag_zero⟩
  set tail := key.drop (64 * (key.length / 64))
  have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
  rw [htail_len] at hx0 hx2 hx23 hx24 hmem_s htail_copy
  clear htail_len
  have htail_lt : tail.length < 64 := by simp [tail]; omega
  set m_pre_ms := m_copy.write8 (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 128#8
  set dst := nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64
  have hrw_pre_ms : m_pre_ms.RW dst (63 - tail.length) := by
    rw [← hmem_s]
    exact hRW_s.sub (by dsimp only [dst]; bv_omega)
  have hsp_al : (s.sp &&& 15#64) = 0#64 := by rw [hsp]; exact hal_nfs
  refine placed_memset_step_sat h_memset
    hstat hpc hx0 hx1 hx2 rfl hsp_al hmem_s hrw_pre_ms
    (fun s' htr' hpc' hstat' hcc _ _ _ hs2_ms hag_on => ?_) (htr_s := ⟨rfl, rfl⟩)
  refine RunsTo.refl ?_ htr'
  set m_end := m_pre_ms.writeBytes dst (List.replicate (63 - tail.length) 0#8)
  have hag_ms : AgreesOutside m_pre_ms m_end dst (63 - tail.length) := by
    have hlen : (List.replicate (63 - tail.length) 0#8).length = 63 - tail.length :=
      List.length_replicate
    rw [← hlen]
    exact ProofLib.agreesOutside_writeBytes m_pre_ms dst (List.replicate (63 - tail.length) 0#8)
  have hag_end : AgreesOutside (nfsZeroMem s₀) m_end (nfsSp s₀ + 176#64) 288 := by
    have h1 : AgreesOutside (nfsZeroMem s₀) m_pre_ms (nfsSp s₀ + 176#64) 288 := hmem_s ▸ hag_zero
    have h2 : AgreesOutside m_pre_ms m_end
        (nfsSp s₀ + (288#64 + BitVec.ofNat 64 tail.length + 1#64)) (63 - tail.length) := by
      simpa only [dst, BitVec.add_assoc] using hag_ms
    exact agreesOutside_sub_176_288 h1 h2 (by bv_omega)
  have hs2_pre : S2Frame s₀.mem m_pre_ms [(s₀.sp - 544#64, 544)] :=
    hmem_s ▸ s2Frame_stack_of_g2a hag_zero
  have hs2_s' : S2Frame s₀.mem s'.mem [(s₀.sp - 544#64, 544)] := by
    refine hs2_pre.trans (hs2_ms.mono fun a ha r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    have ha' := ha (s₀.sp - 544#64, 544) (by simp)
    dsimp only [dst, nfsSp, OutsideRegion] at ha' ⊢; bv_omega
  have hrw_s' : s'.mem.RW (nfsSp s₀) 544 := hs2_s'.rw_of_rw _ _ hrw_stack
  have hP_stk : ∀ a, InRegion (nfsSp s₀) 544 a →
      (m_pre_ms.perm a).r = true ∧ m_pre_ms.isLazyFree a = false := by
    intro a ha
    have hrw_a : m_pre_ms.permNoLazy a = some .rw := (hmem_s ▸ hRW_s) a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hrw_a
    exact ⟨by rw [hp]; rfl, hlf⟩
  have hag_stk : ∀ a, InRegion (nfsSp s₀) 544 a → s'.mem.read8 a = m_end.read8 a :=
    fun a ha => hag_on a (hP_stk a ha)
  have hbuf_s' : s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = innerPadBlock1 tail := by
    have h1 : s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = m_end.readBytes (nfsSp s₀ + 288#64) 64 :=
      AgreesOn.readBytes_eq hag_on (nfsSp s₀ + 288#64) 64 (by decide)
        (fun a ha => hP_stk a (by dsimp only [InRegion] at ha ⊢; bv_omega))
    rw [h1]
    exact readBytes_64_after_pad_memset_lt64 m_copy (nfsSp s₀ + 288#64) tail htail_copy htail_lt
  have hst0_s' : s'.mem.readBytes (nfsSp s₀ + 352#64) 32 =
      shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV) := by
    have h1 : s'.mem.readBytes (nfsSp s₀ + 352#64) 32 = m_end.readBytes (nfsSp s₀ + 352#64) 32 :=
      AgreesOn.readBytes_eq hag_on (nfsSp s₀ + 352#64) 32 (by decide)
        (fun a ha => hP_stk a (by dsimp only [InRegion] at ha ⊢; bv_omega))
    have hag_pad : AgreesOutside m_copy m_end (nfsSp s₀ + 288#64) 64 :=
      agreesOutside_pad_memset_lt64 m_copy (nfsSp s₀ + 288#64) tail htail_lt
    have hd : DisjointRegions (nfsSp s₀ + 288#64) 64 (nfsSp s₀ + 352#64) 32 := by
      clear * -; simp only [DisjointRegions]; bv_omega
    rw [h1, (agreesOutside_toFrame hag_pad).readBytes_eq (by simp [hd]) (by decide), hst0_copy]
  have htail_len' : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
  refine ⟨hs2_s',
    { pc_eq := hpc'.trans hlr
      common :=
        { status := hstat'
          sp_eq := hcc.1.trans hsp
          sp_align := hal_nfs
          x29_eq := (CallingConventionPreserved.x29 hcc).trans hx29
          x19_eq := (CallingConventionPreserved.x19 hcc).trans hx19
          x22_eq := (CallingConventionPreserved.x22 hcc).trans hx22
          x25_eq := (CallingConventionPreserved.x25 hcc).trans hx25
          x26_eq := (CallingConventionPreserved.x26 hcc).trans hx26
          x27_eq := (CallingConventionPreserved.x27 hcc).trans hx27
          agrees_zero := agreesOutside_nfsZeroMem_setMem hag_end hag_stk hrw_s' }
      x20_eq := (CallingConventionPreserved.x20 hcc).trans hx20
      x21_eq := (CallingConventionPreserved.x21 hcc).trans hx21
      x23_eq := (CallingConventionPreserved.x23 hcc).trans (htail_len' ▸ hx23)
      x24_eq := (CallingConventionPreserved.x24 hcc).trans (htail_len' ▸ hx24)
      buf_eq := hbuf_s'
      st0_bytes := hst0_s' }⟩

/-- Sub-segment `0b` (`+1260` setup + `memset`) on the `> 64` path under `HookSat`. -/
public theorem nfs_seg0b_gt64_placed_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG1 nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB)
    (hkey_gt : 64 < key.length)
    (hkey_lt : key.length < 2 ^ 63)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544) :
    RunsTo (lsProg_402 H) s (fun s' =>
      S2Frame s₀.mem s'.mem [(s₀.sp - 544#64, 544)] ∧
      StateG2 nfs3CodeFakeB F key (s₀.setMem s'.mem) s' nfs3PlacedFakeB) :=
  (nfs_seg0b1_gt64_placed hs hkey_gt hkey_lt hrw_stack).trans fun _ h2a =>
    nfs_seg0b2_gt64_placed_sat h_memset h2a hrw_stack

/-! ## Full `> 64` & Arbitrary-Length Block `402` Sibling Contracts -/

/-- Full `key.length > 64` execution of Block `402` (`new_from_slice [local#3]`) under `HookSat`. -/
public theorem new_from_slice3_gt64_placed_run_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat) (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F (sha256With F key) [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  have hk_le : (sha256With F key).length ≤ 64 := by
    have : (sha256With F key).length = 32 := sha256With_length F key
    omega
  have hiv' : s₀.mem.readBytes (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV := by
    rwa [nfs3PlacedFakeB_add_iv]
  have hread_iv' : s₀.mem.Readable (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    rwa [nfs3PlacedFakeB_add_iv]
  have hdisj_iv_stack' : DisjointRegions (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544 := by
    rwa [nfs3PlacedFakeB_add_iv]
  refine (nfs_seg0_pro_gt64_placed hpc hstat hgt hrw_stack hal).trans fun s_g0 hg0 => ?_
  refine (nfs_seg0a_gt64_placed_exact h_mc h_compress hg0 hgt hlt hiv' hread_iv' hdisj_iv_stack' hrw_stack hread_key hdisj_key_stack).trans fun s_g1 hg1 => ?_
  refine (nfs_seg0b_gt64_placed_sat h_memset hg1 hkey_gt hkey_lt hrw_stack).trans fun s_g2 ⟨hs2_g2, hg2⟩ => ?_
  set s₀' := s₀.setMem s_g2.mem
  have hrw_stack' : RW s₀'.mem (s₀'.sp - 544#64) 544 := hs2_g2.rw_of_rw _ _ hrw_stack
  have hrw_out' : RW s₀'.mem (s₀'.readReg64 .x0) 0x98 := hs2_g2.rw_of_rw _ _ hrw_out
  have hread_iv_g2 : s₀'.mem.Readable spqrSha256IVAddr 32 :=
    s2Frame_readable_of_readable hs2_g2 hread_iv
  have hiv_g2 : s₀'.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV :=
    (s2Frame_readBytes_eq_of_readable hs2_g2 hread_iv (by decide) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj_iv_stack.symm).trans hiv
  refine (nfs_seg0c_gt64_placed h_compress hg2 hkey_gt hkey_lt hrw_stack').trans fun s_g3 hg3 => ?_
  refine (nfs_seg0d1_gt64_placed hg3 hrw_stack').trans fun s_g4 hg4 => ?_
  refine (nfs_chunks_1_to_4_of_G4_placed hg4 hk_le hiv_g2 hread_iv_g2 hdisj_iv_stack hrw_out' hrw_stack' hdisj_out_stack hal).trans
    fun s1 ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩ => ?_
  refine (nfs_second_half_placed (s₀ := s₀') h_compress hk_le hal hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1).mono
    fun s' ⟨hpc', hstat', hcs', hm0', hhm', hfr'⟩ => ?_
  have hs2_pre2 : S2Frame s₀.mem s_g2.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)] :=
    hs2_g2.mono fun a ha _ hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ha _ (by simp)
  exact ⟨hpc', hstat', hcs', hm0', hhm', hs2_pre2.trans (s2Frame_of_hmacFrame hfr')⟩

/-- Arbitrary-length (`key.length < 2 ^ 63`) execution of Block `402` (`new_from_slice [local#3]`) under `HookSat`. -/
public theorem new_from_slice3_gen_placed_run_sat [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_memset : HookSat H lsMemsetSym sessionMemsetRegionSpec)
    (h_compress : H lsCompress256Sym = some (compress256Hook F)) {s₀ : State}
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98) (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F (effectiveHmacKey F key) [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  by_cases hle : (s₀.readReg64 .x2).toNat ≤ 64
  · have heff : effectiveHmacKey F key = key := effectiveHmacKey_of_le F (by omega)
    rw [heff]
    exact (new_from_slice3_placed_run_exact h_mc h_compress hpc hstat hle hiv hread_iv hdisj_iv_stack
      hrw_out hrw_stack hdisj_out_stack hread_key hdisj_key_stack hal).mono
      fun s' ⟨hpc', hstat', hcs', hm0', hhm', hfr'⟩ =>
        ⟨hpc', hstat', hcs', hm0', hhm', s2Frame_of_hmacFrame hfr'⟩
  · have hgt : 64 < (s₀.readReg64 .x2).toNat := by omega
    have hgt' : 64 < key.length := by omega
    have heff : effectiveHmacKey F key = sha256With F key := by
      unfold effectiveHmacKey
      simp [hgt']
    rw [heff]
    have hdisj_k : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544 :=
      hdisj_key_stack.resolve_left (by omega)
    exact new_from_slice3_gt64_placed_run_sat h_mc h_memset h_compress hpc hstat hgt hlt hiv hread_iv
      hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hread_key hdisj_k hal

/-- Generalized placed `RunsTo` contract for Block `402` under `[HkdfPlacedHooksExactSat C.F H]`. -/
public theorem new_from_slice3_gen_placed_runsTo_sat [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    [hH : HkdfPlacedHooksExactSat C.F H] {s₀ : State}
    (hpc : s₀.pc = lsmpl.base 402) (hstat : s₀.status = .Running)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    CryptoVerification.LibsignalTripleRatchet.RunsTo (lsProg_402 H) s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧
      CryptoVerification.LibsignalTripleRatchet.CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) C.F (effectiveHmacKey C.F key) [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  intro key hL
  obtain ⟨s', hs, htr, hvregs, hpost, hL'⟩ :=
    new_from_slice3_gen_placed_run_sat
      hH.memcpy hH.memset hH.compress256
      hpc hstat hlt hiv hread_iv hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hread_key hdisj_key_stack hal hL
  exact ⟨s', hs, ⟨htr, hvregs⟩, hpost, hL'⟩

/-- Cross-block `RunsTo` lift of `new_from_slice3_gen_placed_runsTo_sat` to any caller block `i < 619` under `[HkdfPlacedHooksExactSat C.F H]`. -/
public theorem new_from_slice3_gen_placed_runsTo_of_other_block_sat [LibsignalPlacement] (C : Crypto) (H : LibsignalHooks)
    [HkdfPlacedHooksExactSat C.F H] {callerProg : Program} {i : Nat} [hcaller : IsLsBlockProg callerProg i H]
    {s₀ : State} (hcl : LibsignalCodeLoaded lsmpl s₀.mem)
    (hpc : s₀.pc = lsmpl.base 402) (hstat : s₀.status = .Running)
    (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hi : i < 619 := by decide) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    CryptoVerification.LibsignalTripleRatchet.RunsTo callerProg s₀ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧
      CryptoVerification.LibsignalTripleRatchet.CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) C.F (effectiveHmacKey C.F key) [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) :=
  CryptoVerification.LibsignalTripleRatchet.RunsTo.of_other_block hcl
    (new_from_slice3_gen_placed_runsTo_sat C H hpc hstat hlt hiv hread_iv hdisj_iv_stack
      hrw_out hrw_stack hdisj_out_stack hread_key hdisj_key_stack hal)
    hi (by decide) (by decide)

end LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSat
