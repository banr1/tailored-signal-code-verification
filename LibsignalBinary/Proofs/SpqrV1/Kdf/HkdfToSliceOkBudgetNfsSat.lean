/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSegsExact

/-!
# Block `402` (`new_from_slice [local#3]`) `RunsToVm` Bridge (`HkdfToSliceOkBudgetNfsSat`)

Proves `nfs_le64_vm` and `nfs_gen_vm` on Block `402` lifted onto Block `379`'s program
under `[HkdfPlacedHooksExactSat C.F H]`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetNfsSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState chunks64 sha256IV sha256With)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   blkLib_eq_402 blkPC_379 blkPl_379 blkPl_402 libsignalSessionLib lsProg_402 lsmpl)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (agreesOutside_nfsPrologueMem agreesOutside_toFrame nfsPrologueMem nfsSp sha256With_length)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved Frame HmacSt RW RunsTo lsCompress256Sym lsMemcpySym lsMemsetSym)
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
  (nfs3PlacedFakeB nfs3PlacedFakeB_add_iv
   nfs_second_half_placed spqrSha256IVAddr)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.DefsSat
  (s2Frame_of_hmacFrame s2Frame_readBytes_eq_of_readable s2Frame_readable_of_readable)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat
  (RunsToVm blk402_noMsr blk402_noSvc0 hmacNoMemsetExcHooks hmacNoMemsetExcHooks_compress
   hmacNoMemsetExcHooks_memcpy lift_block_to_379_vm placed_memset_budget_optAlloc_steps_sat
   stripS_hmacSt stripS_mem stripS_read64 stripS_read8 stripS_readBytes)
open LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSegsExact
  (new_from_slice3_placed_run_exact nfs_seg0a_gt64_placed_exact)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24
   CallingConventionPreserved.x25 CallingConventionPreserved.x26
   HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

private theorem trRunsTo_of_hmac {prog : Program} {s : State} {P : State → Prop}
    (h : CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo prog s P) :
    RunsTo prog s P :=
  fun hL => let ⟨s', hs, htr, hv, hp, hL'⟩ := h hL; ⟨s', hs, ⟨htr, hv⟩, hp, hL'⟩

/-- `≤ 64`-byte Block `402` (`new_from_slice3`) lifted onto Block `379`'s `RunsToVm`. -/
theorem nfs_le64_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H] {s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_402).base) (hstat : s.status = .Running)
    (hlen : (s.readReg64 .x2).toNat ≤ 64)
    (hiv : s.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s.sp - 544#64) 544)
    (hrw_out : RW s.mem (s.readReg64 .x0) 0x98)
    (hrw_stack : RW s.mem (s.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s.readReg64 .x0) 0x98 (s.sp - 544#64) 544)
    (hread_key : s.mem.Readable (s.readReg64 .x1) (s.readReg64 .x2).toNat)
    (hdisj_key_stack : (s.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s.readReg64 .x1) (s.readReg64 .x2).toNat (s.sp - 544#64) 544)
    (hal : (s.sp &&& 0b1111#64) = 0#64) :
    let key := s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      s'.pc = s.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s s' ∧
      s'.mem.read64 (s.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s.readReg64 .x0 + 8#64) C.F key [] ∧
      Frame s.mem s'.mem [(s.readReg64 .x0, 0x98), (s.sp - 544#64, 544)] := by
  intro key
  have heq402 : ∀ X, lsProg_402 X = libsignalSessionLib.blockProgram lsmpl 402 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_402 X)
  let kp402 := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 402 H)
  have hr : ∀ r, (ProofLib.stripS kp402 s).readReg64 r = s.readReg64 r := fun _ => by cases s; rfl
  have hsp_s : (ProofLib.stripS kp402 s).sp = s.sp := by cases s; rfl
  have hP := heq402 H ▸ trRunsTo_of_hmac (new_from_slice3_placed_run_exact (F := C.F)
    hH.memcpy hH.compress256 hpc hstat hlen hiv hread_iv hdisj_iv_stack
    hrw_out hrw_stack hdisj_out_stack hread_key hdisj_key_stack hal)
  have hQ := heq402 (hmacNoMemsetExcHooks C.F H s.mem kp402) ▸
    trRunsTo_of_hmac (new_from_slice3_placed_run_exact (F := C.F)
    (s₀ := ProofLib.stripS kp402 s)
    (hmacNoMemsetExcHooks_memcpy hH.memcpy s.mem kp402)
    (hmacNoMemsetExcHooks_compress C.F H s.mem kp402)
    ((by cases s; rfl : (ProofLib.stripS kp402 s).pc = s.pc).trans hpc)
    ((by cases s; rfl : (ProofLib.stripS kp402 s).status = s.status).trans hstat)
    (by rw [hr]; exact hlen)
    (by rw [stripS_readBytes]; exact hiv)
    (by rw [stripS_mem]; exact stripExecOutside_readable kp402 s.mem _ _ hread_iv)
    (by rw [hsp_s]; exact hdisj_iv_stack)
    (by rw [stripS_mem, hr]; exact stripExecOutside_rw kp402 s.mem _ _ hrw_out)
    (by rw [stripS_mem, hsp_s]; exact stripExecOutside_rw kp402 s.mem _ _ hrw_stack)
    (by rw [hr, hsp_s]; exact hdisj_out_stack)
    (by rw [stripS_mem, hr .x1, hr .x2]; exact stripExecOutside_readable kp402 s.mem _ _ hread_key)
    (by rw [hr .x1, hr .x2, hsp_s]; exact hdisj_key_stack)
    (by rw [hsp_s]; exact hal))
  refine lift_block_to_379_vm (Pj := lsProg_402 H)
    blkLib_eq_402 blk402_noSvc0 blk402_noMsr (by decide) (by decide) hcl hP hQ
    (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
    fun sf hvm ⟨hpc', hst', hcs', htag', hhm', hfr'⟩ => ?_
  rw [hr .x0, stripS_read64] at htag'
  change HmacSt _ _ _ _ _ at hhm'
  rw [hr .x0, hr .x1, hr .x2, stripS_readBytes, stripS_hmacSt] at hhm'
  rw [stripS_mem, stripS_mem, hr .x0, hsp_s] at hfr'
  refine ⟨(by cases s; cases sf; exact hpc'), (by cases sf; exact hst'),
    ⟨(by cases s; cases sf; exact hcs'.1), fun r hrm => ?_⟩,
    htag', hhm', unstrip_frame hfr' hvm.perm_eq⟩
  have := hcs'.2 r hrm; cases s; cases sf; exact this

/-! ## `> 64`-Byte `nfsZeroMem` & `S2Frame` Helpers -/

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
    intro h; subst h; dsimp only [InRegion, OutsideRegion] at hin_a hout; omega
  exact (Memory.isLazyFree_write8_ne hne).trans (hg.lf_out hout m)

private theorem fixedWriteAt_write64 {sp x a : BitVec 64} {w : BitVec 64} {g : Memory → Memory}
    (hg : FixedWriteAt sp x g) (hoff : (a - sp).toNat + 8 ≤ 544) :
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
      FixedWriteAt sp x g → (a - sp).toNat + bs.length ≤ 544 →
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

private theorem nfsZeroMem_stripS_read8 (kp : BitVec 64 → Bool) (s₀ : State) (x : BitVec 64) :
    (nfsZeroMem (ProofLib.stripS kp s₀)).read8 x = (nfsZeroMem s₀).read8 x := by
  have heq1 : ProofLib.stripS kp s₀ = s₀.setMem (ProofLib.stripExecOutside kp s₀.mem) := by
    cases s₀; rfl
  have heq2 : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
  rcases (fixedWriteAt_nfsZeroMem s₀ x).idem with hid | ⟨b, hb⟩
  · rw [heq1, hid, ProofLib.strip_read8]
    have h0 := hid s₀.mem
    rw [heq2] at h0
    exact h0.symm
  · rw [heq1, hb]
    have h0 := hb s₀.mem
    rw [heq2] at h0
    exact h0.symm

private theorem agreesOutside_nfsZeroMem_of_read_out {s₀ : State} {m' : Memory}
    (hread_out : ∀ x, InRegion (nfsSp s₀) 544 x →
      OutsideRegion (nfsSp s₀ + 176#64) 288 x → m'.read8 x = (nfsZeroMem s₀).read8 x)
    (hrw_m' : m'.RW (nfsSp s₀) 544) :
    AgreesOutside (nfsZeroMem (s₀.setMem m')) m' (nfsSp (s₀.setMem m') + 176#64) 288 := by
  have hsp_set : nfsSp (s₀.setMem m') = nfsSp s₀ := rfl
  rw [hsp_set]
  refine ⟨fun x hx => ?_, ((fixedWriteAt_nfsZeroMem s₀ 0#64).perm_eq m').symm,
    fun x _ => ?_, fun x hlf => ?_,
    fun x han => ((fixedWriteAt_nfsZeroMem s₀ x).anon_eq m').symm.trans han⟩
  · have hfw := fixedWriteAt_nfsZeroMem s₀ x
    by_cases hin : InRegion (nfsSp s₀) 544 x
    · have hm'_eq := hread_out x hin hx
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

private theorem read8_writeBytes_congr {m₁ m₂ : Memory} (heq : ∀ a, m₁.read8 a = m₂.read8 a) :
    ∀ (bs : List (BitVec 8)) (dst a : BitVec 64),
      (m₁.writeBytes dst bs).read8 a = (m₂.writeBytes dst bs).read8 a
  | [], _, a => heq a
  | b :: rest, dst, a => by
    simp only [Memory.writeBytes]
    refine read8_writeBytes_congr (fun x => ?_) rest (dst + 1#64) a
    by_cases hxd : x = dst
    · subst hxd; simp
    · rw [Memory.read8_write8_ne hxd, Memory.read8_write8_ne hxd, heq x]

private theorem readBytes_of_read8_eq {m₁ m₂ : Memory} (heq : ∀ a, m₁.read8 a = m₂.read8 a) :
    ∀ (n : ℕ) (a : BitVec 64), m₁.readBytes a n = m₂.readBytes a n
  | 0, _ => rfl
  | n + 1, a => by
    simp only [Memory.readBytes, heq a, readBytes_of_read8_eq heq n (a + 1#64)]

private structure G2aUnstripped [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) (s₀ s : State) : Prop where
  pc_eq : s.pc = lsmpl.ρ lsMemsetSym
  status : s.status = .Running
  sp_eq : s.sp = nfsSp s₀
  sp_align : (nfsSp s₀ &&& 0b1111#64) = 0#64
  x29_eq : s.readReg64 .x29 = nfsSp s₀ + 464#64
  x19_eq : s.readReg64 .x19 = s₀.readReg64 .x0
  x22_eq : s.readReg64 .x22 = nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)
  x25_eq : s.readReg64 .x25 = s₀.readReg64 .x25
  x26_eq : s.readReg64 .x26 = s₀.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s₀.readReg64 .x27
  x0_eq : s.readReg64 .x0 =
    nfsSp s₀ + 288#64 + BitVec.ofNat 64 (key.length - 64 * (key.length / 64)) + 1#64
  x1_eq : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq : (s.readReg64 .x2).toNat = 63 - (key.length - 64 * (key.length / 64))
  lr_eq : s.readReg64 .lr = nfs3CodeFakeB + bv% (ls_off% CryptoVerification.SpqrV1.Kdf.newFromSlice3Name + 220)
  x20_eq : s.readReg64 .x20 = nfsSp s₀ + 352#64
  x21_eq : s.readReg64 .x21 = BitVec.ofNat 64 (key.length / 64)
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 (key.length - 64 * (key.length / 64))
  x24_eq : s.readReg64 .x24 = BitVec.ofNat 64 (63 - (key.length - 64 * (key.length / 64)))
  frame_stk : Frame s₀.mem s.mem [(s₀.sp - 544#64, 544)]
  read_out : ∀ x, OutsideRegion (nfsSp s₀ + 176#64) 288 x → s.mem.read8 x = (nfsZeroMem s₀).read8 x
  mem_copy : ∃ m_copy : Memory,
    (∀ a, s.mem.read8 a =
      (m_copy.write8 (nfsSp s₀ + 288#64 + BitVec.ofNat 64 (key.length - 64 * (key.length / 64))) 128#8).read8 a) ∧
    m_copy.readBytes (nfsSp s₀ + 288#64) (key.length - 64 * (key.length / 64)) =
      key.drop (64 * (key.length / 64)) ∧
    m_copy.readBytes (nfsSp s₀ + 352#64) 32 =
      shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl F sha256IV)

private theorem g2aUnstripped_of_stateG2a [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {key : List (BitVec 8)} {s₀ s : State}
    (hs : StateG2a nfs3CodeFakeB F key s₀ s nfs3PlacedFakeB (lsmpl.ρ lsMemsetSym)) :
    G2aUnstripped F key s₀ s := by
  rcases hs with ⟨hpc, ⟨hstat, hsp, hal, hx29, hx19, hx22, hx25, hx26, hx27, hag_z⟩,
    hx0, hx1, hx2, hlr, hx20, hx21, hx23, hx24, ⟨m_copy, hmem, ht, hst0⟩⟩
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
    Frame.mono (agreesOutside_toFrame hag_z) fun a ha r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have ha' := ha (s₀.sp - 544#64, 544) (by simp)
      dsimp only [nfsSp, OutsideRegion] at ha' ⊢; bv_omega
  exact ⟨hpc, hstat, hsp, hal, hx29, hx19, hx22, hx25, hx26, hx27,
    hx0, hx1, hx2, hlr, hx20, hx21, hx23, hx24, (hf1.trans hf2).trans hf3,
    fun x hx => hag_z.1 x hx, ⟨m_copy, fun a => by rw [hmem], ht, hst0⟩⟩

private theorem unstrip_g2a [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {key : List (BitVec 8)} {kp : BitVec 64 → Bool} {s₀ sf : State}
    (hvm : LibsignalBinary.Heap.VmPreserved s₀ sf)
    (h : G2aUnstripped F key (ProofLib.stripS kp s₀) (ProofLib.stripS kp sf)) :
    G2aUnstripped F key s₀ sf := by
  rcases h with ⟨hpc, hstat, hsp, hal, hx29, hx19, hx22, hx25, hx26, hx27,
    hx0, hx1, hx2, hlr, hx20, hx21, hx23, hx24, hfr, hrout, ⟨m_copy, hmc8, ht, hst0⟩⟩
  have hsp0 : nfsSp (ProofLib.stripS kp s₀) = nfsSp s₀ := by cases s₀; rfl
  have hsp_s0 : (ProofLib.stripS kp s₀).sp = s₀.sp := by cases s₀; rfl
  rw [hsp0] at hsp hal hx29 hx0 hx20 hrout hmc8 ht hst0
  rw [stripS_mem, stripS_mem, hsp_s0] at hfr
  refine ⟨(by cases sf; exact hpc), (by cases sf; exact hstat), (by cases sf; exact hsp), hal,
    (by cases sf; exact hx29), (by cases s₀; cases sf; exact hx19),
    (by cases sf; exact hx22), (by cases s₀; cases sf; exact hx25),
    (by cases s₀; cases sf; exact hx26), (by cases s₀; cases sf; exact hx27),
    (by cases sf; exact hx0), (by cases sf; exact hx1), (by cases sf; exact hx2),
    (by cases sf; exact hlr), (by cases sf; exact hx20), (by cases sf; exact hx21),
    (by cases sf; exact hx23), (by cases sf; exact hx24),
    unstrip_frame hfr hvm.perm_eq,
    fun x hx => ?_, ⟨m_copy, fun a => ?_, ht, hst0⟩⟩
  · have h1 := hrout x hx
    rwa [stripS_read8, nfsZeroMem_stripS_read8] at h1
  · have h1 := hmc8 a
    rwa [stripS_read8] at h1

private theorem nfs_rw_pad_dst {m : Memory} {sp : BitVec 64} {tlen : Nat}
    (h : m.RW sp 544) (ht : tlen < 64) :
    m.RW (sp + 288#64 + BitVec.ofNat 64 tlen + 1#64) (63 - tlen) :=
  h.sub (by bv_omega)

private theorem nfs_out_pad_dst_of_stack {sp0 a : BitVec 64} {tlen : Nat}
    (ht : tlen < 64) (ha : OutsideRegion (sp0 - 544#64) 544 a) :
    OutsideRegion (sp0 - 544#64 + 288#64 + BitVec.ofNat 64 tlen + 1#64) (63 - tlen) a := by
  dsimp only [OutsideRegion] at ha ⊢; bv_omega

private theorem nfs_in_288_sub_544 {sp a : BitVec 64}
    (ha : InRegion (sp + 288#64) 64 a) : InRegion sp 544 a := by
  dsimp only [InRegion] at ha ⊢; bv_omega

private theorem nfs_in_352_sub_544 {sp a : BitVec 64}
    (ha : InRegion (sp + 352#64) 32 a) : InRegion sp 544 a := by
  dsimp only [InRegion] at ha ⊢; bv_omega

private theorem nfs_disj_288_352 (sp : BitVec 64) :
    DisjointRegions (sp + 288#64) 64 (sp + 352#64) 32 := by
  simp only [DisjointRegions]; bv_omega

private theorem nfs_out_pad_dst_of_176 {sp x : BitVec 64} {tlen : Nat}
    (ht : tlen < 64) (hx : OutsideRegion (sp + 176#64) 288 x) :
    OutsideRegion (sp + 288#64 + BitVec.ofNat 64 tlen + 1#64) (63 - tlen) x := by
  dsimp only [OutsideRegion] at hx ⊢; bv_omega

private theorem stateG2_stripS [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {key : List (BitVec 8)} (kp : BitVec 64 → Bool) {s₀ s_g2 : State}
    (hrout_g2 : ∀ x, InRegion (nfsSp s₀) 544 x →
      OutsideRegion (nfsSp s₀ + 176#64) 288 x → s_g2.mem.read8 x = (nfsZeroMem s₀).read8 x)
    (hrw_stack' : RW s_g2.mem (s₀.sp - 544#64) 544)
    (hg2 : StateG2 nfs3CodeFakeB F key (s₀.setMem s_g2.mem) s_g2 nfs3PlacedFakeB) :
    StateG2 nfs3CodeFakeB F key
      (ProofLib.stripS kp (s₀.setMem s_g2.mem)) (ProofLib.stripS kp s_g2) nfs3PlacedFakeB := by
  let s₀' := s₀.setMem s_g2.mem
  have hnsp : nfsSp (ProofLib.stripS kp s₀') = nfsSp s₀ := by cases s₀; rfl
  have hnsp0 : nfsSp (ProofLib.stripS kp s₀) = nfsSp s₀ := by cases s₀; rfl
  have hset_eq : (ProofLib.stripS kp s₀).setMem (ProofLib.stripS kp s_g2).mem =
      ProofLib.stripS kp s₀' := by cases s₀; cases s_g2; rfl
  have hag_strip : AgreesOutside (nfsZeroMem (ProofLib.stripS kp s₀'))
      (ProofLib.stripS kp s_g2).mem (nfsSp (ProofLib.stripS kp s₀') + 176#64) 288 := by
    have hag0 := agreesOutside_nfsZeroMem_of_read_out
      (s₀ := ProofLib.stripS kp s₀) (m' := (ProofLib.stripS kp s_g2).mem)
      (fun x hin hout => by
        rw [hnsp0] at hin hout
        rw [stripS_read8, nfsZeroMem_stripS_read8]
        exact hrout_g2 x hin hout)
      (by rw [hnsp0, stripS_mem]; exact stripExecOutside_rw kp s_g2.mem _ _ hrw_stack')
    rwa [hset_eq] at hag0
  exact
    { pc_eq := by cases s_g2; exact hg2.pc_eq
      common :=
        { status := by cases s_g2; exact hg2.common.status
          sp_eq := by rw [hnsp]; cases s_g2; exact hg2.common.sp_eq
          sp_align := by rw [hnsp]; exact hg2.common.sp_align
          x29_eq := by rw [hnsp]; cases s_g2; exact hg2.common.x29_eq
          x19_eq := by cases s₀; cases s_g2; exact hg2.common.x19_eq
          x22_eq := by cases s_g2; exact hg2.common.x22_eq
          x25_eq := by cases s₀; cases s_g2; exact hg2.common.x25_eq
          x26_eq := by cases s₀; cases s_g2; exact hg2.common.x26_eq
          x27_eq := by cases s₀; cases s_g2; exact hg2.common.x27_eq
          agrees_zero := hag_strip }
      x20_eq := by rw [hnsp]; cases s_g2; exact hg2.x20_eq
      x21_eq := by cases s_g2; exact hg2.x21_eq
      x23_eq := by cases s_g2; exact hg2.x23_eq
      x24_eq := by cases s_g2; exact hg2.x24_eq
      buf_eq := by rw [hnsp, stripS_readBytes]; exact hg2.buf_eq
      st0_bytes := by rw [hnsp, stripS_readBytes]; exact hg2.st0_bytes }

private theorem nfs_gt64_chunkC [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H] {s₀ s_g2 : State} {key : List (BitVec 8)}
    (hcl_g2 : LibsignalCodeLoaded lsmpl s_g2.mem)
    (hkey_gt : 64 < key.length) (hkey_lt : key.length < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hs2_g2 : S2Frame s₀.mem s_g2.mem [(s₀.sp - 544#64, 544)])
    (hrout_g2 : ∀ x, InRegion (nfsSp s₀) 544 x →
      OutsideRegion (nfsSp s₀ + 176#64) 288 x → s_g2.mem.read8 x = (nfsZeroMem s₀).read8 x)
    (hg2 : StateG2 nfs3CodeFakeB C.F key (s₀.setMem s_g2.mem) s_g2 nfs3PlacedFakeB) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_g2 fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) C.F (sha256With C.F key) [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)] := by
  have hk_le : (sha256With C.F key).length ≤ 64 := by
    have : (sha256With C.F key).length = 32 := sha256With_length C.F key; omega
  have heq402 : ∀ X, lsProg_402 X = libsignalSessionLib.blockProgram lsmpl 402 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_402 X)
  let kp402 := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 402 H)
  have hc256Q := hmacNoMemsetExcHooks_compress C.F H s_g2.mem kp402
  let s₀' := s₀.setMem s_g2.mem
  have hrw_stack' : RW s₀'.mem (s₀'.sp - 544#64) 544 := hs2_g2.rw_of_rw _ _ hrw_stack
  have hrw_out' : RW s₀'.mem (s₀'.readReg64 .x0) 0x98 := hs2_g2.rw_of_rw _ _ hrw_out
  have hread_iv_g2 : s₀'.mem.Readable spqrSha256IVAddr 32 :=
    s2Frame_readable_of_readable hs2_g2 hread_iv
  have hiv_g2 : s₀'.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV :=
    (s2Frame_readBytes_eq_of_readable hs2_g2 hread_iv (by decide) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hdisj_iv_stack.symm).trans hiv
  have hg2_strip : StateG2 nfs3CodeFakeB C.F key
      (ProofLib.stripS kp402 s₀') (ProofLib.stripS kp402 s_g2) nfs3PlacedFakeB :=
    stateG2_stripS kp402 hrout_g2 hrw_stack' hg2
  have hP := heq402 H ▸ trRunsTo_of_hmac (
    (nfs_seg0c_gt64_placed hH.compress256 hg2 hkey_gt hkey_lt hrw_stack').trans fun _ hg3 =>
    (nfs_seg0d1_gt64_placed hg3 hrw_stack').trans fun _ hg4 =>
    (nfs_chunks_1_to_4_of_G4_placed hg4 hk_le hiv_g2 hread_iv_g2 hdisj_iv_stack
      hrw_out' hrw_stack' hdisj_out_stack hal).trans
      fun _ ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩ =>
    nfs_second_half_placed (s₀ := s₀') hH.compress256 hk_le hal
      hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1)
  have hr0' : ∀ r, (ProofLib.stripS kp402 s₀').readReg64 r = s₀.readReg64 r := fun _ => by cases s₀; rfl
  have hsp0' : (ProofLib.stripS kp402 s₀').sp = s₀.sp := by cases s₀; rfl
  have hm0' : (ProofLib.stripS kp402 s₀').mem = ProofLib.stripExecOutside kp402 s_g2.mem := by
    cases s₀; rfl
  have hQ := heq402 (hmacNoMemsetExcHooks C.F H s_g2.mem kp402) ▸ trRunsTo_of_hmac (
    (nfs_seg0c_gt64_placed hc256Q hg2_strip hkey_gt hkey_lt
      (by rw [hm0', hsp0']; exact stripExecOutside_rw kp402 s_g2.mem _ _ hrw_stack')).trans fun _ hg3 =>
    (nfs_seg0d1_gt64_placed hg3
      (by rw [hm0', hsp0']; exact stripExecOutside_rw kp402 s_g2.mem _ _ hrw_stack')).trans fun _ hg4 =>
    (nfs_chunks_1_to_4_of_G4_placed hg4 hk_le
      (by rw [hm0', stripExecOutside_readBytes]; exact hiv_g2)
      (by rw [hm0']; exact stripExecOutside_readable kp402 s_g2.mem _ _ hread_iv_g2)
      (by rw [hsp0']; exact hdisj_iv_stack)
      (by rw [hm0', hr0' .x0]; exact stripExecOutside_rw kp402 s_g2.mem _ _ hrw_out')
      (by rw [hm0', hsp0']; exact stripExecOutside_rw kp402 s_g2.mem _ _ hrw_stack')
      (by rw [hr0' .x0, hsp0']; exact hdisj_out_stack)
      (by rw [hsp0']; exact hal)).trans
      fun _ ⟨hpc1, hstat1, hR1, hM1, hx0_1, hx1_1, hx2_1, hist1, hblk1, hivsw1⟩ =>
    nfs_second_half_placed (s₀ := ProofLib.stripS kp402 s₀') hc256Q hk_le (by rw [hsp0']; exact hal)
      hpc1 hstat1 hR1 hM1 hx0_1 hx1_1 hx2_1 hist1 hblk1 hivsw1)
  refine (lift_block_to_379_vm (Pj := lsProg_402 H)
    blkLib_eq_402 blk402_noSvc0 blk402_noMsr (by decide) (by decide) hcl_g2 hP hQ
    (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
    fun sf hvm ⟨hpc', hst', hcs', htag', hhm', hfr'⟩ => ?_).mono
    fun sf ⟨hpc', hst', hcs', htag', hhm', hfr'⟩ => by
      have hs2_pre2 : S2Frame s₀.mem s_g2.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)] :=
        hs2_g2.mono fun a ha _ hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ha _ (by simp)
      exact ⟨hpc', hst',
        ⟨hcs'.1, fun r hrm => (hcs'.2 r hrm).trans (by cases s₀; rfl)⟩,
        htag', hhm', hs2_pre2.trans (s2Frame_of_hmacFrame hfr')⟩
  rw [hr0' .x0, stripS_read64] at htag'
  change HmacSt _ _ _ _ _ at hhm'
  rw [hr0' .x0, stripS_hmacSt] at hhm'
  rw [hm0', stripS_mem, hr0' .x0, hsp0'] at hfr'
  refine ⟨(by cases s₀; cases sf; exact hpc'), (by cases sf; exact hst'),
    ⟨(by cases s₀; cases sf; exact hcs'.1), fun r hrm => ?_⟩,
    htag', hhm', unstrip_frame hfr' hvm.perm_eq⟩
  have := hcs'.2 r hrm; cases s₀; cases sf; exact this

private theorem nfs_gt64_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec) {s₀ : State}
    (hcl : LibsignalCodeLoaded lsmpl s₀.mem)
    (hpc : s₀.pc = (blkPl_402).base) (hstat : s₀.status = .Running)
    (hgt : 64 < (s₀.readReg64 .x2).toNat) (hlt : (s₀.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) C.F (sha256With C.F key) [] ∧
      S2Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)] := by
  intro key
  have hkey_len : key.length = (s₀.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  have hkey_gt : 64 < key.length := by omega
  have hkey_lt : key.length < 2 ^ 63 := by omega
  have hk_le : (sha256With C.F key).length ≤ 64 := by
    have : (sha256With C.F key).length = 32 := sha256With_length C.F key; omega
  have heq402 : ∀ X, lsProg_402 X = libsignalSessionLib.blockProgram lsmpl 402 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := lsProg_402 X)
  let kp402 := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 402 H)
  have hmcQ := hmacNoMemsetExcHooks_memcpy (F := C.F) hH.memcpy s₀.mem kp402
  have hc256Q := hmacNoMemsetExcHooks_compress C.F H s₀.mem kp402
  have hr0 : ∀ r, (ProofLib.stripS kp402 s₀).readReg64 r = s₀.readReg64 r := fun _ => by cases s₀; rfl
  have hsp0 : (ProofLib.stripS kp402 s₀).sp = s₀.sp := by cases s₀; rfl
  have hkey_s : (ProofLib.stripS kp402 s₀).mem.readBytes
      ((ProofLib.stripS kp402 s₀).readReg64 .x1) ((ProofLib.stripS kp402 s₀).readReg64 .x2).toNat = key := by
    rw [hr0 .x1, hr0 .x2, stripS_readBytes]
  have hiv' : s₀.mem.readBytes (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 = shaStateBytes sha256IV := by
    rwa [nfs3PlacedFakeB_add_iv]
  have hread_iv' : s₀.mem.Readable (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    rwa [nfs3PlacedFakeB_add_iv]
  have hdisj_iv_stack' : DisjointRegions (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 (s₀.sp - 544#64) 544 := by
    rwa [nfs3PlacedFakeB_add_iv]
  -- Chunk A (`s₀ -> s_g2a` before `memset`)
  have hA : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ (G2aUnstripped C.F key s₀) := by
    have hP := heq402 H ▸ trRunsTo_of_hmac (
      (nfs_seg0_pro_gt64_placed (H := H) hpc hstat hgt hrw_stack hal).trans fun _ hg0 =>
      (nfs_seg0a_gt64_placed_exact hH.memcpy hH.compress256 hg0 hgt hlt hiv' hread_iv'
        hdisj_iv_stack' hrw_stack hread_key hdisj_key_stack).trans fun _ hg1 =>
      (nfs_seg0b1_gt64_placed hg1 hkey_gt hkey_lt hrw_stack).mono fun _ h2a =>
        g2aUnstripped_of_stateG2a h2a)
    have hQ := heq402 (hmacNoMemsetExcHooks C.F H s₀.mem kp402) ▸ trRunsTo_of_hmac (
      (nfs_seg0_pro_gt64_placed (H := hmacNoMemsetExcHooks C.F H s₀.mem kp402) (s₀ := ProofLib.stripS kp402 s₀)
        ((by cases s₀; rfl : (ProofLib.stripS kp402 s₀).pc = s₀.pc).trans hpc)
        ((by cases s₀; rfl : (ProofLib.stripS kp402 s₀).status = s₀.status).trans hstat)
        (by rw [hr0 .x2]; exact hgt)
        (by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp402 s₀.mem _ _ hrw_stack)
        (by rw [hsp0]; exact hal)).trans fun _ hg0 =>
      (nfs_seg0a_gt64_placed_exact hmcQ hc256Q hg0
        (by rw [hr0 .x2]; exact hgt) (by rw [hr0 .x2]; exact hlt)
        (by rw [stripS_readBytes]; exact hiv')
        (by rw [stripS_mem]; exact stripExecOutside_readable kp402 s₀.mem _ _ hread_iv')
        (by rw [hsp0]; exact hdisj_iv_stack')
        (by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp402 s₀.mem _ _ hrw_stack)
        (by rw [stripS_mem, hr0 .x1, hr0 .x2]; exact stripExecOutside_readable kp402 s₀.mem _ _ hread_key)
        (by rw [hr0 .x1, hr0 .x2, hsp0]; exact hdisj_key_stack)).trans fun _ hg1 =>
      (nfs_seg0b1_gt64_placed (key := key) (hkey_s ▸ hg1) hkey_gt hkey_lt
        (by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp402 s₀.mem _ _ hrw_stack)).mono
        fun _ h2a => g2aUnstripped_of_stateG2a h2a)
    exact lift_block_to_379_vm (Pj := lsProg_402 H)
      blkLib_eq_402 blk402_noSvc0 blk402_noMsr (by decide) (by decide) hcl hP hQ
      (fun _ hs => hs.status) (fun _ hs => hs.status)
      fun sf hvm hq => unstrip_g2a hvm hq
  -- Chunk B (`s_g2a -> s_g2` across `bl memset`)
  have hB : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ fun s_g2 =>
      S2Frame s₀.mem s_g2.mem [(s₀.sp - 544#64, 544)] ∧
      (∀ x, InRegion (nfsSp s₀) 544 x →
        OutsideRegion (nfsSp s₀ + 176#64) 288 x → s_g2.mem.read8 x = (nfsZeroMem s₀).read8 x) ∧
      StateG2 nfs3CodeFakeB C.F key (s₀.setMem s_g2.mem) s_g2 nfs3PlacedFakeB := by
    refine hA.trans_full fun s h2a _ hL379 => ?_
    rcases h2a with ⟨hpc_s, hstat_s, hsp_s, hal_nfs, hx29, hx19, hx22, hx25, hx26, hx27,
      hx0, hx1, hx2, hlr, hx20, hx21, hx23, hx24, hfr_stk, hrout, ⟨m_copy, hmc8, htail_copy, hst0_copy⟩⟩
    have hRW_s : s.mem.RW (nfsSp s₀) 544 := (hfr_stk.rw_iff _ _).mpr hrw_stack
    set tail := key.drop (64 * (key.length / 64))
    have htail_len : key.length - 64 * (key.length / 64) = tail.length := by simp [tail]
    rw [htail_len] at hx0 hx2 hx23 hx24 hmc8 htail_copy
    have htail_lt : tail.length < 64 := by simp [tail]; omega
    set dst := nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length + 1#64
    have hrw_dst : s.mem.RW dst (63 - tail.length) := nfs_rw_pad_dst hRW_s htail_lt
    have hsp_al_s : (s.sp &&& 15#64) = 0#64 := by rw [hsp_s]; exact hal_nfs
    obtain ⟨s', hsteps_ms, hvm_ms, hacp_ms, htr_ms, hv_ms, hpc', hstat', hcc,
      _, _, _, hs2_ms, hag_on⟩ :=
      placed_memset_budget_optAlloc_steps_sat
        (prog := (blkPC_379).rebase (blkPl_379).base H) (i := 379)
        hMemsetVm hstat_s hpc_s hx0 hx1 hx2 hlr hsp_al_s hrw_dst
    have hs2_s' : S2Frame s₀.mem s'.mem [(s₀.sp - 544#64, 544)] := by
      refine (s2Frame_of_hmacFrame hfr_stk).trans (hs2_ms.mono fun a ha r hr => ?_)
      simp only [List.mem_singleton] at hr; subst hr
      exact nfs_out_pad_dst_of_stack htail_lt (ha (s₀.sp - 544#64, 544) (by simp))
    have hrw_s' : s'.mem.RW (nfsSp s₀) 544 := hs2_s'.rw_of_rw _ _ hrw_stack
    have hP_stk : ∀ a, InRegion (nfsSp s₀) 544 a →
        (s.mem.perm a).r = true ∧ s.mem.isLazyFree a = false := fun a ha => by
      obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hRW_s a ha)
      exact ⟨by rw [hp]; rfl, hlf⟩
    set zeros := List.replicate (63 - tail.length) 0#8
    set m_pre := m_copy.write8 (nfsSp s₀ + 288#64 + BitVec.ofNat 64 tail.length) 128#8
    have hwb_eq : ∀ a, (s.mem.writeBytes dst zeros).read8 a = (m_pre.writeBytes dst zeros).read8 a :=
      read8_writeBytes_congr hmc8 zeros dst
    have hbuf_s' : s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = innerPadBlock1 tail := by
      rw [AgreesOn.readBytes_eq hag_on (nfsSp s₀ + 288#64) 64 (by decide)
            (fun a ha => hP_stk a (nfs_in_288_sub_544 ha)),
          readBytes_of_read8_eq hwb_eq 64 (nfsSp s₀ + 288#64)]
      exact readBytes_64_after_pad_memset_lt64 m_copy (nfsSp s₀ + 288#64) tail htail_copy htail_lt
    have hst0_s' : s'.mem.readBytes (nfsSp s₀ + 352#64) 32 =
        shaStateBytes ((chunks64 (key.take (64 * (key.length / 64)))).foldl C.F sha256IV) := by
      have hag_pad : AgreesOutside m_copy (m_pre.writeBytes dst zeros) (nfsSp s₀ + 288#64) 64 :=
        agreesOutside_pad_memset_lt64 m_copy (nfsSp s₀ + 288#64) tail htail_lt
      have hd : DisjointRegions (nfsSp s₀ + 288#64) 64 (nfsSp s₀ + 352#64) 32 :=
        nfs_disj_288_352 (nfsSp s₀)
      rw [AgreesOn.readBytes_eq hag_on (nfsSp s₀ + 352#64) 32 (by decide)
            (fun a ha => hP_stk a (nfs_in_352_sub_544 ha)),
          readBytes_of_read8_eq hwb_eq 32 (nfsSp s₀ + 352#64),
          (agreesOutside_toFrame hag_pad).readBytes_eq (by simp [hd]) (by decide), hst0_copy]
    have hrout_s' : ∀ x, InRegion (nfsSp s₀) 544 x →
        OutsideRegion (nfsSp s₀ + 176#64) 288 x → s'.mem.read8 x = (nfsZeroMem s₀).read8 x := by
      intro x hin hx
      have ⟨hpr, hlf⟩ := hP_stk x hin
      have hout_dst : OutsideRegion dst (63 - tail.length) x :=
        nfs_out_pad_dst_of_176 htail_lt hx
      exact (hs2_ms.1 x hpr hlf fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hout_dst).trans (hrout x hx)
    have htail_len' : tail.length = key.length - 64 * (key.length / 64) := by simp [tail]
    exact ⟨s', hsteps_ms, hvm_ms, hacp_ms, htr_ms, hv_ms,
      ⟨hs2_s', hrout_s',
        { pc_eq := hpc'
          common :=
            { status := hstat', sp_eq := hcc.1.trans hsp_s, sp_align := hal_nfs
              x29_eq := (CallingConventionPreserved.x29 hcc).trans hx29
              x19_eq := (CallingConventionPreserved.x19 hcc).trans hx19
              x22_eq := (CallingConventionPreserved.x22 hcc).trans hx22
              x25_eq := (CallingConventionPreserved.x25 hcc).trans hx25
              x26_eq := (CallingConventionPreserved.x26 hcc).trans hx26
              x27_eq := (CallingConventionPreserved.x27 hcc).trans hx27
              agrees_zero := agreesOutside_nfsZeroMem_of_read_out hrout_s' hrw_s' }
          x20_eq := (CallingConventionPreserved.x20 hcc).trans hx20
          x21_eq := (CallingConventionPreserved.x21 hcc).trans hx21
          x23_eq := (CallingConventionPreserved.x23 hcc).trans (htail_len' ▸ hx23)
          x24_eq := (CallingConventionPreserved.x24 hcc).trans (htail_len' ▸ hx24)
          buf_eq := hbuf_s', st0_bytes := hst0_s' }⟩,
      hsteps_ms.codeLoaded hL379⟩
  exact hB.trans_full fun s_g2 ⟨hs2_g2, hrout_g2, hg2⟩ hkf_g2 =>
    nfs_gt64_chunkC (hcl.of_keepsFrozen hkf_g2) hkey_gt hkey_lt hiv hread_iv
      hdisj_iv_stack hrw_out hrw_stack hdisj_out_stack hal hs2_g2 hrout_g2 hg2

/-- Arbitrary-length (`< 2 ^ 63`) Block `402` (`new_from_slice3`) lifted onto Block `379`'s
`RunsToVm` under `[HkdfPlacedHooksExactSat C.F H]`. -/
theorem nfs_gen_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec) {s : State}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_402).base) (hstat : s.status = .Running)
    (hlt : (s.readReg64 .x2).toNat < 2 ^ 63)
    (hiv : s.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s.mem.Readable spqrSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions spqrSha256IVAddr 32 (s.sp - 544#64) 544)
    (hrw_out : RW s.mem (s.readReg64 .x0) 0x98)
    (hrw_stack : RW s.mem (s.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s.readReg64 .x0) 0x98 (s.sp - 544#64) 544)
    (hread_key : s.mem.Readable (s.readReg64 .x1) (s.readReg64 .x2).toNat)
    (hdisj_key_stack : (s.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s.readReg64 .x1) (s.readReg64 .x2).toNat (s.sp - 544#64) 544)
    (hal : (s.sp &&& 0b1111#64) = 0#64) :
    let key := s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      s'.pc = s.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s s' ∧
      s'.mem.read64 (s.readReg64 .x0) = 0#64 ∧
      HmacSt s'.mem (s.readReg64 .x0 + 8#64) C.F (effectiveHmacKey C.F key) [] ∧
      S2Frame s.mem s'.mem [(s.readReg64 .x0, 0x98), (s.sp - 544#64, 544)] := by
  intro key
  have hkey_len : key.length = (s.readReg64 .x2).toNat := Memory.readBytes_length _ _ _
  by_cases hle : (s.readReg64 .x2).toNat ≤ 64
  · rw [effectiveHmacKey_of_le C.F (by omega)]
    exact (nfs_le64_vm (C := C) hcl hpc hstat hle hiv hread_iv hdisj_iv_stack
      hrw_out hrw_stack hdisj_out_stack hread_key hdisj_key_stack hal).mono
      fun s' ⟨hpc', hst', hcs', hm0', hhm', hfr'⟩ =>
        ⟨hpc', hst', hcs', hm0', hhm', s2Frame_of_hmacFrame hfr'⟩
  · have hgt : 64 < (s.readReg64 .x2).toNat := by omega
    have hgt' : 64 < key.length := by omega
    have heff : effectiveHmacKey C.F key = sha256With C.F key := by
      unfold effectiveHmacKey; simp [hgt']
    rw [heff]
    exact nfs_gt64_vm (C := C) hMemsetVm hcl hpc hstat hgt hlt hiv hread_iv hdisj_iv_stack
      hrw_out hrw_stack hdisj_out_stack hread_key (hdisj_key_stack.resolve_left (by omega)) hal

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetNfsSat
