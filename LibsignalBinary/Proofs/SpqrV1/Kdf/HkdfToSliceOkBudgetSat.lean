/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixed
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGen
import LibsignalBinary.Proofs.SpqrV1.Kdf.FrameROExt
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpand
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExact
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetFinSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetNfsSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceGen
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs

/-!
# `HookSat` Sibling of `SpqrV1.Kdf.HkdfToSliceOkBudget` (`HkdfToSliceOkBudgetSat`)

Budget-threaded multi-placed bridges for `spqr::kdf::hkdf_to_slice` (Block `379`) and
`spqr::kdf::hkdf_to_vec` (Block `378`) under `[HkdfPlacedHooksExactSat C.F H]` and
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat

open Arm64 ProofLib
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (ShaState hmacWith sha256IV)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkLib_eq_379 blkPC_378 blkPC_379 blkPl_378 blkPl_379 blkPl_402 blkPl_425 libsignalSessionLib lsmpl lsρ)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (disjointRegions_of_ro_rw length_hmacWith)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HmacSt RW RunsTo RunsTo.lsProg_svc
   TraceEq TraceEq.advancePC_step TraceEq.refl TraceEq.setMem_step TraceEq.setPC_step
   TraceEq.setPState_step TraceEq.writeReg32_step TraceEq.writeReg64_step TraceEq.writeVReg128_step
   extHookStack extract_withLsCodeRoLoaded hmacInnerInit
   hmacOuterInit keys_ls_subroutine_ok_of_block_cro lsCompress256Sym lsMemcpySym lsMemsetSym
   noAllocShimSpec ro_outside_rw_shared_lb shaStateBytes_length withLsCodeRoLoaded
   zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (agreesOutside_writeBytes_le and64_255_ofNat64 and_0xffffffffff_ofNat64 cmp32_lt63_lemmas
   cmp_lt64_lemmas hkdfExpand_64_eq mem_setMem t1_length t2_length t3_length
   writeBytes_readBytes_disj zeroExtend32_ofNat8_eq_truncate32 zeroExtend64_add1_truncate32_ofNat64
   zeroExtend64_and255_truncate32_ofNat64 zeroExtend64_ofNat8)
open CryptoVerification.LibsignalTripleRatchet.Extract (S2Frame)
open CryptoVerification.SpqrV1.Alloc (spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Kdf (FinPre3PfxGen HmacStN effectiveHmacKey effectiveHmacKey_length_le
  fin3PlacedFakeB fin3PlacedFakeB_off_0 hmacWith_effectiveHmacKey spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HExpCommon HFrame HmacStN.of_copy_352_32 HmacStN.of_tail_counter_352 HPost HPre HSaved
   StateB1Done StateB1Fin StateB1RetFin StateDone StateEFin StateENfs1 StateENfs2 StateERet1
   StateERet2 StateERetFin StateLoop StateLoopA1 StateLoopA2 StateLoopC StateLoopFin
   agreesOutside_hsp_write64 b1_done_32_placed_runsTo b1_to_loop_placed_runsTo bv_sub_add_lit_ge
   canWrite_hsp_352_add epilogue_placed_runsTo hkdfCodeFakeB hkdfExpand_32_eq hkdfExpand_96_eq hsp
   hsp_aligned info_sub32_lemmas iter_a1_placed_runsTo iter_counter_lemmas okmLen_lt_8161_lemmas
   readBytes_32_hsp_508_of_540 rodata_sha256IV_placed s2_compress256_step_placed_429
   seg_b1a_placed_runsTo seg_e0_placed_runsTo seg_e1d_placed_runsTo seg_e2_placed_runsTo seg_e3_placed_runsTo)
open scoped CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof (nfs3PlacedFakeB nfs3PlacedFakeB_add_iv spqrSha256IVAddr)
open CryptoVerification.SpqrV1.Kdf.SpqrKdfExt (disjointRegions_of_outside)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open scoped LibsignalBinary.Heap.MuslMemOpsRunsToPlaced
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux (stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExact (seg_b1b_placed_runsTo_exact seg_b1d_placed_runsTo_exact)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact
  (inRegion_sub_slice readable_of_rw s2_memcpy_step_placed_429_exact seg_e1_placed_runsTo_exact)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetFinSat (finalize_fixed3_pfx_lt64_kdf_vm_sat)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetNfsSat (nfs_gen_vm nfs_le64_vm)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetVmSat
  (RunsToVm blk379_noMsr blk379_noSvc0 hmacNoMemsetExcHooks hmacNoMemsetExcHooks_compress
   hmacNoMemsetExcHooks_memcpy lift_block_to_379_vm stripS_hcommon_refl stripS_hexpCommon_refl
   stripS_hmacSt stripS_hmacStN stripS_mem stripS_read64 stripS_readBytes unstrip_hcommon unstrip_hexpCommon)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (hkdfToVecSpec hkdf_to_vec_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes
attribute [local simp, local arm64_norm] bv_sub_add_lit hkdfCodeFakeB bv_sub_add_lit_ge

@[local simp, local arm64_norm]
private theorem lsmpl_base_475 [LibsignalPlacement] : lsmpl.base 425 = (blkPl_425).base := rfl

/-! ## 4. Block `379` / `402` Assembly & Separation-Logic Bridges -/

@[local simp]
private theorem hsp_setMem (s₀ : State) (m : Memory) : hsp (s₀.setMem m) = hsp s₀ := rfl

abbrev HFrameS2 (okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  S2Frame s₀.mem m [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 544#64, 1232)]

structure HPreBase [LibsignalPlacement] (salt ikm info : List (BitVec 8))
    (saltA ikmA infoA okmA : BitVec 64) (okmLen : ℕ) (s₀ : State) : Prop where
  pre       : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ nfs3PlacedFakeB True
  read_salt : s₀.mem.Readable saltA salt.length
  read_ikm  : s₀.mem.Readable ikmA ikm.length
  read_info : s₀.mem.Readable infoA info.length

private theorem s2_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {p : BitVec 64} {n : ℕ} (hrd : m₁.Readable p n) : m₂.Readable p n :=
  fun a ha => let ⟨hr, hlf⟩ := hrd a ha; hf.2.2 a hr hlf

private theorem s2_readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {p : BitVec 64} {n : ℕ} (hn : n ≤ 2 ^ 64) (hrd : m₁.Readable p n)
    (hout : ∀ a, InRegion p n a → ∀ r ∈ regs, OutsideRegion r.1 r.2 a) :
    m₂.readBytes p n = m₁.readBytes p n :=
  Memory.readBytes_congr_region hn fun a ha => let ⟨hr, hlf⟩ := hrd a ha; hf.1 a hr hlf (hout a ha)

private theorem HPreBase.at_mem [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (m : Memory) (hf : HFrameS2 okmLen s₀ m) :
    HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen (s₀.setMem m) nfs3PlacedFakeB True := by
  have hout_pair {p : BitVec 64} {n : ℕ} (ho_okm : ∀ a, InRegion p n a → OutsideRegion okmA okmLen a)
      (ho_stk : ∀ a, InRegion p n a → OutsideRegion (hsp s₀ - 544#64) 1232 a) :
      ∀ a, InRegion p n a → ∀ r ∈ [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 544#64, 1232)], OutsideRegion r.1 r.2 a := by
    intro a ha r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl; · rw [hb.pre.x6_eq]; exact ho_okm a ha
    · exact ho_stk a ha
  have hiv_read_iv : s₀.mem.Readable spqrSha256IVAddr 32 := by have h := hb.pre.ro_iv_read; rwa [nfs3PlacedFakeB_add_iv] at h
  have hiv_bytes_iv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV := by
    have h := hb.pre.ro_iv_bytes; rwa [nfs3PlacedFakeB_add_iv] at h
  have hd_iv_okm : DisjointRegions spqrSha256IVAddr 32 okmA okmLen := by have h := hb.pre.disj_iv_okm; rwa [nfs3PlacedFakeB_add_iv] at h
  have hd_iv_stk : DisjointRegions spqrSha256IVAddr 32 (hsp s₀ - 544#64) 1232 := by
    have h := hb.pre.disj_iv_stk; rwa [nfs3PlacedFakeB_add_iv] at h
  exact {
    pc_eq := hb.pre.pc_eq, status := hb.pre.status, x0_eq := hb.pre.x0_eq, x1_eq := hb.pre.x1_eq,
    x2_eq := hb.pre.x2_eq, x3_eq := hb.pre.x3_eq, x4_eq := hb.pre.x4_eq, x5_eq := hb.pre.x5_eq,
    x6_eq := hb.pre.x6_eq, x7_eq := hb.pre.x7_eq, salt_lt := hb.pre.salt_lt, ikm_len := hb.pre.ikm_len,
    info_ge := hb.pre.info_ge, info_lt := hb.pre.info_lt, okm_len := hb.pre.okm_len, base_al := trivial,
    ro_iv_bytes := by
      rw [nfs3PlacedFakeB_add_iv]
      exact (s2_readBytes_eq_of_readable hf (by decide) hiv_read_iv
        (hout_pair (fun a ha => hd_iv_okm.symm.outside ha (by decide))
          (fun a ha => hd_iv_stk.symm.outside ha (by decide)))).trans hiv_bytes_iv,
    ro_iv_read := fun a ha => let ⟨hr, hlf⟩ := hb.pre.ro_iv_read a ha; hf.2.2 a hr hlf,
    disj_iv_stk := hb.pre.disj_iv_stk, disj_iv_okm := hb.pre.disj_iv_okm,
    salt_bytes := (s2_readBytes_eq_of_readable hf (by have := hb.pre.salt_lt; omega) hb.read_salt (hout_pair hb.pre.out_salt_okm hb.pre.out_salt_stk)).trans hb.pre.salt_bytes,
    ikm_bytes := (s2_readBytes_eq_of_readable hf (by have := hb.pre.ikm_len; omega) hb.read_ikm (hout_pair hb.pre.out_ikm_okm hb.pre.out_ikm_stk)).trans hb.pre.ikm_bytes,
    info_bytes := (s2_readBytes_eq_of_readable hf (by have := hb.pre.info_lt; omega) hb.read_info (hout_pair hb.pre.out_info_okm hb.pre.out_info_stk)).trans hb.pre.info_bytes,
    rw_okm := hf.rw_of_rw okmA okmLen hb.pre.rw_okm, rw_stack := hf.rw_of_rw (hsp s₀ - 544#64) 1232 hb.pre.rw_stack,
    disj_okm_stk := hb.pre.disj_okm_stk, disj_salt_stk := hb.pre.disj_salt_stk,
    out_salt_stk := hb.pre.out_salt_stk, out_salt_okm := hb.pre.out_salt_okm,
    out_ikm_stk := hb.pre.out_ikm_stk, out_ikm_okm := hb.pre.out_ikm_okm,
    out_info_stk := hb.pre.out_info_stk, out_info_okm := hb.pre.out_info_okm, sp_aligned := hb.pre.sp_aligned }

private theorem hpre_stripS [LibsignalPlacement] (kp : BitVec 64 → Bool)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s0 : State}
    (hp : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s0 nfs3PlacedFakeB True) :
    HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen (ProofLib.stripS kp s0) nfs3PlacedFakeB True := by
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp0 : hsp (ProofLib.stripS kp s0) = hsp s0 := by cases s0; rfl
  have hsp_eq : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  exact {
    pc_eq := (by cases s0; rfl : (ProofLib.stripS kp s0).pc = s0.pc).trans hp.pc_eq,
    status := (by cases s0; rfl : (ProofLib.stripS kp s0).status = s0.status).trans hp.status,
    x0_eq := (hr .x0).trans hp.x0_eq, x1_eq := (hr .x1).trans hp.x1_eq, x2_eq := (hr .x2).trans hp.x2_eq,
    x3_eq := (hr .x3).trans hp.x3_eq, x4_eq := (hr .x4).trans hp.x4_eq, x5_eq := (hr .x5).trans hp.x5_eq,
    x6_eq := (hr .x6).trans hp.x6_eq, x7_eq := (hr .x7).trans hp.x7_eq, salt_lt := hp.salt_lt,
    ikm_len := hp.ikm_len, info_ge := hp.info_ge, info_lt := hp.info_lt, okm_len := hp.okm_len, base_al := trivial,
    ro_iv_bytes := by rw [stripS_readBytes]; exact hp.ro_iv_bytes,
    ro_iv_read := by rw [stripS_mem]; exact stripExecOutside_readable kp s0.mem _ _ hp.ro_iv_read,
    disj_iv_stk := by rw [hsp0]; exact hp.disj_iv_stk, disj_iv_okm := hp.disj_iv_okm,
    salt_bytes := by rw [stripS_readBytes]; exact hp.salt_bytes,
    ikm_bytes := by rw [stripS_readBytes]; exact hp.ikm_bytes,
    info_bytes := by rw [stripS_readBytes]; exact hp.info_bytes,
    rw_okm := by rw [stripS_mem]; exact stripExecOutside_rw kp s0.mem _ _ hp.rw_okm,
    rw_stack := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp s0.mem _ _ hp.rw_stack,
    disj_okm_stk := by rw [hsp0]; exact hp.disj_okm_stk, disj_salt_stk := by rw [hsp0]; exact hp.disj_salt_stk,
    out_salt_stk := by rw [hsp0]; exact hp.out_salt_stk, out_salt_okm := hp.out_salt_okm,
    out_ikm_stk := by rw [hsp0]; exact hp.out_ikm_stk, out_ikm_okm := hp.out_ikm_okm,
    out_info_stk := by rw [hsp0]; exact hp.out_info_stk, out_info_okm := hp.out_info_okm,
    sp_aligned := by rw [hsp_eq]; exact hp.sp_aligned }

private theorem hframeS2_step {okmLen : ℕ} {s₀ : State} {m_ref m : Memory}
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hfr : HFrame okmLen (s₀.setMem m_ref) m) : HFrameS2 okmLen s₀ m :=
  hf_ref.trans (S2Frame.of_frame hfr)

private theorem hcommon_reset_of_fin [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA outOff : BitVec 64} {okmLen : ℕ} {s₀ s s' : State} {m_ref : Memory}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hc : HCommon okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running) (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + outOff, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)])
    (hout : decide (outOff.toNat + 32 ≤ 592) = true) :
    HFrameS2 okmLen s₀ s'.mem ∧ HCommon okmLen (s₀.setMem s'.mem) s' := by
  have hout' : outOff.toNat + 32 ≤ 592 := of_decide_eq_true hout
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.frame
  have hd_saved : ∀ r ∈ [(hsp s₀ + outOff, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64), decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true →
      s'.mem.read64 (hsp s₀ + off) = s.mem.read64 (hsp s₀ + off) := fun off hoff => by
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    exact hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_saved r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨(hframeS2_step hf_ref hc.frame).trans (hfr.mono fun a ha r hr => ?_),
    ⟨hstat', hcs.sp_eq.trans hc.sp_eq, (CalleeSaved.x29 hcs).trans hc.x29_eq,
      { m592 := (h_saved_eq 592#64 (by decide)).trans h0, m600 := (h_saved_eq 600#64 (by decide)).trans h1,
        m608 := (h_saved_eq 608#64 (by decide)).trans h2, m616 := (h_saved_eq 616#64 (by decide)).trans h3,
        m624 := (h_saved_eq 624#64 (by decide)).trans h4, m632 := (h_saved_eq 632#64 (by decide)).trans h5,
        m640 := (h_saved_eq 640#64 (by decide)).trans h6, m648 := (h_saved_eq 648#64 (by decide)).trans h7,
        m656 := (h_saved_eq 656#64 (by decide)).trans h8, m664 := (h_saved_eq 664#64 (by decide)).trans h9,
        m672 := (h_saved_eq 672#64 (by decide)).trans h10, m680 := (h_saved_eq 680#64 (by decide)).trans h11 },
      Frame.refl s'.mem _⟩⟩
  have hstack := ha (hsp s₀ - 544#64, 1232) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)

private theorem hexpCommon_reset_of_fin [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {prk salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {m_ref : Memory} (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hc : HExpCommon F prk info infoA okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running) (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + 540#64, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)]) :
    HFrameS2 okmLen s₀ s'.mem ∧ HExpCommon F prk info infoA okmLen (s₀.setMem s'.mem) s' := by
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.common.frame
  have hd_low : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀) 32 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have hd_208 : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀ + 208#64) 0x90 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  rcases hc.hmac_208 with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  have hhm' : HmacSt s'.mem (hsp s₀ + 208#64) F prk [] := by
    refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp ((hrw_hsp.sub (by bv_omega) : s.mem.RW (hsp s₀ + 208#64 + 63#64) 1) (hsp s₀ + 208#64 + 63#64) (by simp [InRegion]))
      exact (hfr.1 (hsp s₀ + 208#64 + 63#64) (by rw [hp]; rfl) hlf fun r hr => (hd_208 r hr).outside (by unfold InRegion; bv_omega) (by decide)).trans hpos
    · exact (hfr.readBytes_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩) (by decide)).trans hin
    · exact (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hcnt1
    · exact (hfr.readBytes_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩) (by decide)).trans hout
    · exact (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩)).trans hcnt2
  obtain ⟨hf_s', hc'⟩ := hcommon_reset_of_fin (outOff := 540#64) hb hf_ref hc.common hstat' hcs hfr (by decide)
  exact ⟨hf_s', {
    common := hc',
    m0_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_low r hr).sub_right (hsp s₀ + 0#64) ⟨by decide, by bv_omega⟩).trans hc.m0_eq,
    m8_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_low r hr).sub_right (hsp s₀ + 8#64) ⟨by decide, by bv_omega⟩).trans hc.m8_eq,
    m16_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_low r hr).sub_right (hsp s₀ + 16#64) ⟨by decide, by bv_omega⟩).trans hc.m16_eq,
    m24_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_low r hr).sub_right (hsp s₀ + 24#64) ⟨by decide, by bv_omega⟩).trans hc.m24_eq,
    hmac_208 := hhm' }⟩

private theorem hcommon_reset_of_nfs [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA retOff : BitVec 64} {okmLen : ℕ} {s₀ s s' : State} {m_ref : Memory}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hc : HCommon okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running) (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + retOff, 0x98), (hsp s₀ - 544#64, 544)])
    (hret : decide (retOff.toNat + 0x98 ≤ 592) = true) :
    HFrameS2 okmLen s₀ s'.mem ∧ HCommon okmLen (s₀.setMem s'.mem) s' := by
  have hret' : retOff.toNat + 0x98 ≤ 592 := of_decide_eq_true hret
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.frame
  have hd_saved : ∀ r ∈ [(hsp s₀ + retOff, (0x98 : ℕ)), (hsp s₀ - 544#64, 544)],
      DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64), decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true →
      s'.mem.read64 (hsp s₀ + off) = s.mem.read64 (hsp s₀ + off) := fun off hoff => by
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    exact hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => (hd_saved r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨(hframeS2_step hf_ref hc.frame).trans (hfr.mono fun a ha r hr => ?_),
    ⟨hstat', hcs.sp_eq.trans hc.sp_eq, (CalleeSaved.x29 hcs).trans hc.x29_eq,
      { m592 := (h_saved_eq 592#64 (by decide)).trans h0, m600 := (h_saved_eq 600#64 (by decide)).trans h1,
        m608 := (h_saved_eq 608#64 (by decide)).trans h2, m616 := (h_saved_eq 616#64 (by decide)).trans h3,
        m624 := (h_saved_eq 624#64 (by decide)).trans h4, m632 := (h_saved_eq 632#64 (by decide)).trans h5,
        m640 := (h_saved_eq 640#64 (by decide)).trans h6, m648 := (h_saved_eq 648#64 (by decide)).trans h7,
        m656 := (h_saved_eq 656#64 (by decide)).trans h8, m664 := (h_saved_eq 664#64 (by decide)).trans h9,
        m672 := (h_saved_eq 672#64 (by decide)).trans h10, m680 := (h_saved_eq 680#64 (by decide)).trans h11 },
      Frame.refl s'.mem _⟩⟩
  have hstack := ha (hsp s₀ - 544#64, 1232) (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)

private theorem fin_extract_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H] (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      HFrameS2 okmLen s₀ s'.mem ∧ StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s'.mem) s' := by
  rcases hx.hmac_32 with ⟨pfx, tail, hpt, _hmod, hlt, hhm⟩
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hfin_pre : FinPre3PfxGen fin3PlacedFakeB C.F (effectiveHmacKey C.F salt) pfx tail s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.common.status,
      key_le := effectiveHmacKey_length_le C.F salt, tail_lt := hlt, hmac_st := by rw [hx.x1_eq]; exact hhm,
      rw_out := by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1 }
  refine (finalize_fixed3_pfx_lt64_kdf_vm_sat (C := C) hMemsetVm hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem, hpt, hmacWith_effectiveHmacKey] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq, hsp_setMem] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  obtain ⟨hf_s', hc'⟩ := hcommon_reset_of_fin (outOff := 507#64) hb hf_ref hx.common hrun' hcs hfr (by decide)
  exact ⟨hf_s', ⟨hpc', hc', (CalleeSaved.x19 hcs).trans hx.x19_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x27 hcs).trans hx.x27_eq, hm16', hout⟩⟩

private theorem fin_b1_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H] (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      HFrameS2 okmLen s₀ s'.mem ∧ StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s'.mem) s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hfin_pre : FinPre3PfxGen fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm) [] (info ++ [1#8]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.exp.common.status,
      key_le := by rw [hkdfExtractBytes, length_hmacWith]; decide, tail_lt := by have := hb.pre.info_lt; simp; omega,
      hmac_st := HmacStN.of_hmacSt (by rw [hx.x1_eq]; exact hx.hmac_32),
      rw_out := by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.exp.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.exp.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1 }
  refine (finalize_fixed3_pfx_lt64_kdf_vm_sat (C := C) hMemsetVm hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  simp only [List.nil_append] at ht1; rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem] at hfr
  obtain ⟨hf_s', hexp'⟩ := hexpCommon_reset_of_fin hb hf_ref hx.exp hrun' hcs hfr
  exact ⟨hf_s', ⟨hpc', hexp', (CalleeSaved.x21 hcs).trans hx.x21_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, ht1⟩⟩

private theorem iter_fin_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H] (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem) (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      HFrameS2 okmLen s₀ s'.mem ∧
      StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s'.mem) s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_okm : s.mem.RW okmA okmLen := HFrame.rw_okm hpre_ref hx.exp.common.frame
  have hfin_pre : FinPre3PfxGen fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm)
      (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.exp.common.status,
      key_le := by rw [hkdfExtractBytes, length_hmacWith]; decide, tail_lt := by have := hb.pre.info_lt; simp; omega,
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32,
      rw_out := by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.exp.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.exp.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1 }
  refine (finalize_fixed3_pfx_lt64_kdf_vm_sat (C := C) hMemsetVm hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem] at hout; rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem] at hfr
  have hmsg_eq : (tPrev ++ info.take 32) ++ (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) =
      tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)] := by
    rw [List.append_assoc tPrev (info.take 32), ← List.append_assoc (info.take 32), List.take_append_drop, ← List.append_assoc]
  rw [hmsg_eq] at hout
  have hokm' : s'.mem.readBytes okmA dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0; · subst h0; exact hx.okm_pre
    · have hokm_len := hb.pre.okm_len
      refine (hfr.readBytes_eq (hrw_okm.sub (by bv_omega)) (fun r hr => ?_) (by omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ - 144#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
  obtain ⟨hf_s', hexp'⟩ := hexpCommon_reset_of_fin hb hf_ref hx.exp hrun' hcs hfr
  exact ⟨hf_s', ⟨hpc', hexp', (CalleeSaved.x20 hcs).trans hx.x20_eq, (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x27 hcs).trans hx.x27_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, hout, hokm'⟩⟩

private theorem hsaved_setMem {s₀ : State} {m1 m2 m : Memory}
    (h : HSaved (s₀.setMem m1) m) : HSaved (s₀.setMem m2) m := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

set_option maxHeartbeats 1600000 in
private theorem iter_a2_exact_local [LibsignalPlacement] {b_iv : BitVec 64} {C : Crypto}
    {H : LibsignalHooks} {aligned : Prop} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    (h_compress : H lsCompress256Sym = some (compress256Hook C.F))
    {salt ikm info tPrev okmSoFar : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hread_info₀ : s₀.mem.Readable infoA info.length) (ht_len : tPrev.length = 32) (hdst : dstOff ≤ okmLen)
    (hx : StateLoopA1 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s (lsρ lsMemcpySym)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopA2 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq
  have hx29 := hx.exp.common.x29_eq; have hlr := hx.lr_eq; have hx0 := hx.x0_eq; have hx1 := hx.x1_eq; have hx2 := hx.x2_eq
  have hx19 := hx.x19_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hrw_384 : s.mem.RW (hsp s₀ + 384#64) 32 := hrw_hsp.sub (by bv_omega)
  have hinfo_all : s.mem.readBytes infoA info.length = info := HFrame.info_bytes hpre hx.exp.common.frame
  have hinfo_take : s.mem.readBytes infoA 32 = info.take 32 := by
    simpa using readBytes_slice_of_readBytes_eq s.mem infoA info hinfo_all 0 32 (by have := hpre.info_ge; omega)
  have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  have hsp_al : s.spAligned = true := by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp_eq, hhsp]
  have hread_src : s.mem.Readable infoA 32 := (hx.exp.common.frame.readable_iff infoA 32).mpr fun a ha =>
    hread_info₀ a (inRegion_sub_slice (off := 0) (len := 32) (by have := hpre.info_ge; omega) (by have := hpre.info_lt; omega) (by simpa using ha))
  have hdisj_mc : 32 = 0 ∨ DisjointRegions (hsp s₀ + 384#64) 32 infoA 32 :=
    Or.inr <| ((disjointRegions_of_outside (by have := hpre.info_ge; omega) (by decide) hpre.out_info_stk).symm.sub_left
      (hsp s₀ + 384#64) ⟨by decide, by bv_omega⟩).sub_right infoA ⟨by decide, by have := hpre.info_ge; bv_omega⟩
  refine s2_memcpy_step_placed_429_exact h_mc hrun hpc hsp_al hx0 hx1 hx2_nat hlr hinfo_take hrw_384 hread_src hdisj_mc fun c => ?_
  dsimp only [applyMemcpyClobber]
  let prk := hkdfExtractBytes C.F salt ikm
  let m₁ := s.mem.writeBytes (hsp s₀ + 384#64) (info.take 32)
  have hA1 : AgreesOutside s.mem m₁ (hsp s₀ + 384#64) 32 := agreesOutside_writeBytes_le s.mem (hsp s₀ + 384#64) (info.take 32) 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_352_592 (off := 384#64) (sz := 32) hx.exp hrun hsp_eq hx29 hA1 (by decide)
  have hcnt1_m1 : m₁.read64 (hsp s₀ + 448#64) = 1#64 := by
    rw [hA1.read64_eq (by unfold DisjointRegions; bv_omega), show hsp s₀ + 448#64 = (hsp s₀ + 352#64) + 0x60#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.1
  have hrw1 : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  dsimp only [m₁] at hcnt1_m1 hrw1; iterate 7 kdf_step
  let m₂ := m₁.write64 (hsp s₀ + 448#64) 2#64
  have hA2 : AgreesOutside m₁ m₂ (hsp s₀ + 448#64) 8 := agreesOutside_hsp_write64 (AgreesOutside.rfl' m₁ (hsp s₀ + 448#64) 8) (by decide)
  have hc2 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₂) :=
    HExpCommon.of_agreesOutside_352_592 (off := 448#64) (sz := 8) hc1 hrun hsp_eq hx29 hA2 (by decide)
  have hin_416 : m₂.readBytes (hsp s₀ + 416#64) 32 = shaStateBytes (hmacInnerInit C.F prk) := by
    rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), show hsp s₀ + 416#64 = (hsp s₀ + 352#64) + 0x40#64 by bv_lin]
    exact hx.hmac_352.2.2.2.1
  have hblk_352 : m₂.readBytes (hsp s₀ + 352#64) 64 = tPrev ++ info.take 32 := by
    change m₂.readBytes (hsp s₀ + 352#64) (32 + 32) = tPrev ++ info.take 32
    rw [readBytes_add m₂ (hsp s₀ + 352#64) 32 32, show (hsp s₀ + 352#64) + BitVec.ofNat 64 32 = hsp s₀ + 384#64 by bv_lin]
    have ht_m2 : m₂.readBytes (hsp s₀ + 352#64) 32 = tPrev := by
      rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
          hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide), ← ht_len]; exact hx.hmac_352.2.1
    have hi_m2 : m₂.readBytes (hsp s₀ + 384#64) 32 = info.take 32 := by
      rw [hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)]
      have h := readBytes_writeBytes_same s.mem (hsp s₀ + 384#64) (info.take 32) (by rw [htake_len]; decide); rwa [htake_len] at h
    rw [ht_m2, hi_m2]
  have hblk_len : (tPrev ++ info.take 32).length = 64 := by rw [List.length_append, ht_len, htake_len]
  have hrw_416 : m₂.RW (hsp s₀ + 416#64) 32 := (HFrame.rw_hsp hpre hc2.common.frame).sub (by bv_omega)
  refine s2_compress256_step_placed_429 h_compress (stPtr := hsp s₀ + 416#64) (blkPtr := hsp s₀ + 352#64)
    (lr := (blkPl_379).base + 1544#64) (st := hmacInnerInit C.F prk) (blk := tPrev ++ info.take 32)
    (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg) (by kdf_reg)
    (by rw [mem_setMem]; exact hin_416) (by rw [mem_setMem]; exact hblk_352) hblk_len (by rw [mem_setMem]; exact hrw_416) ?_
  let stBytes := shaStateBytes (C.F (hmacInnerInit C.F prk) (tPrev ++ info.take 32))
  let m₃ := m₂.writeBytes (hsp s₀ + 416#64) stBytes
  have hA3 : AgreesOutside m₂ m₃ (hsp s₀ + 416#64) 32 := agreesOutside_writeBytes_le m₂ (hsp s₀ + 416#64) stBytes 32 (by simp [stBytes, shaStateBytes_length])
  have hc3 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₃) :=
    HExpCommon.of_agreesOutside_352_592 (off := 416#64) (sz := 32) hc2 hrun hsp_eq hx29 hA3 (by decide)
  refine RunsTo.refl ⟨by kdf_reg,
    ⟨⟨by kdf_reg, by kdf_reg, by kdf_reg, by rw [mem_setMem]; exact hc3.common.saved, by rw [mem_setMem]; exact hc3.common.frame⟩,
     by rw [mem_setMem]; exact hc3.m0_eq, by rw [mem_setMem]; exact hc3.m8_eq,
     by rw [mem_setMem]; exact hc3.m16_eq, by rw [mem_setMem]; exact hc3.m24_eq, by rw [mem_setMem]; exact hc3.hmac_208⟩,
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_, ?_, ?_, ?_⟩
  · show m₃.readBytes (hsp s₀ + 416#64) 32 = stBytes
    have hlen : stBytes.length = 32 := shaStateBytes_length _
    have h := readBytes_writeBytes_same m₂ (hsp s₀ + 416#64) stBytes (by rw [hlen]; decide); rwa [hlen] at h
  · show m₃.read64 (hsp s₀ + 448#64) = 2#64
    rw [hA3.read64_eq (by unfold DisjointRegions; bv_omega)]; simp (config := { decide := true }) only [m₂, arm64_norm]
  · show m₃.readBytes (hsp s₀ + 456#64) 32 = shaStateBytes (hmacOuterInit C.F prk)
    rw [hA3.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA2.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide),
        show hsp s₀ + 456#64 = (hsp s₀ + 352#64) + 0x68#64 by bv_lin]; exact hx.hmac_352.2.2.2.2.2.1
  · show m₃.read64 (hsp s₀ + 488#64) = 1#64
    rw [hA3.read64_eq (by unfold DisjointRegions; bv_omega), hA2.read64_eq (by unfold DisjointRegions; bv_omega),
        hA1.read64_eq (by unfold DisjointRegions; bv_omega), show hsp s₀ + 488#64 = (hsp s₀ + 352#64) + 0x88#64 by bv_lin]
    exact hx.hmac_352.2.2.2.2.2.2
  · show m₃.readBytes okmA dstOff = okmSoFar
    by_cases h0 : dstOff = 0; · subst h0; exact hx.okm_pre
    · have hlen : dstOff ≤ 2 ^ 64 := by have := hpre.okm_len; omega
      have hd3 : DisjointRegions (hsp s₀ + 416#64) 32 okmA dstOff := (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 416#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd2 : DisjointRegions (hsp s₀ + 448#64) 8 okmA dstOff := (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 448#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd1 : DisjointRegions (hsp s₀ + 384#64) 32 okmA dstOff := (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 384#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      rw [hA3.readBytes_eq hd3 hlen, hA2.readBytes_eq hd2 hlen, hA1.readBytes_eq hd1 hlen]; exact hx.okm_pre

set_option maxHeartbeats 4000000 in
private theorem iter_b_exact_local [LibsignalPlacement] {b_iv : BitVec 64} {C : Crypto}
    {H : LibsignalHooks} {aligned : Prop} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
    {okmLen i rem dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hread_info₀ : s₀.mem.Readable infoA info.length) (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64) (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoopA2 hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff s₀ · (blkPl_425).base) := by
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx19 := hx.x19_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx23 := hx.x23_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx26 := hx.x26_eq; have hx27 := hx.x27_eq
  have hhsp := hsp_aligned hpre.sp_aligned; have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hx.exp.common.frame
  have hk_lt : info.length - 32 < 23 := by have := hpre.info_lt; omega
  rcases info_sub32_lemmas (by omega : info.length - 32 < 64) with ⟨hlsr6_nat, hlsr6, hand_hi, hand_lo, hlsr6_nat_eq, hlsr6_eq⟩
  rcases cmp_lt64_lemmas (by omega : info.length - 32 < 64) with ⟨h_k_ule, h_k_ult, h_k_cmp⟩
  iterate 11 kdf_step
  let prk := hkdfExtractBytes C.F salt ikm; let k := info.length - 32
  let m₀ := (s.mem.write8 (hsp s₀ + 415#64) 0#8).write8 (hsp s₀ + 415#64) (BitVec.ofNat 8 k)
  have hA0 : AgreesOutside s.mem m₀ (hsp s₀ + 415#64) 1 := by dsimp only [m₀]; prove_agrees_hsp
  have hc0 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₀) :=
    HExpCommon.of_agreesOutside_352_592 (off := 415#64) (sz := 1) hx.exp hrun hsp_eq hx29 hA0 (by decide)
  have hinfo_all : m₀.readBytes infoA info.length = info := HFrame.info_bytes hpre hc0.common.frame
  have hinfo_drop : m₀.readBytes (infoA + 32#64) k = info.drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m₀ infoA info hinfo_all 32 k (by have := hpre.info_ge; omega)
    simpa [k, List.take_of_length_le (by simp : (info.drop 32).length ≤ info.length - 32)] using h
  have hdrop_len : (info.drop 32).length = k := by simp [k]
  have hrw_352 : m₀.RW (hsp s₀ + 352#64) k := (HFrame.rw_hsp hpre hc0.common.frame).sub (by bv_omega)
  have hx2_nat : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hread_src : m₀.Readable (infoA + 32#64) k := (hc0.common.frame.readable_iff (infoA + 32#64) k).mpr fun a ha =>
    hread_info₀ a (inRegion_sub_slice (off := 32) (len := k) (by have := hpre.info_ge; omega) (by have := hpre.info_lt; omega) ha)
  have hdisj_mc : k = 0 ∨ DisjointRegions (hsp s₀ + 352#64) k (infoA + 32#64) k := by
    by_cases hk0 : k = 0; · exact Or.inl hk0
    · exact Or.inr <| ((disjointRegions_of_outside (by have := hpre.info_ge; omega) (by decide) hpre.out_info_stk).symm.sub_left
        (hsp s₀ + 352#64) ⟨by omega, by bv_omega⟩).sub_right (infoA + 32#64)
        ⟨by omega, by have := hpre.info_ge; have := hpre.info_lt; dsimp only [k] at hk0 ⊢; bv_omega⟩
  refine s2_memcpy_step_placed_429_exact h_mc (dst := hsp s₀ + 352#64) (src := infoA + 32#64)
    (lr := (blkPl_379).base + 1612#64) (len := k) (bs := info.drop 32) (by kdf_reg) (by kdf_reg)
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp_eq, hhsp]) (by kdf_reg)
    (by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, BitVec.add_zero])
    hx2_nat (by kdf_reg) (by rw [mem_setMem]; exact hinfo_drop) (by rw [mem_setMem]; exact hrw_352)
    (by rw [mem_setMem]; exact hread_src) hdisj_mc fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := m₀.writeBytes (hsp s₀ + 352#64) (info.drop 32)
  have hA1 : AgreesOutside m₀ m₁ (hsp s₀ + 352#64) 23 := agreesOutside_writeBytes_le m₀ (hsp s₀ + 352#64) (info.drop 32) 23 (by omega)
  refine RunsTo.trans (RunsTo.refl (P := fun s₁ : State =>
      s₁.pc = (blkPl_379).base + 1612#64 ∧ s₁.status = .Running ∧ s₁.sp = hsp s₀ ∧
      s₁.readReg64 .x29 = hsp s₀ + 592#64 ∧ s₁.readReg64 .x19 = hsp s₀ + 352#64 ∧
      s₁.readReg64 .x22 = okmA + BitVec.ofNat 64 dstOff ∧ s₁.readReg64 .x23 = hsp s₀ + 352#64 ∧
      s₁.readReg64 .x24 = 32#64 ∧ s₁.readReg64 .x26 = BitVec.ofNat 64 rem ∧
      s₁.readReg64 .x27 = BitVec.ofNat 64 i ∧ s₁.readReg64 .x28 = hsp s₀ + 352#64 ∧ (∃ _ : Unit, s₁.mem = m₁))
    ⟨by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg,
     by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ⟨(), by rw [State.mem_setPC, mem_setMem, mem_setMem]⟩⟩) ?_
  rintro s₁ ⟨hpc₁, hrun₁, hsp₁, hx29_1, hx19_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1, hx28_1, hm₁_box⟩
  clear hpc hrun hsp_eq hx29 hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hrw_hsp hlsr6_nat hlsr6 hand_hi hand_lo
    hlsr6_nat_eq hlsr6_eq h_k_ule h_k_ult h_k_cmp hinfo_all hinfo_drop hrw_352 hx2_nat hread_src hdisj_mc c
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ s₁ :=
    HExpCommon.of_agreesOutside_352_592 (off := 352#64) (sz := 23) hc0 hrun₁ hsp₁ hx29_1
      (by rcases hm₁_box with ⟨_, h⟩; rw [h]; exact hA1) (by decide)
  have hm16_1 : s₁.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := hc1.m16_eq
  have hpos_415 : s₁.mem.read8 (hsp s₀ + 415#64) = BitVec.ofNat 8 k := by
    rcases hm₁_box with ⟨_, hm₁_save⟩; rw [hm₁_save]
    have h1 := writeBytes_readBytes_disj m₀ (hsp s₀ + 352#64) (info.drop 32) (hsp s₀ + 415#64) 1
      (fun _ _ => by unfold DisjointRegions; bv_omega) (by decide)
    dsimp only [Memory.readBytes, BitVec.add_zero] at h1; rw [List.cons.inj h1 |>.1]; exact Memory.read8_write8_same _ _ _
  have hrw1 : s₁.mem.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  rcases canWrite_hsp_352_add hrw1 (by omega : k < 64) with ⟨hcw_pos1, hcw_pos2⟩
  have hze32 := zeroExtend32_ofNat8_eq_truncate32 (by omega : k < 64); have hze64 := zeroExtend64_ofNat8 (by omega : k < 64)
  have hze64_32 := zeroExtend64_truncate32_ofNat64 (by omega : k < 64); have hand255 := zeroExtend64_and255_truncate32_ofNat64 (by omega : k < 64)
  have hand64_255 := and64_255_ofNat64 (by omega : k < 64); have hand40 := and_0xffffffffff_ofNat64 (by omega : k < 64)
  rcases cmp32_lt63_lemmas (by omega : k < 63) with ⟨hcmp63_eq, hcmp63_ne, hcmp63_z⟩
  have hadd1_k := zeroExtend64_add1_truncate32_ofNat64 (by omega : k < 63)
  rcases iter_counter_lemmas hi with ⟨hi_eq, hi_ne, hi_z, hi_add1, hi1_ze⟩
  have hdst_add : (okmA + BitVec.ofNat 64 dstOff) + 32#64 = okmA + BitVec.ofNat 64 (dstOff + 32) := by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hrem_sub : BitVec.ofNat 64 rem - 32#64 = BitVec.ofNat 64 (rem - 32) := by rcases hrem with rfl | rfl <;> rfl
  dsimp only [k] at hpos_415 hcw_pos1 hcw_pos2 hze32 hze64 hze64_32 hand255 hand64_255 hand40 hcmp63_eq hcmp63_ne hcmp63_z hadd1_k
  iterate 31 kdf_step
  refine RunsTo.refl ?_; rcases hm₁_box with ⟨_, hm₁_save⟩
  have hhm_352 : HmacStN ((((s₁.mem.write8 (hsp s₀ + 32#64) (BitVec.ofNat 8 (i + 1))).write8
        (hsp s₀ + 352#64 + BitVec.ofNat 64 k) (BitVec.ofNat 8 (i + 1))).write8 (hsp s₀ + 415#64) (BitVec.ofNat 8 (k + 1))))
      (hsp s₀ + 352#64) C.F prk (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) := by
    rw [hm₁_save]; have htake_len : (info.take 32).length = 32 := List.length_take_of_le hpre.info_ge
    have hblk_len : (tPrev ++ info.take 32).length = 64 := by rw [List.length_append, ht_len, htake_len]
    simpa only [hdrop_len] using HmacStN.of_tail_counter_352 (b0 := 0#8) (b1 := BitVec.ofNat 8 k)
      (c := BitVec.ofNat 8 (i + 1)) hblk_len (by rw [hdrop_len]; omega : (info.drop 32).length < 55)
      hx.in_416 hx.cnt_448 hx.out_456 hx.cnt_488
  refine ⟨by kdf_reg, HExpCommon.of_agreesOutside_32_560 (off := 32#64) (sz := 464) hc1
      (by kdf_reg) (by kdf_reg) (by kdf_reg) (by prove_agrees_hsp) (by decide) (by prove_hmac_208 hc1.hmac_208),
    by kdf_reg, by kdf_reg, by kdf_reg, by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hdst_add],
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by rw [State.readReg64_setMem]; simp (config := { decide := true }) only [arm64_norm, hrem_sub],
    by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [mem_setMem]
    refine HmacStN.of_copy_352_32 hhm_352 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp (config := { decide := true }) only [k, arm64_norm]
  · by_cases h0 : dstOff = 0; · subst h0; exact hx.okm_pre
    · have hlen : dstOff ≤ 2 ^ 64 := by have := hpre.okm_len; omega
      have hd2 : DisjointRegions (hsp s₀ + 32#64) 464 okmA dstOff := (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd1 : DisjointRegions (hsp s₀ + 352#64) 23 okmA dstOff := (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 352#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      have hd0 : DisjointRegions (hsp s₀ + 415#64) 1 okmA dstOff := (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 415#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by have := hpre.okm_len; bv_omega⟩
      refine Eq.trans (AgreesOutside.readBytes_eq (m₁ := s₁.mem) (by prove_agrees_hsp) hd2 hlen) ?_
      rw [hm₁_save, hA1.readBytes_eq hd1 hlen, hA0.readBytes_eq hd0 hlen]; exact hx.okm_pre

set_option maxHeartbeats 1600000 in
private theorem iter_d_continue_exact_local [LibsignalPlacement] {b_iv : BitVec 64} {C : Crypto}
    {H : LibsignalHooks} {aligned : Prop} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
    {okmLen : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned) (hokm96 : okmLen = 96)
    (hx : StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen 1 64 32 s₀ s) :
    let tNext := hmacWith C.F (hkdfExtractBytes C.F salt ikm) (tPrev ++ info ++ [2#8])
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s
      (StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tNext (okmSoFar ++ tNext) okmLen 2 32 64 s₀) := by
  intro tNext; subst hokm96
  have ht_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 = tNext := hx.t_540
  have htNext_len : tNext.length = 32 := length_hmacWith _ _ _
  generalize tNext = tN at ht_540 htNext_len ⊢
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 : s.readReg64 .x20 = okmA + 64#64 := hx.x20_eq; have hx21 := hx.x21_eq; have hx22 : s.readReg64 .x22 = okmA + 32#64 := hx.x22_eq
  have hx24 := hx.x24_eq; have hx25 := hx.x25_eq; have hx26 : s.readReg64 .x26 = 32#64 := hx.x26_eq
  have hx27 : s.readReg64 .x27 = 1#64 := hx.x27_eq; have hx28 := hx.x28_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_dst : s.mem.RW (okmA + 32#64) 32 := (HFrame.rw_okm hpre hx.exp.common.frame).sub (by bv_omega)
  have hread_540 : s.mem.Readable (hsp s₀ + 540#64) 32 := readable_of_rw ((HFrame.rw_hsp hpre hx.exp.common.frame).sub (by bv_omega))
  have hdisj_mc : 32 = 0 ∨ DisjointRegions (okmA + 32#64) 32 (hsp s₀ + 540#64) 32 :=
    Or.inr <| (hpre.disj_okm_stk.sub_left (okmA + 32#64) ⟨by decide, by bv_omega⟩).sub_right (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩
  iterate 4 kdf_step
  refine s2_memcpy_step_placed_429_exact h_mc hrun rfl
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp_eq, hhsp])
    rfl rfl rfl rfl ht_540 hrw_dst hread_540 hdisj_mc fun c => ?_
  dsimp only [applyMemcpyClobber]
  let prk := hkdfExtractBytes C.F salt ikm; let m₁ := s.mem.writeBytes (okmA + 32#64) tN
  have hA1 : AgreesOutside s.mem m₁ (okmA + 32#64) 32 := agreesOutside_writeBytes_le s.mem (okmA + 32#64) tN 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA 96 s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_okm hpre hx.exp hrun hsp_eq hx29 hA1 ⟨by decide, by decide⟩
  have hm24_1 : m₁.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc1.m24_eq
  have hrw1_hsp : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  dsimp only [m₁] at hm24_1 hrw1_hsp; iterate 9 kdf_step
  refine RunsTo.refl ?_
  have hA2 : AgreesOutside m₁ ((((m₁.write64 (hsp s₀ + 508#64) (m₁.read64 (hsp s₀ + 540#64))).write64
        (hsp s₀ + 516#64) (m₁.read64 (hsp s₀ + 548#64))).write64 (hsp s₀ + 524#64) (m₁.read64 (hsp s₀ + 556#64))).write64
        (hsp s₀ + 532#64) (m₁.read64 (hsp s₀ + 564#64))) (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
  refine ⟨by kdf_reg, HExpCommon.of_agreesOutside_352_592 (off := 508#64) (sz := 32) hc1 (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide),
    by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, by kdf_reg, ?_, ?_⟩
  · simp only [mem_setMem]
    have ht_m1 : m₁.readBytes (hsp s₀ + 540#64) 32 = tN :=
      (hA1.readBytes_eq ((hpre.disj_okm_stk.sub_left (okmA + 32#64) ⟨by decide, by bv_omega⟩).sub_right (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩) (by decide)).trans ht_540
    exact readBytes_32_hsp_508_of_540 ht_m1
      (by simp (config := { decide := true }) only [m₁, arm64_norm]) (by simp (config := { decide := true }) only [m₁, arm64_norm])
      (by simp (config := { decide := true }) only [m₁, arm64_norm]) (by simp (config := { decide := true }) only [m₁, arm64_norm])
  · have hd2 : DisjointRegions (hsp s₀ + 508#64) 32 okmA 64 := (hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by decide, by bv_omega⟩
    dsimp only [mem_setMem]; rw [hA2.readBytes_eq hd2 (by decide), show (64 : ℕ) = 32 + 32 from rfl, readBytes_add m₁ okmA 32 32]
    have hpre_m1 : m₁.readBytes okmA 32 = okmSoFar := (hA1.readBytes_eq (by unfold DisjointRegions; bv_omega) (by decide)).trans hx.okm_pre
    have hnext_m1 : m₁.readBytes (okmA + BitVec.ofNat 64 32) 32 = tN := by
      have h := readBytes_writeBytes_same s.mem (okmA + 32#64) tN (by rw [htNext_len]; decide); rwa [htNext_len] at h
    rw [hpre_m1, hnext_m1]

set_option maxHeartbeats 1600000 in
private theorem iter_d_done_exact_local [LibsignalPlacement] {b_iv : BitVec 64} {C : Crypto}
    {H : LibsignalHooks} {aligned : Prop} (h_mc : HookSatExactMemcpy H lsMemcpySym)
    {salt ikm info tPrev okmSoFar : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
    {okmLen i dstOff : ℕ} {s₀ s : State}
    (hpre : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ b_iv aligned)
    (hdst_pos : 0 < dstOff) (hdst_eq : dstOff + 32 = okmLen)
    (hokm_eq : okmSoFar ++ hmacWith C.F (hkdfExtractBytes C.F salt ikm) (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) =
      hkdfExpand C.F (hkdfExtractBytes C.F salt ikm) info okmLen)
    (hx : StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i 32 dstOff s₀ s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s (StateDone hkdfCodeFakeB C.F salt ikm info okmA okmLen s₀) := by
  let prk := hkdfExtractBytes C.F salt ikm
  have ht_540 : s.mem.readBytes (hsp s₀ + 540#64) 32 = hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) := hx.t_540
  have htNext_len : (hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)])).length = 32 := length_hmacWith _ _ _
  generalize hmacWith C.F prk (tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)]) = tN at ht_540 htNext_len hokm_eq
  have hpc := hx.pc_eq; have hrun := hx.exp.common.status; have hsp_eq := hx.exp.common.sp_eq; have hx29 := hx.exp.common.x29_eq
  have hx20 := hx.x20_eq; have hx21 := hx.x21_eq; have hx22 := hx.x22_eq; have hx24 := hx.x24_eq; have hx25 := hx.x25_eq
  have hx26 : s.readReg64 .x26 = 0#64 := hx.x26_eq; have hx27 := hx.x27_eq; have hx28 := hx.x28_eq; have hhsp := hsp_aligned hpre.sp_aligned
  have hrw_dst : s.mem.RW (okmA + BitVec.ofNat 64 dstOff) 32 := (HFrame.rw_okm hpre hx.exp.common.frame).sub (by have := hpre.okm_len; bv_omega)
  have hread_540 : s.mem.Readable (hsp s₀ + 540#64) 32 := readable_of_rw ((HFrame.rw_hsp hpre hx.exp.common.frame).sub (by bv_omega))
  have hdisj_mc : 32 = 0 ∨ DisjointRegions (okmA + BitVec.ofNat 64 dstOff) 32 (hsp s₀ + 540#64) 32 :=
    Or.inr <| (hpre.disj_okm_stk.sub_left (okmA + BitVec.ofNat 64 dstOff) ⟨by decide, by have := hpre.okm_len; bv_omega⟩).sub_right (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩
  iterate 4 kdf_step
  refine s2_memcpy_step_placed_429_exact h_mc hrun rfl
    (by simp (config := { decide := true }) only [State.spAligned, arm64_norm, hsp_eq, hhsp])
    rfl rfl rfl rfl ht_540 hrw_dst hread_540 hdisj_mc fun c => ?_
  dsimp only [applyMemcpyClobber]
  let m₁ := s.mem.writeBytes (okmA + BitVec.ofNat 64 dstOff) tN
  have hA1 : AgreesOutside s.mem m₁ (okmA + BitVec.ofNat 64 dstOff) 32 := agreesOutside_writeBytes_le s.mem (okmA + BitVec.ofNat 64 dstOff) tN 32 (by omega)
  have hc1 : HExpCommon C.F prk info infoA okmLen s₀ (s.setMem m₁) :=
    HExpCommon.of_agreesOutside_okm hpre hx.exp hrun hsp_eq hx29 hA1 ⟨by decide, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hpre.okm_len; omega)]; omega⟩
  have hm0_1 : m₁.read64 (hsp s₀) = BitVec.ofNat 64 okmLen := by simpa [mem_setMem, BitVec.add_zero] using hc1.m0_eq
  have hm0_1' : m₁.read64 (hsp s₀ + 0#64) = BitVec.ofNat 64 okmLen := hc1.m0_eq
  have hm24_1 : m₁.read64 (hsp s₀ + 24#64) = hsp s₀ + 508#64 := hc1.m24_eq
  have hrw1_hsp : m₁.RW (hsp s₀) 688 := HFrame.rw_hsp hpre hc1.common.frame
  rcases okmLen_lt_8161_lemmas hpre.okm_len with ⟨hokm_c, hokm_ule, hokm_ult⟩
  dsimp only [m₁] at hm0_1 hm0_1' hm24_1 hrw1_hsp; iterate 13 kdf_step
  refine RunsTo.refl ?_
  have hA2 : AgreesOutside m₁ ((((m₁.write64 (hsp s₀ + 508#64) (m₁.read64 (hsp s₀ + 540#64))).write64
        (hsp s₀ + 516#64) (m₁.read64 (hsp s₀ + 548#64))).write64 (hsp s₀ + 524#64) (m₁.read64 (hsp s₀ + 556#64))).write64
        (hsp s₀ + 532#64) (m₁.read64 (hsp s₀ + 564#64))) (hsp s₀ + 508#64) 32 := by prove_agrees_hsp
  refine ⟨by kdf_reg, HCommon.of_agreesOutside_hsp (off := 508#64) (sz := 32) hc1.common (by kdf_reg) (by kdf_reg) (by kdf_reg) hA2 (by decide), ?_⟩
  have hd2 : DisjointRegions (hsp s₀ + 508#64) 32 okmA okmLen := hpre.disj_okm_stk.symm.sub_left (hsp s₀ + 508#64) ⟨by decide, by bv_omega⟩
  dsimp only [mem_setMem]; rw [hA2.readBytes_eq hd2 (by have := hpre.okm_len; omega), ← hdst_eq, readBytes_add m₁ okmA dstOff 32]
  have hpre_m1 : m₁.readBytes okmA dstOff = okmSoFar :=
    (hA1.readBytes_eq (by have := hpre.okm_len; unfold DisjointRegions; bv_omega) (by have := hpre.okm_len; omega)).trans hx.okm_pre
  have hnext_m1 : m₁.readBytes (okmA + BitVec.ofNat 64 dstOff) 32 = tN := by
    have h := readBytes_writeBytes_same s.mem (okmA + BitVec.ofNat 64 dstOff) tN (by rw [htNext_len]; decide); rwa [htNext_len] at h
  rw [hpre_m1, hnext_m1, hokm_eq, hdst_eq]

theorem hkdf_to_slice_kdf_vm_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    {salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64}
    {okmLen : ℕ} {s₀ : State} (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ fun sf =>
      sf.pc = s₀.readReg64 .lr ∧ sf.status = .Running ∧ CalleeSaved s₀ sf ∧
      sf.mem.readBytes okmA okmLen = hkdfExpand C.F (hkdfExtractBytes C.F salt ikm) info okmLen ∧
      HFrameS2 okmLen s₀ sf.mem := by
  have heq379 : ∀ X, (blkPC_379).rebase (blkPl_379).base X = libsignalSessionLib.blockProgram lsmpl 379 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := (blkPC_379).rebase (blkPl_379).base X)
  have runsTo_rebase_of_block379 : ∀ {X : LibsignalHooks} {s : State} {P : State → Prop},
      RunsTo ((blkPC_379).rebase (blkPl_379).base X) s P → RunsTo (libsignalSessionLib.blockProgram lsmpl 379 X) s P :=
    fun {X} _ _ h => heq379 X ▸ h
  let kp379 := ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl 379 H)
  let hmcQ (m : Memory) := hmacNoMemsetExcHooks_memcpy (F := C.F) hH.memcpy m kp379
  let hc256Q (m : Memory) := hmacNoMemsetExcHooks_compress C.F H m kp379
  have hsp0_of (m : Memory) : hsp (ProofLib.stripS kp379 (s₀.setMem m)) = hsp s₀ := by cases s₀; rfl
  have hs_id : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
  have hf₀ : HFrameS2 okmLen s₀ s₀.mem := S2Frame.refl s₀.mem _
  have hc0 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateENfs1 hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen (s₀.setMem s₀.mem) · (blkPl_402).base) := by
    rw [hs_id]
    refine lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl₀
      (heq379 H ▸ seg_e0_placed_runsTo hb.pre)
      (heq379 (hmacNoMemsetExcHooks C.F H s₀.mem kp379) ▸ seg_e0_placed_runsTo (hpre_stripS kp379 hb.pre))
      (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
      fun sf hvm ⟨hpc, hc, hlr, hx0, hx1, hx2, hx22, hx23, hx24, hx25, hx26, hx27⟩ =>
        ⟨(by cases sf; exact hpc), unstrip_hcommon hc hvm.perm_eq, (by cases sf; exact hlr),
          (by cases s₀; cases sf; exact hx0), (by cases sf; exact hx1), (by cases sf; exact hx2),
          (by cases sf; exact hx22), (by cases sf; exact hx23), (by cases sf; exact hx24),
          (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27)⟩
  have hext1 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ fun s =>
      HFrameS2 okmLen s₀ s.mem ∧ StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s.mem) s := by
    refine hc0.trans_full fun s_n1 hn1 hkf1 => ?_
    have hcl_n1 := hcl₀.of_keepsFrozen hkf1; have hpre1 := hb.at_mem s₀.mem hf₀
    have hx2_nat : (s_n1.readReg64 .x2).toNat = salt.length := by
      rw [hn1.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hb.pre.salt_lt; omega)]
    have hrw_hsp1 : s_n1.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem s₀.mem) hpre1 hn1.common.frame
    have hnfs1 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_n1 fun sr1 =>
        HFrameS2 okmLen s₀ sr1.mem ∧ StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen (s₀.setMem sr1.mem) sr1 :=
      (nfs_gen_vm (C := C) hMemsetVm hcl_n1 hn1.pc_eq hn1.common.status
        (by rw [hx2_nat]; exact hb.pre.salt_lt)
        (by rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_bytes hpre1 hn1.common.frame)
        (by rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_read hpre1 hn1.common.frame)
        (by rw [← nfs3PlacedFakeB_add_iv, hn1.common.sp_eq, hsp_setMem]; exact hb.pre.disj_iv_stk.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩)
        (by rw [hn1.x0_eq, hsp_setMem]; exact hrw_hsp1.sub (by bv_omega))
        (by rw [hn1.common.sp_eq]; exact HFrame.rw_sub_544 hpre1 hn1.common.frame)
        (by rw [hn1.x0_eq, hn1.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
        (by rw [hn1.x1_eq, hx2_nat]; exact (hn1.common.frame.readable_iff _ _).mpr hb.read_salt)
        (by rw [hn1.x1_eq, hx2_nat, hn1.common.sp_eq, hsp_setMem]
            exact hb.pre.disj_salt_stk.imp id fun hd => hd.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩)
        (by rw [hn1.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)).mono
        fun sr1 ⟨hpc', hrun', hcs', htag', hhm', hfr'⟩ => by
          rw [hn1.lr_eq] at hpc'; rw [hn1.x0_eq, hsp_setMem] at htag'
          have hx0_8 : s_n1.readReg64 .x0 + 8#64 = hsp s₀ + 40#64 := by rw [hn1.x0_eq, hsp_setMem]; bv_lin
          have hsalt_s : s_n1.mem.readBytes (s_n1.readReg64 .x1) (s_n1.readReg64 .x2).toNat = salt := by
            rw [hn1.x1_eq, hx2_nat]; exact HFrame.salt_bytes hpre1 hn1.common.frame
          rw [hx0_8, hsalt_s] at hhm'; rw [hn1.x0_eq, hn1.common.sp_eq, hsp_setMem] at hfr'
          obtain ⟨hf_r1, hc_r1⟩ := hcommon_reset_of_nfs (retOff := 32#64) hb hf₀ hn1.common hrun' hcs' hfr' (by decide)
          exact ⟨hf_r1, ⟨hpc', hc_r1,
            (CalleeSaved.x22 hcs').trans hn1.x22_eq, (CalleeSaved.x23 hcs').trans hn1.x23_eq,
            (CalleeSaved.x24 hcs').trans hn1.x24_eq, (CalleeSaved.x25 hcs').trans hn1.x25_eq,
            (CalleeSaved.x26 hcs').trans hn1.x26_eq, (CalleeSaved.x27 hcs').trans hn1.x27_eq, htag', hhm'⟩⟩
    refine hnfs1.trans_full fun sr1 ⟨hf_r1, hsr1_ref⟩ hkf_r1 => ?_
    have hcl_r1 := hcl_n1.of_keepsFrozen hkf_r1; have hc_r1 := hsr1_ref.common; have hsr1 := hsr1_ref
    have hsr1_strip : StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen
        (ProofLib.stripS kp379 (s₀.setMem sr1.mem)) (ProofLib.stripS kp379 sr1) :=
      ⟨(by cases sr1; exact hsr1.pc_eq), stripS_hcommon_refl kp379 hc_r1, (by cases sr1; exact hsr1.x22_eq),
        (by cases sr1; exact hsr1.x23_eq), (by cases sr1; exact hsr1.x24_eq), (by cases sr1; exact hsr1.x25_eq),
        (by cases sr1; exact hsr1.x26_eq), (by cases sr1; exact hsr1.x27_eq),
        by rw [hsp0_of, stripS_read64]; exact hsr1.tag_32, by rw [hsp0_of, stripS_hmacSt]; exact hsr1.hmac_40⟩
    have hpre_r1 := hb.at_mem sr1.mem hf_r1; have hread_ikm_r1 := s2_readable hf_r1 hb.read_ikm
    have hread_ikm_r1_s : (ProofLib.stripS kp379 (s₀.setMem sr1.mem)).mem.Readable ikmA ikm.length :=
      stripExecOutside_readable kp379 sr1.mem _ _ hread_ikm_r1
    have hc1 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) sr1
        (StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem sr1.mem) · (blkPl_425).base) := by
      refine lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_r1
        (heq379 H ▸ (seg_e1_placed_runsTo_exact hH.memcpy hH.compress256 hpre_r1 hread_ikm_r1 hsr1_ref).trans fun _ hs2 => seg_e1d_placed_runsTo hpre_r1 hs2)
        (heq379 (hmacNoMemsetExcHooks C.F H sr1.mem kp379) ▸
          (seg_e1_placed_runsTo_exact (hmcQ sr1.mem) (hc256Q sr1.mem) (hpre_stripS kp379 hpre_r1) hread_ikm_r1_s hsr1_strip).trans
          fun _ hs2 => seg_e1d_placed_runsTo (hpre_stripS kp379 hpre_r1) hs2)
        (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
        fun sf hvm ⟨hpc, hc, hlr, hx0, hx1, hx19, hx22, hx25, hx26, hx27, hm16, ⟨pfx, tail, hpt, hmod, hlt, hhm⟩⟩ => ?_
      rw [hsp0_of, stripS_read64] at hm16; rw [hsp0_of, stripS_hmacStN] at hhm
      exact ⟨(by cases sf; exact hpc), unstrip_hcommon hc hvm.perm_eq, (by cases sf; exact hlr), (by cases s₀; cases sf; exact hx0),
        (by cases s₀; cases sf; exact hx1), (by cases s₀; cases sf; exact hx19), (by cases sf; exact hx22),
        (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27), hm16, ⟨pfx, tail, hpt, hmod, hlt, hhm⟩⟩
    exact hc1.trans_full fun s_ef hef hkf_ef => fin_extract_vm hMemsetVm (hcl_r1.of_keepsFrozen hkf_ef) hb hf_r1 hef
  have hb1_ret : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s₀ fun s =>
      HFrameS2 okmLen s₀ s.mem ∧ StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s.mem) s := by
    refine hext1.trans_full fun s_rf ⟨hf_rf, hs_rf⟩ hkf_rf => ?_
    have hcl_rf := hcl₀.of_keepsFrozen hkf_rf; have hpre_rf := hb.at_mem s_rf.mem hf_rf
    have hs_rf_strip : StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (ProofLib.stripS kp379 (s₀.setMem s_rf.mem)) (ProofLib.stripS kp379 s_rf) :=
      ⟨(by cases s_rf; exact hs_rf.pc_eq), stripS_hcommon_refl kp379 hs_rf.common, (by cases s₀; cases s_rf; exact hs_rf.x19_eq),
        (by cases s_rf; exact hs_rf.x22_eq), (by cases s_rf; exact hs_rf.x25_eq), (by cases s_rf; exact hs_rf.x26_eq), (by cases s_rf; exact hs_rf.x27_eq),
        by rw [hsp0_of, stripS_read64]; exact hs_rf.m16_eq, by rw [hsp0_of, stripS_readBytes]; exact hs_rf.prk_507⟩
    have hc2 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_rf
        (StateENfs2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s_rf.mem) · (blkPl_402).base) := by
      refine lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_rf
        (heq379 H ▸ seg_e2_placed_runsTo hpre_rf hs_rf)
        (heq379 (hmacNoMemsetExcHooks C.F H s_rf.mem kp379) ▸ seg_e2_placed_runsTo (hpre_stripS kp379 hpre_rf) hs_rf_strip)
        (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
        fun sf hvm ⟨hpc, hc, hlr, hx0, hx1, hx2, hx19, hx22, hx25, hx26, hx27, hm16, hprk⟩ => ?_
      rw [hsp0_of, stripS_read64] at hm16; rw [hsp0_of, stripS_readBytes] at hprk
      exact ⟨(by cases sf; exact hpc), unstrip_hcommon hc hvm.perm_eq, (by cases sf; exact hlr), (by cases s₀; cases sf; exact hx0),
        (by cases s₀; cases sf; exact hx1), (by cases sf; exact hx2), (by cases s₀; cases sf; exact hx19),
        (by cases sf; exact hx22), (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27), hm16, hprk⟩
    refine hc2.trans_full fun s_n2 hn2 hkf_n2 => ?_
    have hcl_n2 := hcl_rf.of_keepsFrozen hkf_n2; have hx2_nat : (s_n2.readReg64 .x2).toNat = 32 := by rw [hn2.x2_eq]; rfl
    have hrw_hsp2 : s_n2.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem s_rf.mem) hpre_rf hn2.common.frame
    have hnfs2 := (nfs_le64_vm (C := C) (H := H) hcl_n2 hn2.pc_eq hn2.common.status (by rw [hx2_nat]; decide)
      (by rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_bytes hpre_rf hn2.common.frame)
      (by rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_read hpre_rf hn2.common.frame)
      (by rw [← nfs3PlacedFakeB_add_iv, hn2.common.sp_eq, hsp_setMem]; exact hb.pre.disj_iv_stk.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩)
      (by rw [hn2.x0_eq, hsp_setMem]; exact hrw_hsp2.sub (by bv_omega))
      (by rw [hn2.common.sp_eq]; exact HFrame.rw_sub_544 hpre_rf hn2.common.frame)
      (by rw [hn2.x0_eq, hn2.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
      (by rw [hn2.x1_eq, hx2_nat, hsp_setMem]; exact readable_of_rw (hrw_hsp2.sub (by bv_omega)))
      (by rw [hn2.x1_eq, hx2_nat, hn2.common.sp_eq, hsp_setMem]; exact Or.inr (by unfold DisjointRegions; bv_omega))
      (by rw [hn2.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)).mono
      fun sr2 ⟨hpc', hrun', hcs', htag', hhm', hfr'⟩ => by
        rw [hn2.lr_eq] at hpc'; rw [hn2.x0_eq, hsp_setMem] at htag'
        have hx0_8 : s_n2.readReg64 .x0 + 8#64 = hsp s₀ + 360#64 := by rw [hn2.x0_eq, hsp_setMem]; bv_lin
        have hprk_s : s_n2.mem.readBytes (s_n2.readReg64 .x1) (s_n2.readReg64 .x2).toNat = hkdfExtractBytes C.F salt ikm := by
          rw [hn2.x1_eq, hx2_nat]; exact hn2.prk_507
        rw [hx0_8, hprk_s] at hhm'; rw [hn2.x0_eq, hn2.common.sp_eq, hsp_setMem] at hfr'
        have hm16' : sr2.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
          refine (CryptoVerification.LibsignalTripleRatchet.Expand.Frame.read64_eq hfr' fun r hr => ?_).trans hn2.m16_eq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
        exact (⟨hpc', HCommon.of_nfs_frame (retOff := 352#64) hn2.common hrun' hcs' hfr' (by decide),
          (CalleeSaved.x19 hcs').trans hn2.x19_eq, (CalleeSaved.x22 hcs').trans hn2.x22_eq, (CalleeSaved.x25 hcs').trans hn2.x25_eq,
          (CalleeSaved.x26 hcs').trans hn2.x26_eq, (CalleeSaved.x27 hcs').trans hn2.x27_eq, hm16', htag', hhm'⟩ :
          StateERet2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem s_rf.mem) sr2)
    refine hnfs2.trans_full fun sr2 hsr2 hkf_r2 => ?_
    have hcl_r2 := hcl_n2.of_keepsFrozen hkf_r2; have hf_r2 := hframeS2_step hf_rf hsr2.common.frame
    have hc_r2 : HCommon okmLen (s₀.setMem sr2.mem) sr2 :=
      ⟨hsr2.common.status, hsr2.common.sp_eq, hsr2.common.x29_eq, hsaved_setMem hsr2.common.saved, Frame.refl _ _⟩
    have hsr2_ref : StateERet2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem sr2.mem) sr2 :=
      ⟨hsr2.pc_eq, hc_r2, hsr2.x19_eq, hsr2.x22_eq, hsr2.x25_eq, hsr2.x26_eq, hsr2.x27_eq, hsr2.m16_eq, hsr2.tag_352, hsr2.hmac_360⟩
    have hsr2_strip : StateERet2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (ProofLib.stripS kp379 (s₀.setMem sr2.mem)) (ProofLib.stripS kp379 sr2) :=
      ⟨(by cases sr2; exact hsr2.pc_eq), stripS_hcommon_refl kp379 hc_r2, (by cases s₀; cases sr2; exact hsr2.x19_eq),
        (by cases sr2; exact hsr2.x22_eq), (by cases sr2; exact hsr2.x25_eq), (by cases sr2; exact hsr2.x26_eq), (by cases sr2; exact hsr2.x27_eq),
        by rw [hsp0_of, stripS_read64]; exact hsr2.m16_eq, by rw [hsp0_of, stripS_read64]; exact hsr2.tag_352, by rw [hsp0_of, stripS_hmacSt]; exact hsr2.hmac_360⟩
    have hpre_r2 := hb.at_mem sr2.mem hf_r2; have hread_info_r2 := s2_readable hf_r2 hb.read_info
    have hread_info_r2_s : (ProofLib.stripS kp379 (s₀.setMem sr2.mem)).mem.Readable infoA info.length :=
      stripExecOutside_readable kp379 sr2.mem _ _ hread_info_r2
    have hc3 : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) sr2
        (StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem sr2.mem) · (blkPl_425).base) := by
      refine lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_r2
        (heq379 H ▸ (seg_e3_placed_runsTo hpre_r2 hsr2_ref).trans fun _ hs0 =>
          (seg_b1a_placed_runsTo hpre_r2 hs0).trans fun _ hs1 => seg_b1b_placed_runsTo_exact hH.memcpy hpre_r2 hread_info_r2 hs1)
        (heq379 (hmacNoMemsetExcHooks C.F H sr2.mem kp379) ▸
          (seg_e3_placed_runsTo (hpre_stripS kp379 hpre_r2) hsr2_strip).trans fun _ hs0 =>
          (seg_b1a_placed_runsTo (hpre_stripS kp379 hpre_r2) hs0).trans fun _ hs1 =>
          seg_b1b_placed_runsTo_exact (hmcQ sr2.mem) (hpre_stripS kp379 hpre_r2) hread_info_r2_s hs1)
        (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status)
        fun sf hvm ⟨hpc, hexp, hlr, hx0, hx1, hx21, hx22, hx24, hx25, hx26, hx28, hhm⟩ => ?_
      rw [hsp0_of, stripS_hmacSt] at hhm
      exact ⟨(by cases sf; exact hpc), unstrip_hexpCommon hexp hvm.perm_eq, (by cases sf; exact hlr),
        (by cases s₀; cases sf; exact hx0), (by cases s₀; cases sf; exact hx1), (by cases sf; exact hx21),
        (by cases sf; exact hx22), (by cases sf; exact hx24), (by cases sf; exact hx25),
        (by cases sf; exact hx26), (by cases s₀; cases sf; exact hx28), hhm⟩
    exact hc3.trans_full fun s_bf hbf hkf_bf => fin_b1_vm hMemsetVm (hcl_r2.of_keepsFrozen hkf_bf) hb hf_r2 hbf
  have hiter_vm : ∀ {tPrev okmSoFar : List (BitVec 8)} {i rem dstOff : ℕ} {s : State},
      LibsignalCodeLoaded lsmpl s.mem → HFrameS2 okmLen s₀ s.mem →
      tPrev.length = 32 → (i = 1 ∨ i = 2) → (rem = 32 ∨ rem = 64) → dstOff + 32 ≤ okmLen →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s.mem) s →
      RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
        HFrameS2 okmLen s₀ s'.mem ∧ StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s'.mem) s' := by
    intro tPrev okmSoFar i rem dstOff s hcl_s hf_s ht_len hi hrem hdst hl
    have hpre_s := hb.at_mem s.mem hf_s; have hread_info_s := s2_readable hf_s hb.read_info
    have hread_info_s_q : (ProofLib.stripS kp379 (s₀.setMem s.mem)).mem.Readable infoA info.length :=
      stripExecOutside_readable kp379 s.mem _ _ hread_info_s
    have hl_strip : StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff
        (ProofLib.stripS kp379 (s₀.setMem s.mem)) (ProofLib.stripS kp379 s) :=
      ⟨(by cases s; exact hl.pc_eq), stripS_hexpCommon_refl kp379 hl.exp, (by cases s; exact hl.x12_eq),
        (by cases s₀; cases s; exact hl.x21_eq), (by cases s; exact hl.x22_eq), (by cases s; exact hl.x25_eq),
        (by cases s; exact hl.x26_eq), (by cases s; exact hl.x27_eq), (by cases s₀; cases s; exact hl.x28_eq),
        by rw [hsp0_of, stripS_readBytes]; exact hl.t_508, by rw [stripS_readBytes]; exact hl.okm_pre⟩
    have hc_it : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s
        (StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff (s₀.setMem s.mem) · (blkPl_425).base) := by
      refine lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_s
        (heq379 H ▸ (iter_a1_placed_runsTo hpre_s ht_len hrem (by omega) hl).trans fun _ hs1 =>
          (iter_a2_exact_local hH.memcpy hH.compress256 hpre_s hread_info_s ht_len (by omega) hs1).trans
          fun _ hs2 => iter_b_exact_local hH.memcpy hpre_s hread_info_s ht_len hi hrem hdst hs2)
        (heq379 (hmacNoMemsetExcHooks C.F H s.mem kp379) ▸
          (iter_a1_placed_runsTo (hpre_stripS kp379 hpre_s) ht_len hrem (by omega) hl_strip).trans fun _ hs1 =>
          (iter_a2_exact_local (hmcQ s.mem) (hc256Q s.mem) (hpre_stripS kp379 hpre_s) hread_info_s_q ht_len (by omega) hs1).trans
          fun _ hs2 => iter_b_exact_local (hmcQ s.mem) (hpre_stripS kp379 hpre_s) hread_info_s_q ht_len hi hrem hdst hs2)
        (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status)
        fun sf hvm ⟨hpc, hexp, hlr, hx0, hx1, hx20, hx21, hx22, hx24, hx25, hx26, hx27, hx28, hhm, hokm⟩ => ?_
      rw [hsp0_of, stripS_hmacStN] at hhm; rw [stripS_readBytes] at hokm
      exact ⟨(by cases sf; exact hpc), unstrip_hexpCommon hexp hvm.perm_eq, (by cases sf; exact hlr), (by cases s₀; cases sf; exact hx0),
        (by cases s₀; cases sf; exact hx1), (by cases sf; exact hx20), (by cases s₀; cases sf; exact hx21), (by cases sf; exact hx22),
        (by cases sf; exact hx24), (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27), (by cases s₀; cases sf; exact hx28), hhm, hokm⟩
    exact hc_it.trans_full fun sc hsc hkf_c => iter_fin_vm hMemsetVm (hcl_s.of_keepsFrozen hkf_c) hb hf_s (by omega) hsc
  have unstrip_hpost : ∀ {s sf : State}, VmPreserved s sf →
      HPost C.F salt ikm info okmA okmLen (ProofLib.stripS kp379 (s₀.setMem s.mem)) (ProofLib.stripS kp379 sf) →
      HPost C.F salt ikm info okmA okmLen (s₀.setMem s.mem) sf := by
    intro s sf hvm ⟨hpc, hst, hcs, hokm, hfr⟩
    have hr0 : (ProofLib.stripS kp379 (s₀.setMem s.mem)).readReg64 .x6 = s₀.readReg64 .x6 := by cases s₀; rfl
    have hm0 : (ProofLib.stripS kp379 (s₀.setMem s.mem)).mem = ProofLib.stripExecOutside kp379 s.mem := by cases s₀; rfl
    rw [stripS_readBytes] at hokm; unfold HFrame at hfr; rw [hm0, stripS_mem, hr0, hsp0_of] at hfr
    refine ⟨(by cases s₀; cases sf; exact hpc), (by cases sf; exact hst), ⟨(by cases s₀; cases sf; exact hcs.1), fun r hr => ?_⟩, hokm, unstrip_frame hfr hvm.perm_eq⟩
    have := hcs.2 r hr; cases s₀; cases sf; exact this
  have unstrip_loop : ∀ {okmL i rem dstOff : ℕ} {tP okmSF : List (BitVec 8)} {s sf : State}, VmPreserved s sf →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tP okmSF okmL i rem dstOff (ProofLib.stripS kp379 (s₀.setMem s.mem)) (ProofLib.stripS kp379 sf) →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tP okmSF okmL i rem dstOff (s₀.setMem s.mem) sf := by
    intro _ _ _ _ _ _ s sf hvm ⟨hpc, hexp, hx12, hx21, hx22, hx25, hx26, hx27, hx28, ht508, hokm⟩
    rw [hsp0_of, stripS_readBytes] at ht508; rw [stripS_readBytes] at hokm
    exact ⟨(by cases sf; exact hpc), unstrip_hexpCommon hexp hvm.perm_eq, (by cases sf; exact hx12), (by cases s₀; cases sf; exact hx21),
      (by cases sf; exact hx22), (by cases sf; exact hx25), (by cases sf; exact hx26), (by cases sf; exact hx27), (by cases s₀; cases sf; exact hx28), ht508, hokm⟩
  have stateLoop_reanchor : ∀ {tPrev okmSoFar : List (BitVec 8)} {okmL i rem dstOff : ℕ} {m_old : Memory} {sl : State},
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmL i rem dstOff (s₀.setMem m_old) sl →
      StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmL i rem dstOff (s₀.setMem sl.mem) sl :=
    fun hsl => ⟨hsl.pc_eq, ⟨⟨hsl.exp.common.status, hsl.exp.common.sp_eq, hsl.exp.common.x29_eq,
      hsaved_setMem hsl.exp.common.saved, Frame.refl _ _⟩, hsl.exp.m0_eq, hsl.exp.m8_eq,
      hsl.exp.m16_eq, hsl.exp.m24_eq, hsl.exp.hmac_208⟩, hsl.x12_eq, hsl.x21_eq, hsl.x22_eq,
      hsl.x25_eq, hsl.x26_eq, hsl.x27_eq, hsl.x28_eq, hsl.t_508, hsl.okm_pre⟩
  have stateLoopFin_stripS : ∀ {tPrev okmSoFar : List (BitVec 8)} {okmL i rem dstOff : ℕ} {s_lf : State},
      StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmL i rem dstOff (s₀.setMem s_lf.mem) s_lf →
      StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmL i rem dstOff
        (ProofLib.stripS kp379 (s₀.setMem s_lf.mem)) (ProofLib.stripS kp379 s_lf) := by
    intro _ _ _ _ _ _ s_lf hlf
    exact ⟨(by cases s_lf; exact hlf.pc_eq), stripS_hexpCommon_refl kp379 hlf.exp, (by cases s_lf; exact hlf.x20_eq),
      (by cases s₀; cases s_lf; exact hlf.x21_eq), (by cases s_lf; exact hlf.x22_eq), (by cases s_lf; exact hlf.x24_eq),
      (by cases s_lf; exact hlf.x25_eq), (by cases s_lf; exact hlf.x26_eq), (by cases s_lf; exact hlf.x27_eq),
      (by cases s₀; cases s_lf; exact hlf.x28_eq), by rw [hsp0_of, stripS_readBytes]; exact hlf.t_540, by rw [stripS_readBytes]; exact hlf.okm_pre⟩
  refine hb1_ret.trans_full fun s_b1r ⟨hf_b1r, hs_b1r⟩ hkf_b1r => ?_
  have hcl_b1r := hcl₀.of_keepsFrozen hkf_b1r; have hpre_b1r := hb.at_mem s_b1r.mem hf_b1r
  have hs_b1r_strip : StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen
      (ProofLib.stripS kp379 (s₀.setMem s_b1r.mem)) (ProofLib.stripS kp379 s_b1r) :=
    ⟨(by cases s_b1r; exact hs_b1r.pc_eq), stripS_hexpCommon_refl kp379 hs_b1r.exp,
      (by cases s_b1r; exact hs_b1r.x21_eq), (by cases s_b1r; exact hs_b1r.x22_eq), (by cases s_b1r; exact hs_b1r.x24_eq),
      (by cases s_b1r; exact hs_b1r.x25_eq), (by cases s_b1r; exact hs_b1r.x26_eq), (by cases s₀; cases s_b1r; exact hs_b1r.x28_eq),
      by rw [hsp0_of, stripS_readBytes]; exact hs_b1r.t1_540⟩
  rcases hb.pre.okm_len with rfl | rfl | rfl
  · exact (lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_b1r
      (heq379 H ▸ (seg_b1d_placed_runsTo_exact hH.memcpy hpre_b1r hs_b1r).trans fun _ hs1 => (b1_done_32_placed_runsTo hpre_b1r hs1).trans fun _ hd => epilogue_placed_runsTo hpre_b1r hd)
      (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooks C.F H s_b1r.mem kp379) <|
        (seg_b1d_placed_runsTo_exact (hmcQ s_b1r.mem) (hpre_stripS kp379 hpre_b1r) hs_b1r_strip).trans
        fun _ hs1 => (b1_done_32_placed_runsTo (hpre_stripS kp379 hpre_b1r) hs1).trans fun _ hd => epilogue_placed_runsTo (hpre_stripS kp379 hpre_b1r) hd)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1) fun sf hvm hp => unstrip_hpost hvm hp).mono
      fun sf ⟨hpc, hst, hcs, hokm, hfr⟩ => ⟨hpc, hst, hcs, hokm, hframeS2_step hf_b1r hfr⟩
  · have hl1_vm : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_b1r
        (StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA
          (CryptoVerification.LibsignalTripleRatchet.Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
          (CryptoVerification.LibsignalTripleRatchet.Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info) 64 1 32 32 (s₀.setMem s_b1r.mem)) :=
      lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_b1r
        (heq379 H ▸ (seg_b1d_placed_runsTo_exact hH.memcpy hpre_b1r hs_b1r).trans fun _ hs1 => b1_to_loop_placed_runsTo (Or.inl rfl) hs1)
        (heq379 (hmacNoMemsetExcHooks C.F H s_b1r.mem kp379) ▸ (seg_b1d_placed_runsTo_exact (hmcQ s_b1r.mem) (hpre_stripS kp379 hpre_b1r) hs_b1r_strip).trans fun _ hs1 => b1_to_loop_placed_runsTo (Or.inl rfl) hs1)
        (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status) fun _ hvm h => unstrip_loop hvm h
    refine hl1_vm.trans_full fun sl1 hsl1 hkf_l1 => ?_
    have hcl_l1 := hcl_b1r.of_keepsFrozen hkf_l1; have hf_l1 := hframeS2_step hf_b1r hsl1.exp.common.frame
    refine (hiter_vm hcl_l1 hf_l1 (t1_length _ _ _) (Or.inl rfl) (Or.inl rfl) (by decide) (stateLoop_reanchor hsl1)).trans_full
      fun s_lf1 ⟨hf_lf1, hlf1⟩ hkf_lf1 => ?_
    have hcl_lf1 := hcl_l1.of_keepsFrozen hkf_lf1; have hpre_lf1 := hb.at_mem s_lf1.mem hf_lf1
    have hokm64 := (hkdfExpand_64_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
    exact (lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_lf1
      (runsTo_rebase_of_block379 <| (iter_d_done_exact_local hH.memcpy hpre_lf1 (by decide) rfl hokm64 hlf1).trans fun _ hd => epilogue_placed_runsTo hpre_lf1 hd)
      (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooks C.F H s_lf1.mem kp379) <|
        (iter_d_done_exact_local (hmcQ s_lf1.mem) (hpre_stripS kp379 hpre_lf1) (by decide) rfl hokm64 (stateLoopFin_stripS hlf1)).trans fun _ hd => epilogue_placed_runsTo (hpre_stripS kp379 hpre_lf1) hd)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1) fun sf hvm hp => unstrip_hpost hvm hp).mono
      fun sf ⟨hpc, hst, hcs, hokm, hfr⟩ => ⟨hpc, hst, hcs, hokm, hframeS2_step hf_lf1 hfr⟩
  · have hl1_vm : RunsToVm ((blkPC_379).rebase (blkPl_379).base H) s_b1r
        (StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA
          (CryptoVerification.LibsignalTripleRatchet.Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info)
          (CryptoVerification.LibsignalTripleRatchet.Expand.t1 C.F (hkdfExtractBytes C.F salt ikm) info) 96 1 64 32 (s₀.setMem s_b1r.mem)) :=
      lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_b1r
        (runsTo_rebase_of_block379 <| (seg_b1d_placed_runsTo_exact hH.memcpy hpre_b1r hs_b1r).trans fun _ hs1 => b1_to_loop_placed_runsTo (Or.inr rfl) hs1)
        (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooks C.F H s_b1r.mem kp379) <| (seg_b1d_placed_runsTo_exact (hmcQ s_b1r.mem) (hpre_stripS kp379 hpre_b1r) hs_b1r_strip).trans fun _ hs1 => b1_to_loop_placed_runsTo (Or.inr rfl) hs1)
        (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status) fun _ hvm h => unstrip_loop hvm h
    refine hl1_vm.trans_full fun sl1 hsl1 hkf_l1 => ?_
    have hcl_l1 := hcl_b1r.of_keepsFrozen hkf_l1; have hf_l1 := hframeS2_step hf_b1r hsl1.exp.common.frame
    refine (hiter_vm hcl_l1 hf_l1 (t1_length _ _ _) (Or.inl rfl) (Or.inr rfl) (by decide) (stateLoop_reanchor hsl1)).trans_full
      fun s_lf1 ⟨hf_lf1, hlf1⟩ hkf_lf1 => ?_
    have hcl_lf1 := hcl_l1.of_keepsFrozen hkf_lf1; have hpre_lf1 := hb.at_mem s_lf1.mem hf_lf1
    have hl2_vm := lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_lf1
      (runsTo_rebase_of_block379 <| iter_d_continue_exact_local hH.memcpy hpre_lf1 rfl hlf1)
      (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooks C.F H s_lf1.mem kp379) <| iter_d_continue_exact_local (hmcQ s_lf1.mem) (hpre_stripS kp379 hpre_lf1) rfl (stateLoopFin_stripS hlf1))
      (fun _ hs => hs.exp.common.status) (fun _ hs => hs.exp.common.status) fun _ hvm h => unstrip_loop hvm h
    refine hl2_vm.trans_full fun sl2 hsl2 hkf_l2 => ?_
    have hcl_l2 := hcl_lf1.of_keepsFrozen hkf_l2; have hf_l2 := hframeS2_step hf_lf1 hsl2.exp.common.frame
    refine (hiter_vm hcl_l2 hf_l2 (length_hmacWith _ _ _) (Or.inr rfl) (Or.inl rfl) (by decide) (stateLoop_reanchor hsl2)).trans_full
      fun s_lf2 ⟨hf_lf2, hlf2⟩ hkf_lf2 => ?_
    have hcl_lf2 := hcl_l2.of_keepsFrozen hkf_lf2; have hpre_lf2 := hb.at_mem s_lf2.mem hf_lf2
    have hokm96 := (hkdfExpand_96_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
    exact (lift_block_to_379_vm (Pj := (blkPC_379).rebase (blkPl_379).base H) blkLib_eq_379 blk379_noSvc0 blk379_noMsr (by decide) (by decide) hcl_lf2
      (runsTo_rebase_of_block379 <| (iter_d_done_exact_local hH.memcpy hpre_lf2 (by decide) rfl hokm96 hlf2).trans fun _ hd => epilogue_placed_runsTo hpre_lf2 hd)
      (runsTo_rebase_of_block379 (X := hmacNoMemsetExcHooks C.F H s_lf2.mem kp379) <|
        (iter_d_done_exact_local (hmcQ s_lf2.mem) (hpre_stripS kp379 hpre_lf2) (by decide) rfl hokm96 (stateLoopFin_stripS hlf2)).trans fun _ hd => epilogue_placed_runsTo (hpre_stripS kp379 hpre_lf2) hd)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1) fun sf hvm hp => unstrip_hpost hvm hp).mono
      fun sf ⟨hpc, hst, hcs, hokm, hfr⟩ => ⟨hpc, hst, hcs, hokm, hframeS2_step hf_lf2 hfr⟩

theorem bytesAt_read {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64) (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.readBytes p bs.length = bs := by
  cases ro; · exact ((IsBlock.pointsToBytes p bs).read hsep).2
  · exact (IsBlockRO.pointsToBytesRO p bs hle).read hsep

theorem bytesAt_readable {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64) (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.Readable p bs.length := by
  cases ro
  · intro a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp ((IsBlock.pointsToBytes p bs).permNoLazy_rw hsep ha)
    exact ⟨by rw [hp]; rfl, hlf⟩
  · have hb := IsBlockRO.pointsToBytesRO p bs hle
    exact fun a ha => ⟨hb.perm_r hsep ha, hb.isLazyFree_false hsep ha⟩

theorem bytesAt_outside_rw {ro : Bool} {p b_rw : BitVec 64} {bs : List (BitVec 8)}
    {n_rw : Nat} {Q R : SepProp} {Φ_rw : Memory → Prop} {m : Memory}
    (hle : bs.length ≤ 2 ^ 64) (hrw_pos : 0 < n_rw)
    (hrw : IsBlock Q b_rw n_rw Φ_rw) (hsep : m ⊨ bytesAt ro p bs ∗ (Q ∗ R)) :
    ∀ a, InRegion p bs.length a → OutsideRegion b_rw n_rw a := by
  cases ro
  · intro a ha; have hpos : 0 < bs.length := by unfold InRegion at ha; omega
    have hd := (IsBlock.pointsToBytes p bs).disjoint hrw hpos hrw_pos hsep
    unfold DisjointRegions at hd; unfold InRegion at ha; unfold OutsideRegion; bv_omega
  · exact ro_outside_rw_shared_lb (IsBlockRO.pointsToBytesRO p bs hle) hrw hsep

theorem stackAt_hkdfToSlice (s₀ : State) : stackAt s₀.sp extHookStack =
    memRegion (s₀.sp - 16384#64) 15152 ∗ memRegion (hsp s₀ - 544#64) 1232 := by
  have h1 : stackAt s₀.sp extHookStack = memRegion (s₀.sp - 16384#64) 15152 ∗ stackAt s₀.sp 1232 :=
    ProofLib.stackAt_split_bottom s₀.sp 1232 15152 (by decide)
  have h2 : stackAt s₀.sp 1232 = memRegion (hsp s₀ - 544#64) 1232 := by
    simp only [stackAt, hsp]; congr 1; bv_lin
  rw [h1, h2]

/-- **Block `379` (`spqr::kdf::hkdf_to_slice`, 473 instructions) meets
`withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))`** on
`(blkPC_379).rebase (blkPl_379).base H` under `[HkdfPlacedHooksExactSat C.F H]` and
`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem hkdf_to_slice_spqr_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec) :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  change s0.mem ⊨ (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)).pre x s0 ∗ R at hpre
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 544#64) 1232
  let R_inv : SepProp := bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
    bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗ (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 544#64) 1232 ∗ (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗ (memRegion (hsp s0 - 544#64) 1232 ∗
      (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗ (memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗ (memRegion (hsp s0 - 544#64) 1232 ∗
      (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗ (memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗ (memRegion (hsp s0 - 544#64) 1232 ∗
      (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗ (memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 544#64) 1232 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_placed hro
  have hread_iv : s0.mem.Readable spqrSha256IVAddr 32 := fun a ha =>
    let ⟨hp, hlf⟩ := hro_iv a ha; ⟨by rw [hp]; rfl, hlf⟩
  have hout_salt_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have hb : HPreBase x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0 :=
    { pre :=
        { pc_eq := by rw [hkdfCodeFakeB, BitVec.sub_add_cancel]; exact hpc, status := hrun,
          x0_eq := hx0, x1_eq := hx1, x2_eq := hx2, x3_eq := hx3,
          x4_eq := hx4, x5_eq := hx5, x6_eq := hx6, x7_eq := hx7,
          salt_lt := hsalt_lt, ikm_len := hikm_len, info_ge := hinfo_ge, info_lt := hinfo_lt,
          okm_len := hokm_len, base_al := trivial,
          ro_iv_bytes := by rw [nfs3PlacedFakeB_add_iv]; exact hiv_eq,
          ro_iv_read := by rw [nfs3PlacedFakeB_add_iv]; exact hread_iv,
          disj_iv_stk := by rw [nfs3PlacedFakeB_add_iv]; exact disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk,
          disj_iv_okm := by rw [nfs3PlacedFakeB_add_iv]; exact disjointRegions_of_ro_rw (by decide) hokm_pos hro_iv hrw_okm,
          salt_bytes := bytesAt_read (by omega) hsep_salt_stk,
          ikm_bytes := bytesAt_read (by omega) hsep_ikm_stk,
          info_bytes := bytesAt_read (by omega) hsep_info_stk,
          rw_okm := hrw_okm, rw_stack := hrw_stk,
          disj_okm_stk := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk,
          disj_salt_stk := by
            by_cases h0 : x.salt.length = 0; · exact Or.inl h0
            · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk),
          out_salt_stk := hout_salt_stk,
          out_salt_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm,
          out_ikm_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk,
          out_ikm_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm,
          out_info_stk := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk,
          out_info_okm := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm,
          sp_aligned := by simpa [State.spAligned] using hsp_al },
      read_salt := bytesAt_readable (by omega) hsep_salt_stk,
      read_ikm := bytesAt_readable (by omega) hsep_ikm_stk,
      read_info := bytesAt_readable (by omega) hsep_info_stk }
  intro hL0
  obtain ⟨sf, hsteps_H, hvm, _hacp, htr, hvregs, ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩, _⟩ :=
    hkdf_to_slice_kdf_vm_sat (C := C) hMemsetVm hcl hb hL0
  refine ⟨sf, hsteps_H, Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee (htr := ⟨htr, hvregs⟩)⟩⟩
  dsimp only [withLsCodeRoLoaded, withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hvm, ?_⟩
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec]; dsimp only []; rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]; rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [t1_length, t2_length, t3_length]
  refine ⟨⟨h_exp_len, htr⟩, ?_⟩
  unfold HFrameS2 at hframe_sf; rw [hx6] at hframe_sf; rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    S2Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [stackAt_hkdfToSlice s0]; dsimp only [R_inv] at hpost_sep; ac_nf at hpost_sep ⊢

/-- Any caller block `i < 619` can invoke Block `379` (`spqr::kdf::hkdf_to_slice`) at
`lsmpl.base 379` under `withLsCodeRoLoaded lsmpl` with `VmPreserved`. -/
theorem hkdf_to_slice_spqr_placed_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith C.F)))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_slice_spqr_placed_ok_sat C hMemsetVm) hi

/-- **Block `378` (`spqr::kdf::hkdf_to_vec`) meets `hkdfToVecSpec` under `[HkdfPlacedHooksExactSat C.F H]`.** -/
theorem hkdf_to_vec_spqr_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (hshim : HookSat H spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_378).rebase (blkPl_378).base H) (blkPl_378).base
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))) :=
  hkdf_to_vec_placed_ok M A lim (spqrHkdfWith C.F) hshim hZero
    (hkdf_to_slice_spqr_placed_ok_of_other_block_sat C hMemsetVm)

/-- Any caller block `i < 619` can invoke Block `378` (`spqr::kdf::hkdf_to_vec`) at `lsmpl.base 378`. -/
theorem hkdf_to_vec_spqr_placed_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hMemsetVm : HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec)
    (hshim : HookSat H spqrRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))) :=
  keys_ls_subroutine_ok_of_block_cro
    (hkdf_to_vec_spqr_placed_ok_sat C M A lim hMemsetVm hshim hZero) hi

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat
