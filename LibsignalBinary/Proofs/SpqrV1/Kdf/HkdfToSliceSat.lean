/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGenSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedSat
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpand
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExact
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceLoopExact
import LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSat

/-!
# `HookSat` Placed Contracts for `spqr::kdf::hkdf_to_slice` and `hkdf_to_vec`

Replaces `[HkdfPlacedHooks C.F H]` (`H lsMemsetSym = some memsetHook`) with
`[HkdfPlacedHooksExactSat C.F H]` (`HookSatExactMemcpy H lsMemcpySym` +
`HookSat H lsMemsetSym sessionMemsetRegionSpec`) for placed
`spqr::kdf::hkdf_to_slice` (Block `379`) and `spqr::kdf::hkdf_to_vec` (Block `378`), proving the
**identical** `subroutine_ok` conclusions:
- `hkdf_to_slice_spqr_placed_ok_sat` (`HkdfToSliceOk.lean:654`)
- `hkdf_to_slice_spqr_placed_ok_of_other_block_sat` (`HkdfToSliceOk.lean:804`)
- `hkdf_to_vec_spqr_placed_ok_sat` (`HkdfToSliceOk.lean:815`)
- `hkdf_to_vec_spqr_placed_ok_of_other_block_sat` (`HkdfToSliceOk.lean:827`)
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceSat

open Arm64 ProofLib
open CryptoGames.HKDF (hkdfExpand)
open CryptoGames.HMAC (ShaState hmacWith sha256IV)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded blkPC_378
   blkPC_379 blkPl_378 blkPl_379 blkPl_402 blkPl_425 lsmpl)
open CryptoVerification.LibsignalHmac (shaStateBytes)
open CryptoVerification.LibsignalSpqrV1 (hkdfExtractBytes spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HmacSt RW RunsTo
   TraceEq TraceEq.advancePC_step TraceEq.refl TraceEq.setMem_step TraceEq.setPC_step
   TraceEq.setPState_step TraceEq.writeReg32_step TraceEq.writeReg64_step
   TraceEq.writeVReg128_step extHookStack extract_withLsCodeRoLoaded
   keys_ls_subroutine_ok_of_block_cro length_hmacWith noAllocShimSpec rustAllocZeroedSpec
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Expand (hkdfExpand_64_eq t1_length t2_length t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract (RunsTo.toE RunsToE S2Frame)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.Alloc (spqrHandleErrorSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt hkdfToSliceSpec hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.Kdf
  (FinPre3 FinPre3Pfx FinPre3PfxGen effectiveHmacKey effectiveHmacKey_length_le
   effectiveHmacKey_of_le fin3PlacedFakeB fin3PlacedFakeB_off_0
   hkdfToVecSpec hkdf_to_vec_placed_ok
   hmacWith_effectiveHmacKey spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
  (HCommon HExpCommon HFrame HPost HPre HSaved StateB1Done StateB1Fin StateB1RetFin StateDone
   StateE3cc StateEFin StateENfs1 StateENfs2 StateERet1 StateERet2 StateERetFin StateExtractDone
   StateLoop StateLoopC StateLoopFin b1_done_32_placed_runsTo b1_to_loop_placed_runsTo
   bv_sub_add_lit_ge epilogue_placed_runsTo hkdfCodeFakeB hkdfExpand_32_eq hkdfExpand_96_eq hsp
   hsp_aligned iter_a1_placed_runsTo rodata_sha256IV_placed
   seg_b1a_placed_runsTo seg_e0_placed_runsTo
   seg_e1d_placed_runsTo seg_e2_placed_runsTo seg_e3_placed_runsTo)
open CryptoVerification.SpqrV1.Kdf.NewFromSlice3Proof
  (nfs3PlacedFakeB nfs3PlacedFakeB_add_iv spqrSha256IVAddr)
open LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedGenSat
  (finalize_fixed3_pfx_lt64_placed_runsTo_of_other_block_sat)
open LibsignalBinary.Proofs.SpqrV1.Kdf.FinalizeFixedSat
  (finalize_fixed3_pfx_placed_runsTo_of_other_block_sat
   finalize_fixed3_placed_runsTo_of_other_block_sat)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExpandExact
  (seg_b1b_placed_runsTo_exact seg_b1d_placed_runsTo_exact)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtractExact
  (readable_of_rw seg_e1_placed_runsTo_exact)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceLoopExact
  (iter_a2_placed_runsTo_exact iter_b_placed_runsTo_exact iter_d_continue_placed_runsTo_exact
   iter_d_done_placed_runsTo_exact)
open LibsignalBinary.Proofs.SpqrV1.Kdf.NewFromSliceSat
  (new_from_slice3_gen_placed_runsTo_of_other_block_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)

/-! ## `S2Frame` & Ghost-State Reset (`s₀ ↦ s₀.setMem m`) Helpers -/

@[local simp]
private theorem hsp_setMem (s₀ : State) (m : Memory) : hsp (s₀.setMem m) = hsp s₀ := rfl

private abbrev HFrameS2 (okmLen : ℕ) (s₀ : State) (m : Memory) : Prop :=
  S2Frame s₀.mem m [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 544#64, 1232)]

private structure HPreBase [LibsignalPlacement] (salt ikm info : List (BitVec 8))
    (saltA ikmA infoA okmA : BitVec 64) (okmLen : ℕ) (s₀ : State) : Prop where
  pre       : HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen s₀ nfs3PlacedFakeB True
  read_salt : s₀.mem.Readable saltA salt.length
  read_ikm  : s₀.mem.Readable ikmA ikm.length
  read_info : s₀.mem.Readable infoA info.length

private theorem s2_readable_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {p : BitVec 64} {n : ℕ} (hrd : m₁.Readable p n) :
    m₂.Readable p n :=
  fun a ha => let ⟨hr, hlf⟩ := hrd a ha; hf.2.2 a hr hlf

private theorem s2_readBytes_eq_of_readable {m₁ m₂ : Memory} {regs : List (BitVec 64 × ℕ)}
    (hf : S2Frame m₁ m₂ regs) {p : BitVec 64} {n : ℕ} (hn : n ≤ 2 ^ 64)
    (hrd : m₁.Readable p n)
    (hout : ∀ a, InRegion p n a → ∀ r ∈ regs, OutsideRegion r.1 r.2 a) :
    m₂.readBytes p n = m₁.readBytes p n := by
  refine Memory.readBytes_congr_region hn fun a ha => ?_
  obtain ⟨hr, hlf⟩ := hrd a ha
  exact hf.1 a hr hlf (hout a ha)

private theorem HPreBase.at_mem [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (m : Memory) (hf : HFrameS2 okmLen s₀ m) :
    HPre hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen
      (s₀.setMem m) nfs3PlacedFakeB True := by
  have hokm_le : okmLen ≤ 2 ^ 64 := by have := hb.pre.okm_len; omega
  have hout_pair {p : BitVec 64} {n : ℕ}
      (ho_okm : ∀ a, InRegion p n a → OutsideRegion okmA okmLen a)
      (ho_stk : ∀ a, InRegion p n a → OutsideRegion (hsp s₀ - 544#64) 1232 a) :
      ∀ a, InRegion p n a →
        ∀ r ∈ [(s₀.readReg64 .x6, okmLen), (hsp s₀ - 544#64, 1232)], OutsideRegion r.1 r.2 a := by
    intro a ha r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hb.pre.x6_eq]; exact ho_okm a ha
    · exact ho_stk a ha
  have hiv_read_iv : s₀.mem.Readable spqrSha256IVAddr 32 := by
    have h := hb.pre.ro_iv_read; rwa [nfs3PlacedFakeB_add_iv] at h
  have hiv_bytes_iv : s₀.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV := by
    have h := hb.pre.ro_iv_bytes; rwa [nfs3PlacedFakeB_add_iv] at h
  have hd_iv_okm : DisjointRegions spqrSha256IVAddr 32 okmA okmLen := by
    have h := hb.pre.disj_iv_okm; rwa [nfs3PlacedFakeB_add_iv] at h
  have hd_iv_stk : DisjointRegions spqrSha256IVAddr 32 (hsp s₀ - 544#64) 1232 := by
    have h := hb.pre.disj_iv_stk; rwa [nfs3PlacedFakeB_add_iv] at h
  exact
    { pc_eq         := hb.pre.pc_eq
      status        := hb.pre.status
      x0_eq         := hb.pre.x0_eq
      x1_eq         := hb.pre.x1_eq
      x2_eq         := hb.pre.x2_eq
      x3_eq         := hb.pre.x3_eq
      x4_eq         := hb.pre.x4_eq
      x5_eq         := hb.pre.x5_eq
      x6_eq         := hb.pre.x6_eq
      x7_eq         := hb.pre.x7_eq
      salt_lt       := hb.pre.salt_lt
      ikm_len       := hb.pre.ikm_len
      info_ge       := hb.pre.info_ge
      info_lt       := hb.pre.info_lt
      okm_len       := hb.pre.okm_len
      base_al       := trivial
      ro_iv_bytes   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact (s2_readBytes_eq_of_readable hf (by decide) hiv_read_iv
          (hout_pair (fun a ha => hd_iv_okm.symm.outside ha (by decide))
            (fun a ha => hd_iv_stk.symm.outside ha (by decide)))).trans hiv_bytes_iv
      ro_iv_read    := fun a ha =>
        let ⟨hr, hlf⟩ := hb.pre.ro_iv_read a ha
        hf.2.2 a hr hlf
      disj_iv_stk   := hb.pre.disj_iv_stk
      disj_iv_okm   := hb.pre.disj_iv_okm
      salt_bytes    := (s2_readBytes_eq_of_readable hf (by have := hb.pre.salt_lt; omega)
        hb.read_salt (hout_pair hb.pre.out_salt_okm hb.pre.out_salt_stk)).trans hb.pre.salt_bytes
      ikm_bytes     := (s2_readBytes_eq_of_readable hf (by have := hb.pre.ikm_len; omega)
        hb.read_ikm (hout_pair hb.pre.out_ikm_okm hb.pre.out_ikm_stk)).trans hb.pre.ikm_bytes
      info_bytes    := (s2_readBytes_eq_of_readable hf (by have := hb.pre.info_lt; omega)
        hb.read_info (hout_pair hb.pre.out_info_okm hb.pre.out_info_stk)).trans hb.pre.info_bytes
      rw_okm        := hf.rw_of_rw okmA okmLen hb.pre.rw_okm
      rw_stack      := hf.rw_of_rw (hsp s₀ - 544#64) 1232 hb.pre.rw_stack
      disj_okm_stk  := hb.pre.disj_okm_stk
      disj_salt_stk := hb.pre.disj_salt_stk
      out_salt_stk  := hb.pre.out_salt_stk
      out_salt_okm  := hb.pre.out_salt_okm
      out_ikm_stk   := hb.pre.out_ikm_stk
      out_ikm_okm   := hb.pre.out_ikm_okm
      out_info_stk  := hb.pre.out_info_stk
      out_info_okm  := hb.pre.out_info_okm
      sp_aligned    := hb.pre.sp_aligned }

private theorem hframeS2_step {okmLen : ℕ} {s₀ : State} {m_ref m : Memory}
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hfr : HFrame okmLen (s₀.setMem m_ref) m) :
    HFrameS2 okmLen s₀ m :=
  hf_ref.trans (S2Frame.of_frame hfr)

private theorem hcommon_reset_of_nfs [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA retOff : BitVec 64} {okmLen : ℕ} {s₀ s s' : State} {m_ref : Memory}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hc : HCommon okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + retOff, 0x98), (hsp s₀ - 544#64, 544)])
    (hret : decide (retOff.toNat + 0x98 ≤ 592) = true) :
    HFrameS2 okmLen s₀ s'.mem ∧ HCommon okmLen (s₀.setMem s'.mem) s' := by
  have hret' : retOff.toNat + 0x98 ≤ 592 := of_decide_eq_true hret
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.frame
  have hd_saved : ∀ r ∈ [(hsp s₀ + retOff, (0x98 : ℕ)), (hsp s₀ - 544#64, 544)],
      DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true →
      s'.mem.read64 (hsp s₀ + off) = s.mem.read64 (hsp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_
    exact (hd_saved r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hsaved' : HSaved (s₀.setMem s'.mem) s'.mem :=
    { m592 := (h_saved_eq 592#64 (by decide)).trans h0, m600 := (h_saved_eq 600#64 (by decide)).trans h1
      m608 := (h_saved_eq 608#64 (by decide)).trans h2, m616 := (h_saved_eq 616#64 (by decide)).trans h3
      m624 := (h_saved_eq 624#64 (by decide)).trans h4, m632 := (h_saved_eq 632#64 (by decide)).trans h5
      m640 := (h_saved_eq 640#64 (by decide)).trans h6, m648 := (h_saved_eq 648#64 (by decide)).trans h7
      m656 := (h_saved_eq 656#64 (by decide)).trans h8, m664 := (h_saved_eq 664#64 (by decide)).trans h9
      m672 := (h_saved_eq 672#64 (by decide)).trans h10, m680 := (h_saved_eq 680#64 (by decide)).trans h11 }
  have hf_s' : HFrameS2 okmLen s₀ s'.mem := by
    refine (hframeS2_step hf_ref hc.frame).trans (hfr.mono ?_)
    intro a ha r hr
    have hstack := ha (hsp s₀ - 544#64, 1232) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)
  exact ⟨hf_s', ⟨hstat', hcs.sp_eq.trans hc.sp_eq, (CalleeSaved.x29 hcs).trans hc.x29_eq,
    hsaved', Frame.refl s'.mem _⟩⟩

private theorem hcommon_reset_of_fin [LibsignalPlacement] {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA outOff : BitVec 64} {okmLen : ℕ} {s₀ s s' : State} {m_ref : Memory}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hc : HCommon okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + outOff, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)])
    (hout : decide (outOff.toNat + 32 ≤ 592) = true) :
    HFrameS2 okmLen s₀ s'.mem ∧ HCommon okmLen (s₀.setMem s'.mem) s' := by
  have hout' : outOff.toNat + 32 ≤ 592 := of_decide_eq_true hout
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.frame
  have hd_saved : ∀ r ∈ [(hsp s₀ + outOff, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀ + 592#64) 96 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have h_saved_eq : ∀ (off : BitVec 64),
      decide (592 ≤ off.toNat ∧ off.toNat + 8 ≤ 688) = true →
      s'.mem.read64 (hsp s₀ + off) = s.mem.read64 (hsp s₀ + off) := by
    intro off hoff
    have ⟨h1, h2⟩ := of_decide_eq_true hoff
    refine hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_
    exact (hd_saved r hr).sub_right (hsp s₀ + off) ⟨by decide, by bv_omega⟩
  rcases hc.saved with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have hsaved' : HSaved (s₀.setMem s'.mem) s'.mem :=
    { m592 := (h_saved_eq 592#64 (by decide)).trans h0, m600 := (h_saved_eq 600#64 (by decide)).trans h1
      m608 := (h_saved_eq 608#64 (by decide)).trans h2, m616 := (h_saved_eq 616#64 (by decide)).trans h3
      m624 := (h_saved_eq 624#64 (by decide)).trans h4, m632 := (h_saved_eq 632#64 (by decide)).trans h5
      m640 := (h_saved_eq 640#64 (by decide)).trans h6, m648 := (h_saved_eq 648#64 (by decide)).trans h7
      m656 := (h_saved_eq 656#64 (by decide)).trans h8, m664 := (h_saved_eq 664#64 (by decide)).trans h9
      m672 := (h_saved_eq 672#64 (by decide)).trans h10, m680 := (h_saved_eq 680#64 (by decide)).trans h11 }
  have hf_s' : HFrameS2 okmLen s₀ s'.mem := by
    refine (hframeS2_step hf_ref hc.frame).trans (hfr.mono ?_)
    intro a ha r hr
    have hstack := ha (hsp s₀ - 544#64, 1232) (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold OutsideRegion at *; bv_omega)
  exact ⟨hf_s', ⟨hstat', hcs.sp_eq.trans hc.sp_eq, (CalleeSaved.x29 hcs).trans hc.x29_eq,
    hsaved', Frame.refl s'.mem _⟩⟩

private theorem hexpCommon_reset_of_fin [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {prk salt ikm info : List (BitVec 8)} {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ}
    {s₀ s s' : State} {m_ref : Memory}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hc : HExpCommon F prk info infoA okmLen (s₀.setMem m_ref) s)
    (hstat' : s'.status = .Running)
    (hcs : CalleeSaved s s')
    (hfr : S2Frame s.mem s'.mem [(hsp s₀ + 540#64, 32), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)]) :
    HFrameS2 okmLen s₀ s'.mem ∧ HExpCommon F prk info infoA okmLen (s₀.setMem s'.mem) s' := by
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) (hb.at_mem m_ref hf_ref) hc.common.frame
  have hd_low : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀) 32 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  have hd_208 : ∀ r ∈ [(hsp s₀ + 540#64, (32 : ℕ)), (hsp s₀ + 32#64, 0x90), (hsp s₀ - 144#64, 144)],
      DisjointRegions r.1 r.2 (hsp s₀ + 208#64) 0x90 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  rcases hc.hmac_208 with ⟨hlen, _, hpos, hin, hcnt1, hout, hcnt2⟩
  have hhm' : HmacSt s'.mem (hsp s₀ + 208#64) F prk [] := by
    refine ⟨hlen, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · have hrw63 : s.mem.RW (hsp s₀ + 208#64 + 63#64) 1 := hrw_hsp.sub (by bv_omega)
      obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp
        (hrw63 (hsp s₀ + 208#64 + 63#64) (by simp [InRegion]))
      refine (hfr.1 _ (by rw [hp]; rfl) hlf fun r hr => ?_).trans hpos
      exact (hd_208 r hr).outside (by unfold InRegion; bv_omega) (by decide)
    · refine (hfr.readBytes_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => ?_) (by decide)).trans hin
      exact (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩
    · refine (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_).trans hcnt1
      exact (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩
    · refine (hfr.readBytes_eq (hrw_hsp.sub (by bv_omega)) (fun r hr => ?_) (by decide)).trans hout
      exact (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩
    · refine (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_).trans hcnt2
      exact (hd_208 r hr).sub_right _ ⟨by decide, by bv_omega⟩
  obtain ⟨hf_s', hc'⟩ := hcommon_reset_of_fin (outOff := 540#64) hb hf_ref hc.common hstat' hcs hfr (by decide)
  exact ⟨hf_s',
    { common := hc'
      m0_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 0#64) ⟨by decide, by bv_omega⟩).trans hc.m0_eq
      m8_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 8#64) ⟨by decide, by bv_omega⟩).trans hc.m8_eq
      m16_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 16#64) ⟨by decide, by bv_omega⟩).trans hc.m16_eq
      m24_eq := (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr =>
        (hd_low r hr).sub_right (hsp s₀ + 24#64) ⟨by decide, by bv_omega⟩).trans hc.m24_eq
      hmac_208 := hhm' }⟩

/-! ## Call-Glue Wrappers & Phase `RunsToE` Assembly (Block `379`) -/

section PlacedSat

set_option linter.unusedSectionVars false

variable [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks} [hH : HkdfPlacedHooksExactSat C.F H]

private theorem nfs1_placed_runsTo_sat {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateENfs1 hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen
      (s₀.setMem m_ref) s (lsmpl.base 402)) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      ∃ m_ref', HFrameS2 okmLen s₀ m_ref' ∧
        StateERet1 hkdfCodeFakeB C.F salt ikm info ikmA infoA okmA okmLen (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hx2_nat : (s.readReg64 .x2).toNat = salt.length := by
    rw [hx.x2_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hb.pre.salt_lt; omega)]
  have hiv_bytes : s.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV := by
    rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_bytes hpre_ref hx.common.frame
  have hiv_read : s.mem.Readable spqrSha256IVAddr 32 := by
    rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_read hpre_ref hx.common.frame
  have hiv_disj : DisjointRegions spqrSha256IVAddr 32 (s.sp - 544#64) 544 := by
    rw [← nfs3PlacedFakeB_add_iv, hx.common.sp_eq, hsp_setMem]
    exact hb.pre.disj_iv_stk.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  refine (new_from_slice3_gen_placed_runsTo_of_other_block_sat C H hcl hx.pc_eq hx.common.status
    (by rw [hx2_nat]; exact hb.pre.salt_lt) hiv_bytes hiv_read hiv_disj
    (by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega))
    (by rw [hx.common.sp_eq]; exact HFrame.rw_sub_544 hpre_ref hx.common.frame)
    (by rw [hx.x0_eq, hx.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
    (by rw [hx.x1_eq, hx2_nat]
        exact (Frame.readable_iff hx.common.frame _ _).mpr
          (s2_readable_of_readable hf_ref hb.read_salt))
    (by rw [hx.x1_eq, hx2_nat, hx.common.sp_eq, hsp_setMem]
        exact hb.pre.disj_salt_stk.imp id (fun hd => hd.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩))
    (by rw [hx.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)).mono
    fun s' ⟨hpc', hrun', hcs, htag, hhm, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem] at htag
  have hx0_8 : s.readReg64 .x0 + 8#64 = hsp s₀ + 40#64 := by rw [hx.x0_eq, hsp_setMem]; bv_lin
  have hsalt_s : s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat = salt := by
    rw [hx.x1_eq, hx2_nat]; exact HFrame.salt_bytes hpre_ref hx.common.frame
  rw [hx0_8, hsalt_s] at hhm; rw [hx.x0_eq, hx.common.sp_eq, hsp_setMem] at hfr
  obtain ⟨hf_s', hc'⟩ := hcommon_reset_of_nfs (retOff := 32#64) hb hf_ref hx.common hrun' hcs hfr (by decide)
  exact ⟨s'.mem, hf_s', ⟨hpc', hc',
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x27 hcs).trans hx.x27_eq, htag, hhm⟩⟩

private theorem fin_extract_placed_runsTo_sat {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateEFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      ∃ m_ref', HFrameS2 okmLen s₀ m_ref' ∧
        StateERetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  rcases hx.hmac_32 with ⟨pfx, tail, hpt, hmod, hlt, hhm⟩
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hfin_pre : FinPre3PfxGen fin3PlacedFakeB C.F (effectiveHmacKey C.F salt) pfx tail s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.common.status,
      key_le := effectiveHmacKey_length_le C.F salt, tail_lt := hlt,
      hmac_st := by rw [hx.x1_eq]; exact hhm,
      rw_out := by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1 }
  refine (finalize_fixed3_pfx_lt64_placed_runsTo_of_other_block_sat (C := C) (H := H)
    hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem, hpt, hmacWith_effectiveHmacKey] at hout
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq, hsp_setMem] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  obtain ⟨hf_s', hc'⟩ := hcommon_reset_of_fin (outOff := 507#64) hb hf_ref hx.common hrun' hcs hfr (by decide)
  exact ⟨s'.mem, hf_s', ⟨hpc', hc',
    (CalleeSaved.x19 hcs).trans hx.x19_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, hm16', hout⟩⟩

private theorem nfs2_placed_runsTo_sat {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateENfs2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref) s (blkPl_402).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      ∃ m_ref', HFrameS2 okmLen s₀ m_ref' ∧
        StateERet2 hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hx2_nat : (s.readReg64 .x2).toNat = 32 := by rw [hx.x2_eq]; rfl
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.common.frame
  have hiv_bytes : s.mem.readBytes spqrSha256IVAddr 32 = shaStateBytes sha256IV := by
    rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_bytes hpre_ref hx.common.frame
  have hiv_read : s.mem.Readable spqrSha256IVAddr 32 := by
    rw [← nfs3PlacedFakeB_add_iv]; exact HFrame.ro_iv_read hpre_ref hx.common.frame
  have hiv_disj : DisjointRegions spqrSha256IVAddr 32 (s.sp - 544#64) 544 := by
    rw [← nfs3PlacedFakeB_add_iv, hx.common.sp_eq, hsp_setMem]
    exact hb.pre.disj_iv_stk.sub_right (hsp s₀ - 544#64) ⟨by decide, by bv_omega⟩
  refine (new_from_slice3_gen_placed_runsTo_of_other_block_sat C H hcl hx.pc_eq hx.common.status
    (by rw [hx2_nat]; decide) hiv_bytes hiv_read hiv_disj
    (by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega))
    (by rw [hx.common.sp_eq]; exact HFrame.rw_sub_544 hpre_ref hx.common.frame)
    (by rw [hx.x0_eq, hx.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega)
    (by rw [hx.x1_eq, hx2_nat, hsp_setMem]; exact readable_of_rw (hrw_hsp.sub (by bv_omega)))
    (by rw [hx.x1_eq, hx2_nat, hx.common.sp_eq, hsp_setMem]; exact Or.inr (by unfold DisjointRegions; bv_omega))
    (by rw [hx.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1)).mono
    fun s' ⟨hpc', hrun', hcs, htag, hhm, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem] at htag
  have hx0_8 : s.readReg64 .x0 + 8#64 = hsp s₀ + 360#64 := by rw [hx.x0_eq, hsp_setMem]; bv_lin
  have hprk_s : s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat =
      hkdfExtractBytes C.F salt ikm := by
    rw [hx.x1_eq, hx2_nat]; exact hx.prk_507
  rw [hx0_8, hprk_s, effectiveHmacKey_of_le C.F (by rw [hkdfExtractBytes, length_hmacWith]; decide)] at hhm
  rw [hx.x0_eq, hx.common.sp_eq, hsp_setMem] at hfr
  have hm16' : s'.mem.read64 (hsp s₀ + 16#64) = BitVec.ofNat 64 info.length := by
    refine (hfr.read64_eq (hrw_hsp.sub (by bv_omega)) fun r hr => ?_).trans hx.m16_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (unfold DisjointRegions; bv_omega)
  obtain ⟨hf_s', hc'⟩ := hcommon_reset_of_nfs (retOff := 352#64) hb hf_ref hx.common hrun' hcs hfr (by decide)
  exact ⟨s'.mem, hf_s', ⟨hpc', hc',
    (CalleeSaved.x19 hcs).trans hx.x19_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, hm16', htag, hhm⟩⟩

private theorem fin_b1_placed_runsTo_sat {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateB1Fin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      ∃ m_ref', HFrameS2 okmLen s₀ m_ref' ∧
        StateB1RetFin hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hfin_pre : FinPre3 fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm) (info ++ [1#8]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.exp.common.status,
      key_le := by rw [hkdfExtractBytes, length_hmacWith]; decide,
      msg_lt := by have := hb.pre.info_lt; simp; omega,
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32,
      rw_out := by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.exp.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.exp.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1 }
  refine (finalize_fixed3_placed_runsTo_of_other_block_sat (C := C) (H := H)
    hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem] at hfr
  obtain ⟨hf_s', hexp'⟩ := hexpCommon_reset_of_fin hb hf_ref hx.exp hrun' hcs hfr
  exact ⟨s'.mem, hf_s', ⟨hpc', hexp',
    (CalleeSaved.x21 hcs).trans hx.x21_eq, (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x24 hcs).trans hx.x24_eq, (CalleeSaved.x25 hcs).trans hx.x25_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, ht1⟩⟩

private theorem iter_fin_placed_runsTo_sat {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hdst : dstOff ≤ okmLen)
    (hx : StateLoopC hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff
      (s₀.setMem m_ref) s (blkPl_425).base) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      ∃ m_ref', HFrameS2 okmLen s₀ m_ref' ∧
        StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff
          (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hrw_hsp : s.mem.RW (hsp s₀) 688 := HFrame.rw_hsp (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_sub : s.mem.RW (hsp s₀ - 544#64) 544 := HFrame.rw_sub_544 (s₀ := s₀.setMem m_ref) hpre_ref hx.exp.common.frame
  have hrw_okm : s.mem.RW okmA okmLen := HFrame.rw_okm hpre_ref hx.exp.common.frame
  have hfin_pre : FinPre3Pfx fin3PlacedFakeB C.F (hkdfExtractBytes C.F salt ikm)
      (tPrev ++ info.take 32) (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [fin3PlacedFakeB_off_0]; exact hx.pc_eq, status := hx.exp.common.status,
      key_le := by rw [hkdfExtractBytes, length_hmacWith]; decide,
      tail_lt := by have := hb.pre.info_lt; simp; omega,
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_32,
      rw_out := by rw [hx.x0_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_hm := by rw [hx.x1_eq, hsp_setMem]; exact hrw_hsp.sub (by bv_omega),
      rw_fsp := by rw [hx.exp.common.sp_eq, hsp_setMem]; exact hrw_sub.sub (by bv_omega),
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_out_fsp := by rw [hx.x0_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      disj_hm_fsp := by rw [hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem]; unfold DisjointRegions; bv_omega,
      sp_aligned := by rw [hx.exp.common.sp_eq, hsp_setMem]; exact (hsp_aligned hb.pre.sp_aligned).2.1 }
  refine (finalize_fixed3_pfx_placed_runsTo_of_other_block_sat (C := C) (H := H)
    hcl hfin_pre).mono fun s' ⟨hpc', hrun', hcs, hout, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'; rw [hx.x0_eq, hsp_setMem] at hout; rw [hx.x0_eq, hx.x1_eq, hx.exp.common.sp_eq, hsp_setMem] at hfr
  have hmsg_eq : (tPrev ++ info.take 32) ++ (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) =
      tPrev ++ info ++ [BitVec.ofNat 8 (i + 1)] := by
    rw [List.append_assoc tPrev (info.take 32), ← List.append_assoc (info.take 32),
        List.take_append_drop, ← List.append_assoc]
  rw [hmsg_eq] at hout
  have hokm' : s'.mem.readBytes okmA dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · have hokm_len := hb.pre.okm_len
      refine (hfr.readBytes_eq (hrw_okm.sub (by bv_omega)) (fun r hr => ?_) (by omega)).trans hx.okm_pre
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> dsimp only
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ + 540#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ + 32#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
      · exact (hb.pre.disj_okm_stk.symm.sub_left (hsp s₀ - 144#64) ⟨by decide, by bv_omega⟩).sub_right okmA ⟨by omega, by bv_omega⟩
  obtain ⟨hf_s', hexp'⟩ := hexpCommon_reset_of_fin hb hf_ref hx.exp hrun' hcs hfr
  exact ⟨s'.mem, hf_s', ⟨hpc', hexp',
    (CalleeSaved.x20 hcs).trans hx.x20_eq, (CalleeSaved.x21 hcs).trans hx.x21_eq,
    (CalleeSaved.x22 hcs).trans hx.x22_eq, (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x25 hcs).trans hx.x25_eq, (CalleeSaved.x26 hcs).trans hx.x26_eq,
    (CalleeSaved.x27 hcs).trans hx.x27_eq, (CalleeSaved.x28 hcs).trans hx.x28_eq, hout, hokm'⟩⟩

private theorem block1_phase_placed_runsToE_sat {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsToE ((blkPC_379).rebase (blkPl_379).base H) s₀ fun s =>
      ∃ m_ref, HFrameS2 okmLen s₀ m_ref ∧
        StateB1Done hkdfCodeFakeB C.F salt ikm info infoA okmA okmLen (s₀.setMem m_ref) s := by
  have hs_id : s₀.setMem s₀.mem = s₀ := by cases s₀; rfl
  have hf₀ : HFrameS2 okmLen s₀ s₀.mem := S2Frame.refl s₀.mem _
  have h0 : RunsToE ((blkPC_379).rebase (blkPl_379).base H) s₀
      (StateENfs1 hkdfCodeFakeB salt ikm info saltA ikmA infoA okmA okmLen
        (s₀.setMem s₀.mem) · (lsmpl.base 402)) := by
    rw [hs_id]; exact RunsTo.toE (seg_e0_placed_runsTo hb.pre)
  have h1 := RunsToE.trans_full h0 fun s hs hkf _ =>
    RunsTo.toE (nfs1_placed_runsTo_sat (C := C) (hcl₀.of_keepsFrozen hkf) hb hf₀ hs)
  have h2 := h1.trans fun s ⟨m1, hf1, hs1⟩ =>
    RunsTo.toE ((seg_e1_placed_runsTo_exact hH.memcpy hH.compress256 (hb.at_mem m1 hf1)
      (s2_readable_of_readable hf1 hb.read_ikm) hs1).trans
      fun s2 hs2 => (seg_e1d_placed_runsTo (hb.at_mem m1 hf1) hs2).mono fun s3 hs3 =>
        Exists.intro m1 (And.intro hf1 hs3))
  have h3 := RunsToE.trans_full h2 fun s ⟨m1, hf1, hs3⟩ hkf _ =>
    RunsTo.toE (fin_extract_placed_runsTo_sat (hcl₀.of_keepsFrozen hkf) hb hf1 hs3)
  have h4 := h3.trans fun s ⟨m2, hf2, hs4⟩ =>
    RunsTo.toE ((seg_e2_placed_runsTo (hb.at_mem m2 hf2) hs4).mono fun s5 hs5 =>
      Exists.intro m2 (And.intro hf2 hs5))
  have h5 := RunsToE.trans_full h4 fun s ⟨m2, hf2, hs5⟩ hkf _ =>
    RunsTo.toE (nfs2_placed_runsTo_sat (hcl₀.of_keepsFrozen hkf) hb hf2 hs5)
  have h6 := h5.trans fun s ⟨m3, hf3, hs6⟩ =>
    RunsTo.toE ((seg_e3_placed_runsTo (hb.at_mem m3 hf3) hs6).trans fun s7 hs7 =>
      (seg_b1a_placed_runsTo (hb.at_mem m3 hf3) hs7).trans fun s8 hs8 =>
      (seg_b1b_placed_runsTo_exact hH.memcpy (hb.at_mem m3 hf3)
        (s2_readable_of_readable hf3 hb.read_info) hs8).mono fun s9 hs9 =>
        Exists.intro m3 (And.intro hf3 hs9))
  have h7 := RunsToE.trans_full h6 fun s ⟨m3, hf3, hs9⟩ hkf _ =>
    RunsTo.toE (fin_b1_placed_runsTo_sat (hcl₀.of_keepsFrozen hkf) hb hf3 hs9)
  exact h7.trans fun s ⟨m4, hf4, hs10⟩ =>
    RunsTo.toE ((seg_b1d_placed_runsTo_exact hH.memcpy (hb.at_mem m4 hf4) hs10).mono fun s11 hs11 =>
      ⟨m4, hf4, hs11⟩)

private theorem iter_step_placed_runsTo_sat {salt ikm info tPrev okmSoFar : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen i rem dstOff : ℕ} {s₀ s : State} {m_ref : Memory}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hkf_s : s₀.mem.KeepsFrozen s.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (ht_len : tPrev.length = 32) (hi : i = 1 ∨ i = 2) (hrem : rem = 32 ∨ rem = 64)
    (hdst : dstOff + 32 ≤ okmLen)
    (hx : StateLoop hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff
      (s₀.setMem m_ref) s) :
    RunsToE ((blkPC_379).rebase (blkPl_379).base H) s fun s' =>
      ∃ m_ref', HFrameS2 okmLen s₀ m_ref' ∧
        StateLoopFin hkdfCodeFakeB C.F salt ikm info infoA okmA tPrev okmSoFar okmLen i rem dstOff
          (s₀.setMem m_ref') s' := by
  have hpre_ref := hb.at_mem m_ref hf_ref
  have hpre_fin := RunsTo.toE
    ((iter_a1_placed_runsTo hpre_ref ht_len hrem (by omega) hx).trans fun _ hs1 =>
     (iter_a2_placed_runsTo_exact hH.memcpy hH.compress256 hpre_ref
       (s2_readable_of_readable hf_ref hb.read_info) ht_len (by omega) hs1).trans fun _ hs2 =>
     iter_b_placed_runsTo_exact hH.memcpy hpre_ref
       (s2_readable_of_readable hf_ref hb.read_info) ht_len hi hrem hdst hs2)
  exact RunsToE.trans_full hpre_fin fun s3 hs3 hkf3 _ =>
    RunsTo.toE (iter_fin_placed_runsTo_sat
      (hcl₀.of_keepsFrozen (Memory.KeepsFrozen.trans hkf_s hkf3)) hb hf_ref (by omega) hs3)

private theorem epilogue_placed_runsTo_sat {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ s : State} {m_ref : Memory}
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀)
    (hf_ref : HFrameS2 okmLen s₀ m_ref)
    (hx : StateDone hkdfCodeFakeB C.F salt ikm info okmA okmLen (s₀.setMem m_ref) s) :
    RunsTo ((blkPC_379).rebase (blkPl_379).base H) s fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes okmA okmLen = hkdfExpand C.F (hkdfExtractBytes C.F salt ikm) info okmLen ∧
      HFrameS2 okmLen s₀ sf.mem :=
  (epilogue_placed_runsTo (hb.at_mem m_ref hf_ref) hx).mono fun _ ⟨hpc, hstat, hcs, hokm, hfr⟩ =>
    ⟨hpc, hstat, hcs, hokm, hframeS2_step hf_ref hfr⟩

private theorem hkdf_to_slice_placed_runsToE_sat {salt ikm info : List (BitVec 8)}
    {saltA ikmA infoA okmA : BitVec 64} {okmLen : ℕ} {s₀ : State}
    (hcl₀ : LibsignalCodeLoaded lsmpl s₀.mem)
    (hb : HPreBase salt ikm info saltA ikmA infoA okmA okmLen s₀) :
    RunsToE ((blkPC_379).rebase (blkPl_379).base H) s₀ fun sf =>
      sf.pc = s₀.readReg64 .lr ∧
      sf.status = .Running ∧
      CalleeSaved s₀ sf ∧
      sf.mem.readBytes okmA okmLen = hkdfExpand C.F (hkdfExtractBytes C.F salt ikm) info okmLen ∧
      HFrameS2 okmLen s₀ sf.mem := by
  refine RunsToE.trans_full (block1_phase_placed_runsToE_sat (C := C) hcl₀ hb) fun s₁ ⟨m1, hf1, hs₁⟩ hkf1 _ => ?_
  rcases hb.pre.okm_len with rfl | rfl | rfl
  · exact RunsTo.toE ((b1_done_32_placed_runsTo (hb.at_mem m1 hf1) hs₁).trans fun _ hdone =>
      epilogue_placed_runsTo_sat hb hf1 hdone)
  · have hloop1 := RunsTo.toE (b1_to_loop_placed_runsTo (H := H) (Or.inl rfl) hs₁)
    have hfin1 := RunsToE.trans_full hloop1 fun s_l1 hl1 hkf_l1 _ =>
      iter_step_placed_runsTo_sat hcl₀ (Memory.KeepsFrozen.trans hkf1 hkf_l1) hb hf1
        (t1_length _ _ _) (Or.inl rfl) (Or.inl rfl) (by decide) hl1
    refine hfin1.trans fun _ ⟨m2, hf2, hfin1'⟩ => ?_
    have hokm64 := (hkdfExpand_64_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
    exact RunsTo.toE ((iter_d_done_placed_runsTo_exact hH.memcpy (hb.at_mem m2 hf2)
      (by decide) rfl hokm64 hfin1').trans fun _ hdone => epilogue_placed_runsTo_sat hb hf2 hdone)
  · have hloop1 := RunsTo.toE (b1_to_loop_placed_runsTo (H := H) (Or.inr rfl) hs₁)
    have hfin1 := RunsToE.trans_full hloop1 fun s_l1 hl1 hkf_l1 _ =>
      iter_step_placed_runsTo_sat hcl₀ (Memory.KeepsFrozen.trans hkf1 hkf_l1) hb hf1
        (t1_length _ _ _) (Or.inl rfl) (Or.inr rfl) (by decide) hl1
    have hloop2 := hfin1.trans fun _ ⟨m2, hf2, hfin1'⟩ =>
      RunsTo.toE ((iter_d_continue_placed_runsTo_exact hH.memcpy (hb.at_mem m2 hf2) rfl hfin1').mono
        fun _ hl2 => Exists.intro m2 (And.intro hf2 hl2))
    have hfin2 := RunsToE.trans_full hloop2 fun s_l2 ⟨m2, hf2, hl2⟩ hkf_l2 _ =>
      iter_step_placed_runsTo_sat hcl₀ (Memory.KeepsFrozen.trans hkf1 hkf_l2) hb hf2
        (length_hmacWith _ _ _) (Or.inr rfl) (Or.inl rfl) (by decide) hl2
    refine hfin2.trans fun _ ⟨m3, hf3, hfin2'⟩ => ?_
    have hokm96 := (hkdfExpand_96_eq C.F (hkdfExtractBytes C.F salt ikm) info).symm
    exact RunsTo.toE ((iter_d_done_placed_runsTo_exact hH.memcpy (hb.at_mem m3 hf3)
      (by decide) rfl hokm96 hfin2').trans fun _ hdone => epilogue_placed_runsTo_sat hb hf3 hdone)

end PlacedSat

/-! ## Separation-Logic Bridges (`hkdf_to_slice_spqr_placed_ok_sat`, `hkdf_to_vec_spqr_placed_ok_sat`) -/

private theorem ro_outside_rw {P Q R : SepProp} {b_ro b_rw : BitVec 64} {n_ro n_rw : ℕ}
    {Φ_ro Φ_rw : Memory → Prop} {m : Memory}
    (hro : IsBlockRO P b_ro n_ro Φ_ro)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ P ∗ (Q ∗ R)) :
    ∀ a, InRegion b_ro n_ro a → OutsideRegion b_rw n_rw a := by
  intro a ha_ro
  rw [outsideRegion_iff_not_inRegion]
  intro ha_rw
  have hQPR : m ⊨ Q ∗ (P ∗ R) := by rwa [sepConj_left_comm]
  have hperm : m.perm a = some Perm.rw := hrw.perm_rw hQPR ha_rw
  have hm_reg : m ⊨ memRegion b_rw n_rw ∗ (P ∗ R) :=
    hrw.update (IsBlock.memRegion b_rw n_rw) (Nat.le_refl _) hQPR
      (AgreesOutside.rfl' m b_rw n_rw) trivial
  have hm_lf := Satisfies.madvFreeNonFrozen hm_reg
  rw [sepConj_left_comm] at hm_lf
  have hfalse := hro.isLazyFree_false hm_lf ha_ro
  rw [Memory.isLazyFree_madvFreeNonFrozen] at hfalse
  have hin : (a - b_rw).toNat < n_rw := ha_rw
  have hcond : ((some Perm.rw).mapped && !(some Perm.rw).frozen) = true := rfl
  simp only [hin, hperm, decide_true, Bool.true_and, hcond, ↓reduceIte] at hfalse
  cases hfalse

private theorem bytesAt_read {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64)
    (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.readBytes p bs.length = bs := by
  cases ro
  · exact ((IsBlock.pointsToBytes p bs).read hsep).2
  · exact (IsBlockRO.pointsToBytesRO p bs hle).read hsep

private theorem bytesAt_readable {ro : Bool} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hle : bs.length ≤ 2 ^ 64)
    (hsep : m ⊨ bytesAt ro p bs ∗ R) :
    m.Readable p bs.length := by
  cases ro
  · exact fun a ha => by
      have hp := (IsBlock.pointsToBytes p bs).permNoLazy_rw hsep ha
      obtain ⟨hrw, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hp
      exact ⟨by rw [hrw]; rfl, hlf⟩
  · have hb := IsBlockRO.pointsToBytesRO p bs hle
    exact fun a ha => ⟨hb.perm_r hsep ha, hb.isLazyFree_false hsep ha⟩

private theorem disjointRegions_of_outside {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hout : ∀ a, InRegion b₁ n₁ a → OutsideRegion b₂ n₂ a) :
    DisjointRegions b₁ n₁ b₂ n₂ := by
  have hdisj : ∀ a, ¬ (InRegion b₁ n₁ a ∧ InRegion b₂ n₂ a) := by
    intro a ⟨h1, h2⟩
    have h_out := hout a h1
    rw [outsideRegion_iff_not_inRegion] at h_out
    exact h_out h2
  constructor
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₂ ⟨by simp only [InRegion]; omega,
      by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  · apply Classical.byContradiction; intro hlt
    exact hdisj b₁ ⟨by simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega,
      by simp only [InRegion]; omega⟩

private theorem disjointRegions_of_ro_rw {m : Memory} {b₁ b₂ : BitVec 64} {n₁ n₂ : Nat}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hro : m.RO b₁ n₁) (hrw : m.RW b₂ n₂) :
    DisjointRegions b₁ n₁ b₂ n₂ :=
  disjointRegions_of_outside hn₁ hn₂ fun a ha₁ => by
    rw [outsideRegion_iff_not_inRegion]; intro ha₂
    have h1 := (hro a ha₁).1
    have h2 := (Memory.permNoLazy_eq_some_rw_iff.mp (hrw a ha₂)).1
    rw [h1] at h2; cases h2

private theorem bytesAt_outside_rw {ro : Bool} {p b_rw : BitVec 64} {bs : List (BitVec 8)}
    {n_rw : ℕ} {Q R : SepProp} {Φ_rw : Memory → Prop} {m : Memory}
    (hle : bs.length ≤ 2 ^ 64) (hrw_pos : 0 < n_rw)
    (hrw : IsBlock Q b_rw n_rw Φ_rw)
    (hsep : m ⊨ bytesAt ro p bs ∗ (Q ∗ R)) :
    ∀ a, InRegion p bs.length a → OutsideRegion b_rw n_rw a := by
  cases ro
  · intro a ha
    have hpos : 0 < bs.length := by unfold InRegion at ha; omega
    have hd := (IsBlock.pointsToBytes p bs).disjoint hrw hpos hrw_pos hsep
    unfold DisjointRegions at hd
    unfold InRegion at ha
    unfold OutsideRegion
    bv_omega
  · exact ro_outside_rw (IsBlockRO.pointsToBytesRO p bs hle) hrw hsep

private theorem stackAt_hkdfToSlice (s₀ : State) :
    stackAt s₀.sp extHookStack =
      memRegion (s₀.sp - 16384#64) 15152 ∗ memRegion (hsp s₀ - 544#64) 1232 := by
  have h1 : stackAt s₀.sp extHookStack =
      memRegion (s₀.sp - 16384#64) 15152 ∗ stackAt s₀.sp 1232 :=
    ProofLib.stackAt_split_bottom s₀.sp 1232 15152 (by decide)
  have h2 : stackAt s₀.sp 1232 = memRegion (hsp s₀ - 544#64) 1232 := by
    simp only [stackAt, hsp]
    congr 1
    bv_lin
  rw [h1, h2]

/-- Block `379` (`spqr::kdf::hkdf_to_slice`) meets `withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith C.F))` under `[HkdfPlacedHooksExactSat C.F H]`. -/
theorem hkdf_to_slice_spqr_placed_ok_sat [LibsignalPlacement] (C : Crypto)
    {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H] :
    subroutine_ok ((blkPC_379).rebase (blkPl_379).base H) (blkPl_379).base
      (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith C.F))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre hsp_al => ?_
  obtain ⟨⟨hcl, hro⟩, hpre⟩ := extract_withLsCodeRoLoaded hpre
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    hsalt_lt, hikm_len, hinfo_ge, hinfo_lt, hokm_len⟩, hsep⟩
  rw [stackAt_hkdfToSlice s0] at hsep
  have hb_okm := IsBlock.memRegion x.okmA x.okmLen
  have hb_stk := IsBlock.memRegion (hsp s0 - 544#64) 1232
  let R_inv : SepProp :=
    bytesAt x.saltRO x.saltA x.salt ∗
      bytesAt x.ikmRO x.ikmA x.ikm ∗
      bytesAt x.infoRO x.infoA x.info ∗
      memRegion (s0.sp - 16384#64) 15152 ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA x.okmLen ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (hsp s0 - 544#64) 1232 ∗
      (memRegion x.okmA x.okmLen ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_salt_stk : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.ikmRO x.ikmA x.ikm ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_salt_okm : s0.mem ⊨ bytesAt x.saltRO x.saltA x.salt ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.infoRO x.infoA x.info ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_okm : s0.mem ⊨ bytesAt x.ikmRO x.ikmA x.ikm ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.infoRO x.infoA x.info ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗
        (bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
          memRegion x.okmA x.okmLen ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ bytesAt x.infoRO x.infoA x.info ∗
      (memRegion x.okmA x.okmLen ∗
        (memRegion (hsp s0 - 544#64) 1232 ∗ bytesAt x.saltRO x.saltA x.salt ∗
          bytesAt x.ikmRO x.ikmA x.ikm ∗ memRegion (s0.sp - 16384#64) 15152 ∗ R)) := by
    ac_nf at hsep ⊢
  have hokm_pos : 0 < x.okmLen := by omega
  have hokm_le : x.okmLen ≤ 2 ^ 64 := by omega
  have hrw_okm : s0.mem.RW x.okmA x.okmLen := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (hsp s0 - 544#64) 1232 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_sha256IV_placed hro
  have hread_iv : s0.mem.Readable (nfs3PlacedFakeB + bv% (ls_bytes% "0000000000000000000000000000000000000000000000000000000000000000456e63617073756c6174696f6e206b6579204d414320697320696e76616c6964" + 64)) 32 := by
    rw [nfs3PlacedFakeB_add_iv]
    exact fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hout_salt_stk : ∀ a, InRegion x.saltA x.salt.length a →
      OutsideRegion (hsp s0 - 544#64) 1232 a :=
    bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_salt_stk
  have h_hpre : HPre hkdfCodeFakeB x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0
      nfs3PlacedFakeB True :=
    { pc_eq         := by
        rw [hkdfCodeFakeB, bv_sub_add_lit_ge _ (384652 : Nat) (384652 : Nat) (by decide)]
        simpa using hpc
      status        := hrun
      x0_eq         := hx0
      x1_eq         := hx1
      x2_eq         := hx2
      x3_eq         := hx3
      x4_eq         := hx4
      x5_eq         := hx5
      x6_eq         := hx6
      x7_eq         := hx7
      salt_lt       := hsalt_lt
      ikm_len       := hikm_len
      info_ge       := hinfo_ge
      info_lt       := hinfo_lt
      okm_len       := hokm_len
      base_al       := trivial
      ro_iv_bytes   := by rw [nfs3PlacedFakeB_add_iv]; exact hiv_eq
      ro_iv_read    := hread_iv
      disj_iv_stk   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
      disj_iv_okm   := by
        rw [nfs3PlacedFakeB_add_iv]
        exact disjointRegions_of_ro_rw (by decide) hokm_pos hro_iv hrw_okm
      salt_bytes    := bytesAt_read (by omega) hsep_salt_stk
      ikm_bytes     := bytesAt_read (by omega) hsep_ikm_stk
      info_bytes    := bytesAt_read (by omega) hsep_info_stk
      rw_okm        := hrw_okm
      rw_stack      := hrw_stk
      disj_okm_stk  := hb_okm.disjoint hb_stk hokm_pos (by decide) hsep_okm_stk
      disj_salt_stk := by
        by_cases h0 : x.salt.length = 0
        · exact Or.inl h0
        · exact Or.inr (disjointRegions_of_outside (by omega) (by decide) hout_salt_stk)
      out_salt_stk  := hout_salt_stk
      out_salt_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_salt_okm
      out_ikm_stk   := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_ikm_stk
      out_ikm_okm   := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_ikm_okm
      out_info_stk  := bytesAt_outside_rw (by omega) (by decide) hb_stk hsep_info_stk
      out_info_okm  := bytesAt_outside_rw (by omega) hokm_pos hb_okm hsep_info_okm
      sp_aligned    := by simpa [State.spAligned] using hsp_al }
  have hb_base : HPreBase x.salt x.ikm x.info x.saltA x.ikmA x.infoA x.okmA x.okmLen s0 :=
    { pre       := h_hpre
      read_salt := bytesAt_readable (by omega) hsep_salt_stk
      read_ikm  := bytesAt_readable (by omega) hsep_ikm_stk
      read_info := bytesAt_readable (by omega) hsep_info_stk }
  refine (hkdf_to_slice_placed_runsToE_sat (C := C) (H := H) hcl hb_base).to_reaches_pc
    fun sf hpost _ _ htr => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [withLsCodeRoLoaded]
  rw [hkdfToSliceSpqrSpec, hkdfToSliceSpec]
  dsimp only []
  rw [sepConj_assoc, satisfies_pure_sepConj]
  have h_spqr_eq : spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen =
      hkdfExpand C.F (hkdfExtractBytes C.F x.salt x.ikm) x.info x.okmLen := rfl
  have h_exp_len : (spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen).length = x.okmLen := by
    rw [h_spqr_eq]
    rcases hokm_len with h32 | h64 | h96
    · rw [h32, hkdfExpand_32_eq, t1_length]
    · rw [h64, hkdfExpand_64_eq]; simp [t1_length, t2_length]
    · rw [h96, hkdfExpand_96_eq]; simp [t1_length, t2_length, t3_length]
  refine ⟨⟨h_exp_len, htr.1⟩, ?_⟩
  unfold HFrameS2 at hframe_sf
  rw [hx6] at hframe_sf
  rw [← h_spqr_eq] at hokm_sf
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ spqrHkdfWith C.F x.salt x.ikm x.info x.okmLen) ∗
      (memRegion (hsp s0 - 544#64) 1232 ∗ R_inv) :=
    S2Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; exact hokm_le, by rwa [h_exp_len]⟩ trivial
  rw [stackAt_hkdfToSlice s0]
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-- Cross-block `subroutine_ok` lift of `hkdf_to_slice_spqr_placed_ok_sat` to any caller block `i < 619` under `[HkdfPlacedHooksExactSat C.F H]`. -/
theorem hkdf_to_slice_spqr_placed_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 379)
      (withLsCodeRoLoaded lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith C.F))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_slice_spqr_placed_ok_sat C) hi

/-- Block `378` (`spqr::kdf::hkdf_to_vec`) meets `withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F))` under `[HkdfPlacedHooksExactSat C.F H]`. -/
theorem hkdf_to_vec_spqr_placed_ok_sat [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    {H : LibsignalHooks} [HkdfPlacedHooksExactSat C.F H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedSpec A)) :
    subroutine_ok ((blkPC_378).rebase (blkPl_378).base H) (blkPl_378).base
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F))) :=
  hkdf_to_vec_placed_ok A (spqrHkdfWith C.F) h_panic hshim hZero
    (hkdf_to_slice_spqr_placed_ok_of_other_block_sat C)

/-- Cross-block `subroutine_ok` lift of `hkdf_to_vec_spqr_placed_ok_sat` to any caller block `i < 619` under `[HkdfPlacedHooksExactSat C.F H]`. -/
theorem hkdf_to_vec_spqr_placed_ok_of_other_block_sat [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] [HkdfPlacedHooksExactSat C.F H]
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (hZero : HookSat H spqrRustAllocZeroedSym (rustAllocZeroedSpec A))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F))) :=
  keys_ls_subroutine_ok_of_block_cro (hkdf_to_vec_spqr_placed_ok_sat C A h_panic hshim hZero) hi

end LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceSat
