/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPb
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopClPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded `[LibsignalPlacement]` Proof of `<spqr::chain::Chain>::into_pb` (Block `365`)

Code-loaded `[LibsignalPlacement]` post-allocation paths and subroutine contracts
(`chain_into_pb_pinned_cl_placed_ok`, `chain_into_pb_cl_placed_ok`,
`chain_into_pb_pinned_cl_placed_ok_X`, `chain_into_pb_cl_placed_ok_X`) for Block `365`, with
`withLsCodeLoaded lsmpl` on cross-block drop-glue callee `287` (`dropChainEpochSliceSpec A`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.ChainProofs

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L36
open IntoPbDecodes

set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem chain_sepWP_seq_lscl_mid [LibsignalPlacement] {prog : Program} {mid tgt : BitVec 64}
    {s : State} {P : SepProp} {Mid post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P Mid)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Mid sm Pm → SepWP prog tgt sm Pm post) :
    SepWP prog tgt s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun hmid hclm =>
    h2 sm Pm hpc hrun hclm hmid)

set_option maxHeartbeats 800000 in
theorem intoPb_post_alloc_nonwrap_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length) (hl_pos : 1 ≤ x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hnonwrap : x.chain.links.length ≤ x.gChain.linksCap.toNat - x.gChain.linksHead.toNat)
    (hl_new_ne : newLinksPtr ≠ 0) (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 288#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = newLinksPtr)
    (hx3 : s.readReg64 .x3 = x.gChain.linksCap) (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24 : s.readReg64 .x24 = 8#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = x.gChain.linksHead) (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live newLinksPtr (x.chain.links.length * 112) 8 ∗
        memRegion newLinksPtr (x.chain.links.length * 112) ∗
        A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
          x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  let cap := x.gChain.linksCap.toNat
  let head := x.gChain.linksHead.toNat
  let len := x.chain.links.length
  let srcBase := x.gChain.linksPtr + BitVec.ofNat 64 (head * 112)
  have hl_new_lt : len * 112 < 2 ^ 63 := lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_cap_lt
  have hcap_ne : (x.gChain.linksCap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0; rw [h0] at hhead_lt; simp at hhead_lt
  have hult_hc : BitVec.ult x.gChain.linksHead x.gChain.linksCap = true := head_ult_cap hhead_lt
  have hcap_sub_head : x.gChain.linksCap - x.gChain.linksHead = BitVec.ofNat 64 (cap - head) :=
    cap_sub_head_eq_ofNat (Nat.le_of_lt hhead_lt)
  have hult_hi_false : BitVec.ult (BitVec.ofNat 64 (cap - head)) (BitVec.ofNat 64 len) = false :=
    nonwrap_ult_hi_false hnonwrap (by omega)
  have hhi_false :
      (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (cap - head))) &&
        !(BitVec.ofNat 64 len == BitVec.ofNat 64 (cap - head))) = false :=
    nonwrap_hi_false hnonwrap (by omega)
  have hhead_ne_end : (x.gChain.linksHead == x.gChain.linksHead + BitVec.ofNat 64 len) = false :=
    nonwrap_head_ne_end x.gChain.linksHead hl_pos (by omega)
  have hmin_eq :
      (if BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 (cap - head)) = true
       then BitVec.ofNat 64 len else BitVec.ofNat 64 (cap - head)) = BitVec.ofNat 64 len :=
    nonwrap_min_eq_len hnonwrap (by omega)
  have hlsl_len : (BitVec.ofNat 64 len <<< (7 : Nat)) - (BitVec.ofNat 64 len <<< (4 : Nat)) =
      BitVec.ofNat 64 (len * 112) := mul_112_shift_eq len hl_new_lt
  have hhead_mul : x.gChain.linksHead * 112#64 = BitVec.ofNat 64 (head * 112) :=
    head_mul_112_eq_ofNat x.gChain.linksHead (by omega)
  have humulh := umulh_div112_sub_112 hl_pos hl_new_lt
  have hadd1 := ofNat_sub_one_add_one hl_pos
  have hzlen : (x.gChain.epochs.zip x.chain.links).length = len := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hslots := vecDequeSlots_nonwrap_split A cap head x.gChain.linksPtr
    (x.gChain.epochs.zip x.chain.links) hl_cap_lt hhead_lt (by rw [hzlen]; exact hnonwrap)
  rw [hzlen] at hslots
  refine SepWP.focus_weaken hslots (by sep_focus) ?_
  have hloop1 := @intoPb_loop1_run_placed _ A H x.chain.links x.gChain.epochs [] [] s0
  have hepilogue := @chainIntoPb_epilogue_cl_placed _ A H hdealloc hdrop x s0
  refine chain_seq_clean_lscl hcl (mid := (blkPl_365).base + 300#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.live newLinksPtr (len * 112) 8 ∗ memRegion newLinksPtr (len * 112) ∗
      A.live x.gChain.linksPtr (cap * 112) 8 ∗
      arrayAt (chainEpochAt A) 112 srcBase (x.gChain.epochs.zip x.chain.links) ∗
      memRegion x.gChain.linksPtr (head * 112) ∗
      memRegion (x.gChain.linksPtr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 =>
      s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
      s1.readReg64 .x0 = newLinksPtr ∧ s1.readReg64 .x3 = x.gChain.linksCap ∧
      s1.readReg64 .x8 = BitVec.ofNat 64 len ∧ s1.readReg64 .x9 = 0#64 ∧
      s1.readReg64 .x10 = s0.sp - 160#64 ∧ s1.readReg64 .x12 = BitVec.ofNat 64 (len * 112) ∧
      s1.readReg64 .x13 = s0.sp - 160#64 ∧ s1.readReg64 .x14 = s0.sp - 208#64 ∧
      s1.readReg64 .x15 = s0.sp - 260#64 ∧ s1.readReg64 .x16 = newLinksPtr + 52#64 ∧
      s1.readReg64 .x17 = srcBase + 56#64 ∧ s1.readReg64 .x19 = x.chainPtr ∧
      s1.readReg64 .x20 = x.out ∧ s1.readReg64 .x22 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s1.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have hcond_228 :
        (x.gChain.linksHead ==
          if (BitVec.ofNat 64 (cap - head)).ult (BitVec.ofNat 64 x.chain.links.length) = true
          then x.gChain.linksCap else x.gChain.linksHead + BitVec.ofNat 64 x.chain.links.length) = false := by
      dsimp only [len] at hult_hi_false hhead_ne_end
      simp only [hult_hi_false, Bool.false_eq_true, ↓reduceIte, hhead_ne_end]
    have humulh_norm :
        BitVec.truncate 64
          ((BitVec.zeroExtend 128 ((BitVec.ofNat 64 (len * 112) - 112#64) >>> 4) *
            2635249153387078803#128) >>> 64) = BitVec.ofNat 64 (len - 1) := by
      simpa using umulh_div112_sub_112 hl_pos hl_new_lt
    dsimp only [len] at hult_hi_false hhi_false hhead_ne_end hmin_eq hlsl_len humulh humulh_norm hadd1
    wp_steps; dsimp only [srcBase]
    rw [BitVec.add_comm x.gChain.linksPtr (BitVec.ofNat 64 (head * 112))]; wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1⟩
    have hrun_l1 := hloop1 s1 x.gChain x.chain srcBase newLinksPtr hsp0_align
      hl_pos hlen rfl (by simpa using hl_new_lt)
      hpc1 hrun1 hsp1 htr1 hfp1 hx10_1 hx12_1 hx13_1 hx14_1 hx15_1
      (by simpa using hx16_1) (by simpa using hx17_1)
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, memRegion_zero, emp_sepConj,
      List.map_nil, List.zip_nil_right, arrayAt, BitVec.add_zero, List.nil_append] at hrun_l1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (chain_sepWP_seq_lscl_mid hcl1 (SepWP.frame_post_entails (F :=
        memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗ A.live x.gChain.linksPtr (cap * 112) 8 ∗
          memRegion x.gChain.linksPtr (head * 112) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 ((head + len) * 112)) ((cap - head - len) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l1) ?_)
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
    rw [hx0_1] at hx0_2; rw [hx8_1] at hx8_2; rw [hx9_1] at hx9_2
    have hx19_2 : s2.readReg64 .x19 = x.chainPtr := (hcs2.1).trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = x.out := (hcs2.2.1).trans hx20_1
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 len := (hcs2.2.2.2.1).trans hx22_1
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 len := (hcs2.2.2.2.2.2.2.1).trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs2.2.2.2.2.2.2.2.1).trans hx26_1
    have hx28_2 : s2.readReg64 .x28 = x.gChain.linksPtr := (hcs2.2.2.2.2.2.2.2.2.2.1).trans hx28_1
    have hjoin_old := memRegion_nonwrap_join x.gChain.linksPtr cap head len hl_cap_lt (Nat.le_of_lt hhead_lt) hnonwrap
    have hnew_raw : A.live newLinksPtr (len * 112) 8 ⊢
        linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len := by
      unfold linksRawAllocAt
      have hne0 : BitVec.ofNat 64 len ≠ 0 := fun h0 =>
        absurd h0 (beq_eq_false_iff_ne.mp (ofNat_beq_zero_false_of_lt (by omega) (by omega)))
      have htn : (BitVec.ofNat 64 len).toNat = len := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [hne0, ↓reduceIte, htn, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
      exact Entails.refl _
    refine SepWP.weaken_pre hP2 ?_
    refine SepWP.focus_weaken hjoin_old (by dsimp only [srcBase]; sep_focus) ?_
    refine SepWP.focus_weaken hnew_raw (by sep_focus) ?_
    refine chain_seq_clean_lscl hcl2 (mid := (blkPl_365).base + 820#64)
      (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (cap * 112) 8 ∗ memRegion x.gChain.linksPtr (cap * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (Q := fun s3 =>
        s3.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s3 s0 ∧ s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x8 = 0#64 ∧ s3.readReg64 .x9 = 0#64 ∧ s3.readReg64 .x19 = x.chainPtr ∧
        s3.readReg64 .x20 = x.out ∧ s3.readReg64 .x21 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x22 = BitVec.ofNat 64 len ∧ s3.readReg64 .x23 = 0#64 ∧
        s3.readReg64 .x24 = newLinksPtr ∧ s3.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s3.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · simp only [hcap_ne, Bool.false_eq_true, ↓reduceIte]; wp_steps; wp_done
    · rintro s3 hpc3 hrun3 hcl3 ⟨hsp3, htr3, hfp3, hx8_3, hx9_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx28_3⟩
      exact hepilogue s3 newLinksPtr hcl3 hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt hl_new_ne
        hn1 hn2 hn3 hpc3 hrun3 hsp3 htr3 hfp3 hx8_3 hx9_3 hx19_3 hx20_3 hx21_3 hx22_3
        hx23_3 hx24_3 hx26_3 hx28_3

set_option maxHeartbeats 800000 in
theorem intoPb_post_alloc_wrap_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hwrap : x.gChain.linksCap.toNat - x.gChain.linksHead.toNat < x.chain.links.length)
    (hl_new_ne : newLinksPtr ≠ 0) (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 156#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 288#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx0 : s.readReg64 .x0 = newLinksPtr)
    (hx3 : s.readReg64 .x3 = x.gChain.linksCap) (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24 : s.readReg64 .x24 = 8#64) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27 : s.readReg64 .x27 = x.gChain.linksHead) (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live newLinksPtr (x.chain.links.length * 112) 8 ∗
        memRegion newLinksPtr (x.chain.links.length * 112) ∗
        A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
        vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
          x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  let cap := x.gChain.linksCap.toNat
  let head := x.gChain.linksHead.toNat
  let len := x.chain.links.length
  let m₁ := cap - head
  let m₂ := len - m₁
  let srcBase1 := x.gChain.linksPtr + BitVec.ofNat 64 (head * 112)
  let rem1 := x.chain.links.take m₁
  let rem1G := x.gChain.epochs.take m₁
  let rem2 := x.chain.links.drop m₁
  let rem2G := x.gChain.epochs.drop m₁
  have hm1_pos : 1 ≤ m₁ := by omega
  have hm2_pos : 1 ≤ m₂ := by omega
  have hm_sum : m₁ + m₂ = len := by omega
  have hl_new_lt : len * 112 < 2 ^ 63 := lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_cap_lt
  have hm1_lt : m₁ * 112 < 2 ^ 63 := by omega
  have hm2_lt : m₂ * 112 < 2 ^ 63 := by omega
  have hcap_ne : (x.gChain.linksCap == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h0; rw [h0] at hhead_lt; simp at hhead_lt
  have hult_hc : BitVec.ult x.gChain.linksHead x.gChain.linksCap = true := head_ult_cap hhead_lt
  have hhead_ne_cap : (x.gChain.linksHead == x.gChain.linksCap) = false := by
    rw [beq_eq_false_iff_ne]; intro heq; rw [heq] at hhead_lt; exact Nat.lt_irrefl _ hhead_lt
  have hcap_sub_head : x.gChain.linksCap - x.gChain.linksHead = BitVec.ofNat 64 m₁ :=
    cap_sub_head_eq_ofNat (Nat.le_of_lt hhead_lt)
  have hlen_sub_m1 : BitVec.ofNat 64 len - BitVec.ofNat 64 m₁ = BitVec.ofNat 64 m₂ :=
    wrap_len_sub_m1 (Nat.le_of_lt hwrap) (by omega)
  have hlsl_m2 : (BitVec.ofNat 64 m₂ <<< (7 : Nat)) - (BitVec.ofNat 64 m₂ <<< (4 : Nat)) =
      BitVec.ofNat 64 (m₂ * 112) := mul_112_shift_eq m₂ hm2_lt
  have hult_hi_true : BitVec.ult (BitVec.ofNat 64 m₁) (BitVec.ofNat 64 len) = true :=
    wrap_ult_hi_true hwrap (by omega)
  have hhi_true :
      (!(BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁)) &&
        !(BitVec.ofNat 64 len == BitVec.ofNat 64 m₁)) = true := wrap_hi_true hwrap (by omega)
  have hult_false : BitVec.ult (BitVec.ofNat 64 len) (BitVec.ofNat 64 m₁) = false :=
    wrap_ult_false hwrap (by omega)
  have hlsl_m1 : (BitVec.ofNat 64 m₁ <<< (7 : Nat)) - (BitVec.ofNat 64 m₁ <<< (4 : Nat)) =
      BitVec.ofNat 64 (m₁ * 112) := mul_112_shift_eq m₁ hm1_lt
  have hhead_mul : x.gChain.linksHead * 112#64 = BitVec.ofNat 64 (head * 112) :=
    head_mul_112_eq_ofNat x.gChain.linksHead (by omega)
  have humulh1 := umulh_div112_sub_112 hm1_pos hm1_lt
  have humulh1_norm := umulh_div112_sub_112_norm hm1_pos hm1_lt
  have hadd1_m1 := ofNat_sub_one_add_one hm1_pos
  have hm2_cbz_false : (BitVec.ofNat 64 (m₂ * 112) == 0#64) = false :=
    mul_112_beq_zero_false (by omega) hm2_lt
  have humulh2 := umulh_div112_sub_112 hm2_pos hm2_lt
  have humulh2_norm := umulh_div112_sub_112_norm hm2_pos hm2_lt
  have hmadd_dst := madd_m1_112_add_52 newLinksPtr m₁
  have hadd_x2 := add_m1_m2_sub_one hm2_pos hm_sum
  have hadd_x8 := add_m2_sub_one_m1 hm2_pos hm_sum
  have hrem1_len : rem1.length = m₁ := List.length_take_of_le (by omega)
  have hrem1G_len : rem1G.length = m₁ := List.length_take_of_le (by omega)
  have hrem2_len : rem2.length = m₂ := by dsimp [rem2]; rw [List.length_drop]
  have hrem2G_len : rem2G.length = m₂ := by dsimp [rem2G]; rw [List.length_drop, hlen]
  have hzlen : (x.gChain.epochs.zip x.chain.links).length = len := by
    rw [List.length_zip, hlen, Nat.min_self]
  have hzip_take : (x.gChain.epochs.zip x.chain.links).take m₁ = rem1G.zip rem1 :=
    take_zip_eq m₁ x.gChain.epochs x.chain.links
  have hzip_drop : (x.gChain.epochs.zip x.chain.links).drop m₁ = rem2G.zip rem2 :=
    drop_zip_eq m₁ x.gChain.epochs x.chain.links
  have hslots := vecDequeSlots_wrap_split A cap head x.gChain.linksPtr
    (x.gChain.epochs.zip x.chain.links) hl_cap_lt hhead_lt
    (by rw [hzlen]; exact hl_le) (by rw [hzlen]; exact hwrap)
  rw [hzlen, hzip_take, hzip_drop] at hslots
  have hsplit_dst : memRegion newLinksPtr (len * 112) =
      memRegion newLinksPtr (m₁ * 112) ∗
      memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) := by
    have hmul_sum : len * 112 = m₁ * 112 + m₂ * 112 := by rw [← Nat.add_mul, hm_sum]
    conv_lhs => rw [hmul_sum]
    exact ProofLib.memRegion_split' (b := newLinksPtr) (n := m₁ * 112) (k := m₂ * 112)
      (b' := newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) rfl rfl (by omega)
  rw [hsplit_dst]
  refine SepWP.focus_weaken hslots (by sep_focus) ?_
  have hloop1 := @intoPb_loop1_run_placed _ A H rem1 rem1G [] [] s0
  have hloop2 := @intoPb_loop2_run_placed _ A H rem2 rem2G rem1G rem1 s0
  have hepilogue := @chainIntoPb_epilogue_cl_placed _ A H hdealloc hdrop x s0
  refine chain_seq_clean_lscl hcl (mid := (blkPl_365).base + 300#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.live newLinksPtr (len * 112) 8 ∗ memRegion newLinksPtr (m₁ * 112) ∗
      memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
      A.live x.gChain.linksPtr (cap * 112) 8 ∗
      arrayAt (chainEpochAt A) 112 srcBase1 (rem1G.zip rem1) ∗
      arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
      memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 =>
      s1.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s1 s0 ∧ s1.readReg64 .fp = s0.sp - 96#64 ∧
      s1.readReg64 .x0 = newLinksPtr ∧ s1.readReg64 .x3 = x.gChain.linksCap ∧
      s1.readReg64 .x8 = BitVec.ofNat 64 m₁ ∧ s1.readReg64 .x9 = BitVec.ofNat 64 (m₂ * 112) ∧
      s1.readReg64 .x10 = s0.sp - 160#64 ∧ s1.readReg64 .x11 = 0x2492492492492493#64 ∧
      s1.readReg64 .x12 = BitVec.ofNat 64 (m₁ * 112) ∧ s1.readReg64 .x13 = s0.sp - 160#64 ∧
      s1.readReg64 .x14 = s0.sp - 208#64 ∧ s1.readReg64 .x15 = s0.sp - 260#64 ∧
      s1.readReg64 .x16 = newLinksPtr + 52#64 ∧ s1.readReg64 .x17 = srcBase1 + 56#64 ∧
      s1.readReg64 .x19 = x.chainPtr ∧ s1.readReg64 .x20 = x.out ∧
      s1.readReg64 .x22 = BitVec.ofNat 64 len ∧ s1.readReg64 .x25 = BitVec.ofNat 64 len ∧
      s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s1.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have hcond_228 :
        (x.gChain.linksHead ==
          if (BitVec.ofNat 64 m₁).ult (BitVec.ofNat 64 x.chain.links.length) = true
          then x.gChain.linksCap else x.gChain.linksHead + BitVec.ofNat 64 x.chain.links.length) = false := by
      dsimp only [len] at hult_hi_true; simp only [hult_hi_true, ↓reduceIte, hhead_ne_cap]
    dsimp only [len] at hlen_sub_m1 hult_hi_true hhi_true hult_false
    wp_steps; dsimp only [srcBase1]
    rw [BitVec.add_comm x.gChain.linksPtr (BitVec.ofNat 64 (head * 112))]; wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1⟩
    have hrun_l1 := hloop1 s1 x.gChain x.chain srcBase1 newLinksPtr hsp0_align
      (by rw [hrem1_len]; exact hm1_pos) (by rw [hrem1G_len, hrem1_len]) rfl
      (by rw [List.length_nil, Nat.zero_add, hrem1_len]; exact hm1_lt)
      hpc1 hrun1 hsp1 htr1 hfp1 hx10_1 (by rw [hrem1_len]; exact hx12_1)
      hx13_1 hx14_1 hx15_1 (by simpa using hx16_1) (by simpa using hx17_1)
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, memRegion_zero, emp_sepConj,
      List.map_nil, List.zip_nil_right, arrayAt, BitVec.add_zero, List.nil_append, hrem1_len] at hrun_l1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (chain_sepWP_seq_lscl_mid hcl1 (SepWP.frame_post_entails (F :=
        memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗
          memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
          A.live x.gChain.linksPtr (cap * 112) 8 ∗
          arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l1) ?_)
    rintro s2 P2 hpc2 hrun2 hcl2 ⟨hP2, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
    rw [hx0_1] at hx0_2; rw [hx3_1] at hx3_2; rw [hx8_1] at hx8_2; rw [hx9_1] at hx9_2; rw [hx11_1] at hx11_2
    have hx19_2 : s2.readReg64 .x19 = x.chainPtr := (hcs2.1).trans hx19_1
    have hx20_2 : s2.readReg64 .x20 = x.out := (hcs2.2.1).trans hx20_1
    have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 len := (hcs2.2.2.2.1).trans hx22_1
    have hx25_2 : s2.readReg64 .x25 = BitVec.ofNat 64 len := (hcs2.2.2.2.2.2.2.1).trans hx25_1
    have hx26_2 : s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs2.2.2.2.2.2.2.2.1).trans hx26_1
    have hx28_2 : s2.readReg64 .x28 = x.gChain.linksPtr := (hcs2.2.2.2.2.2.2.2.2.2.1).trans hx28_1
    refine SepWP.weaken_pre hP2 ?_
    refine chain_seq_clean_lscl hcl2 (mid := (blkPl_365).base + 512#64)
      (P_mid := memRegion srcBase1 (m₁ * 112) ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((rem1G.map toChainEpochPBGhost).zip (rem1.map chainEpochIntoPb)) ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          A.live newLinksPtr (len * 112) 8 ∗
          memRegion (newLinksPtr + BitVec.ofNat 64 (m₁ * 112)) (m₂ * 112) ∗
          A.live x.gChain.linksPtr (cap * 112) 8 ∗
          arrayAt (chainEpochAt A) 112 x.gChain.linksPtr (rem2G.zip rem2) ∗
          memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32))
      (Q := fun s3 =>
        s3.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s3 s0 ∧ s3.readReg64 .fp = s0.sp - 96#64 ∧
        s3.readReg64 .x0 = newLinksPtr ∧ s3.readReg64 .x2 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x3 = x.gChain.linksCap ∧ s3.readReg64 .x8 = BitVec.ofNat 64 m₁ ∧
        s3.readReg64 .x9 = BitVec.ofNat 64 (m₂ * 112) ∧ s3.readReg64 .x10 = s0.sp - 160#64 ∧
        s3.readReg64 .x11 = BitVec.ofNat 64 (m₂ - 1) ∧ s3.readReg64 .x12 = s0.sp - 160#64 ∧
        s3.readReg64 .x13 = s0.sp - 208#64 ∧ s3.readReg64 .x14 = s0.sp - 260#64 ∧
        s3.readReg64 .x15 = newLinksPtr + BitVec.ofNat 64 (m₁ * 112) + 52#64 ∧
        s3.readReg64 .x16 = x.gChain.linksPtr + 56#64 ∧ s3.readReg64 .x19 = x.chainPtr ∧
        s3.readReg64 .x20 = x.out ∧ s3.readReg64 .x22 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x25 = BitVec.ofNat 64 len ∧
        s3.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        s3.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · wp_steps; wp_done
    · rintro s3 hpc3 hrun3 hcl3 ⟨hsp3, htr3, hfp3, hx0_3, hx2_3, hx3_3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx13_3, hx14_3, hx15_3, hx16_3, hx19_3, hx20_3, hx22_3, hx25_3, hx26_3, hx28_3⟩
      have h0_bv : BitVec.ofNat 64 0 = 0#64 := rfl
      have hrun_l2 := hloop2 s3 x.gChain x.chain x.gChain.linksPtr newLinksPtr m₁ hsp0_align
        (by rw [hrem2_len]; exact hm2_pos) (by rw [hrem2G_len, hrem2_len])
        (by rw [hrem1G_len, hrem1_len]) (by rw [hrem1_len])
        (by rw [hrem1_len, hrem2_len, hm_sum]; exact hl_new_lt)
        hpc3 hrun3 hsp3 htr3 hfp3 (by rw [hrem2_len]; exact hx9_3)
        hx10_3 hx12_3 hx13_3 hx14_3 (by rw [hrem1_len]; exact hx15_3)
        (by rw [hrem1_len, Nat.sub_self, Nat.zero_mul, h0_bv, BitVec.add_zero]; exact hx16_3)
      have happG : rem1G ++ rem2G = x.gChain.epochs := List.take_append_drop m₁ x.gChain.epochs
      have happ : rem1 ++ rem2 = x.chain.links := List.take_append_drop m₁ x.chain.links
      simp only [hrem1_len, hrem2_len, Nat.sub_self, Nat.zero_mul, Nat.zero_add,
        memRegion_zero, emp_sepConj, h0_bv, BitVec.add_zero, happG, happ] at hrun_l2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
        (chain_sepWP_seq_lscl_mid hcl3 (SepWP.frame_post_entails (F :=
          memRegion srcBase1 (m₁ * 112) ∗ memRegion x.out 80 ∗
            chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
            A.live newLinksPtr (len * 112) 8 ∗ A.live x.gChain.linksPtr (cap * 112) 8 ∗
            memRegion (x.gChain.linksPtr + BitVec.ofNat 64 (m₂ * 112)) ((head - m₂) * 112) ∗
            vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
            A.pool ∗ calleeSavedFromPbAt s0 ∗ stackAt (s0.sp - 288#64) dropStack32) hrun_l2) ?_)
      rintro s4 P4 hpc4 hrun4 hcl4 ⟨hP4, hsp4, htr4, hfp4, hx0_4, hx2_4, hx3_4, hx8_4, hx11_4, hcs4⟩
      rw [hx0_3] at hx0_4; rw [hx2_3] at hx2_4; rw [hx3_3] at hx3_4; rw [hx8_3] at hx8_4; rw [hx11_3] at hx11_4
      have hx19_4 : s4.readReg64 .x19 = x.chainPtr := (hcs4.1).trans hx19_3
      have hx20_4 : s4.readReg64 .x20 = x.out := (hcs4.2.1).trans hx20_3
      have hx22_4 : s4.readReg64 .x22 = BitVec.ofNat 64 len := (hcs4.2.2.2.1).trans hx22_3
      have hx25_4 : s4.readReg64 .x25 = BitVec.ofNat 64 len := (hcs4.2.2.2.2.2.2.1).trans hx25_3
      have hx26_4 : s4.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 := (hcs4.2.2.2.2.2.2.2.1).trans hx26_3
      have hx28_4 : s4.readReg64 .x28 = x.gChain.linksPtr := (hcs4.2.2.2.2.2.2.2.2.2.1).trans hx28_3
      have hjoin_old := memRegion_wrap_join x.gChain.linksPtr cap head len hl_cap_lt hhead_lt hl_le hwrap
      have hnew_raw : A.live newLinksPtr (len * 112) 8 ⊢
          linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len := by
        unfold linksRawAllocAt
        have hne0 : BitVec.ofNat 64 len ≠ 0 := fun h0 =>
          absurd h0 (beq_eq_false_iff_ne.mp (ofNat_beq_zero_false_of_lt (by omega) (by omega)))
        have htn : (BitVec.ofNat 64 len).toNat = len := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        simp only [hne0, ↓reduceIte, htn, Nat.sub_self, Nat.zero_mul, memRegion_zero, sepConj_emp]
        exact Entails.refl _
      refine SepWP.weaken_pre hP4 ?_
      refine SepWP.focus_weaken hjoin_old (by dsimp only [srcBase1, m₁, m₂]; sep_focus) ?_
      refine SepWP.focus_weaken hnew_raw (by sep_focus) ?_
      refine chain_seq_clean_lscl hcl4 (mid := (blkPl_365).base + 820#64)
        (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A (BitVec.ofNat 64 len) newLinksPtr len ∗
          (if (x.gChain.linksCap == 0#64) = true then emp
           else A.live x.gChain.linksPtr (cap * 112) 8 ∗ memRegion x.gChain.linksPtr (cap * 112)) ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32)
        (Q := fun s5 =>
          s5.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s5 s0 ∧ s5.readReg64 .fp = s0.sp - 96#64 ∧
          s5.readReg64 .x8 = 0#64 ∧ s5.readReg64 .x9 = 0#64 ∧ s5.readReg64 .x19 = x.chainPtr ∧
          s5.readReg64 .x20 = x.out ∧ s5.readReg64 .x21 = BitVec.ofNat 64 len ∧
          s5.readReg64 .x22 = BitVec.ofNat 64 len ∧ s5.readReg64 .x23 = 0#64 ∧
          s5.readReg64 .x24 = newLinksPtr ∧ s5.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          s5.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
      · simp only [hcap_ne, Bool.false_eq_true, ↓reduceIte]; wp_steps; wp_done
      · rintro s5 hpc5 hrun5 hcl5 ⟨hsp5, htr5, hfp5, hx8_5, hx9_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx26_5, hx28_5⟩
        exact hepilogue s5 newLinksPtr hcl5 hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt hl_new_ne
          hn1 hn2 hn3 hpc5 hrun5 hsp5 htr5 hfp5 hx8_5 hx9_5 hx19_5 hx20_5 hx21_5 hx22_5
          hx23_5 hx24_5 hx26_5 hx28_5

theorem intoPb_empty_links_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainIntoPbCall) (s0 s1 : State)
    (hcl1 : LibsignalCodeLoaded lsmpl s1.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hnil : x.chain.links = [])
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc1 : s1.pc = (blkPl_365).base + 116#64)
    (hrun1 : s1.status = .Running) (hsp1 : s1.sp = s0.sp - 288#64) (htr1 : TraceCalleeSaved s1 s0)
    (hfp1 : s1.readReg64 .fp = s0.sp - 96#64) (hx19_1 : s1.readReg64 .x19 = x.chainPtr)
    (hx20_1 : s1.readReg64 .x20 = x.out)
    (hx23_1 : s1.readReg64 .x23 = BitVec.ofNat 64 (x.chain.links.length * 112))
    (hx25_1 : s1.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26_1 : s1.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx28_1 : s1.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s1
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hepilogue := @chainIntoPb_epilogue_cl_placed _ A H hdealloc hdrop x s0
  have hlen0 : x.chain.links.length = 0 := by rw [hnil]; rfl
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by rw [hlen0]; decide
  have hdealloc_buf := vecDequeSlots_nil_entails_dealloc A x.gChain.linksCap x.gChain.linksPtr
    x.gChain.linksHead x.gChain.epochs x.chain.links hnil hl_cap_lt
  have hraw0 : (emp : SepProp) ⊢
      arrayAt (chainEpochPBAt A) 112 8#64
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length := by
    unfold linksRawAllocAt; simp [hnil, arrayAt]; exact Entails.refl _
  refine SepWP.focus_weaken hdealloc_buf (by sep_focus) ?_
  refine chain_seq_clean_lscl hcl1 (mid := (blkPl_365).base + 820#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A) 112 8#64
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) 8#64 x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s2 =>
      s2.sp = s0.sp - 288#64 ∧ TraceCalleeSaved s2 s0 ∧ s2.readReg64 .fp = s0.sp - 96#64 ∧
      s2.readReg64 .x8 = 0#64 ∧ s2.readReg64 .x9 = 0#64 ∧ s2.readReg64 .x19 = x.chainPtr ∧
      s2.readReg64 .x20 = x.out ∧ s2.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
      s2.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧ s2.readReg64 .x23 = 0#64 ∧
      s2.readReg64 .x24 = 8#64 ∧ s2.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      s2.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · rw [hlen0] at hx23_1 hx25_1 ⊢
    simp only [Nat.zero_mul, BitVec.ofNat_eq_ofNat] at hx23_1 hx25_1 ⊢
    wp_steps; rw [← emp_sepConj (memRegion x.out 80 ∗ _)]
    refine SepWP.focus_weaken hraw0 (by sep_focus) ?_
    rw [hlen0]; wp_done
  · rintro s2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hfp2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx26_2, hx28_2⟩
    exact hepilogue s2 8#64 hcl2 hsp0_align hlen hl_cap_lt hl_cap_ne hl_new_lt (by decide)
      hn1 hn2 hn3 hpc2 hrun2 hsp2 htr2 hfp2 hx8_2 hx9_2 hx19_2 hx20_2 hx21_2 hx22_2
      hx23_2 hx24_2 hx26_2 hx28_2

theorem intoPb_post_alloc_ok_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainIntoPbCall) (s0 sm : State)
    (hclm : LibsignalCodeLoaded lsmpl sm.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen_pos : 1 ≤ x.chain.links.length) (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_le : x.chain.links.length ≤ x.gChain.linksCap.toNat)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63) (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hl_head : if x.gChain.linksCap = 0 then x.gChain.linksHead = 0
               else x.gChain.linksHead.toNat < x.gChain.linksCap.toNat)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63) (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpcm : sm.pc = (blkPl_365).base + 148#64)
    (hrunm : sm.status = .Running) (hspm : sm.sp = s0.sp - 288#64) (htrm : TraceCalleeSaved sm s0)
    (hfpm : sm.readReg64 .fp = s0.sp - 96#64) (hx0m_ne : sm.readReg64 .x0 ≠ 0)
    (hx3m : sm.readReg64 .x3 = x.gChain.linksCap) (hx19m : sm.readReg64 .x19 = x.chainPtr)
    (hx20m : sm.readReg64 .x20 = x.out)
    (hx22m : sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx24m : sm.readReg64 .x24 = 8#64)
    (hx25m : sm.readReg64 .x25 = BitVec.ofNat 64 x.chain.links.length)
    (hx26m : sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx27m : sm.readReg64 .x27 = x.gChain.linksHead)
    (hx28m : sm.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) sm
      (memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        A.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
        memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
        (if x.gChain.linksCap = 0 then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
             x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hcap_ne0 : x.gChain.linksCap ≠ 0#64 := by
    intro h0; rw [h0] at hl_le; change x.chain.links.length ≤ 0 at hl_le; omega
  have hhead_lt : x.gChain.linksHead.toNat < x.gChain.linksCap.toNat := by
    simpa only [BitVec.ofNat_eq_ofNat, hcap_ne0, ↓reduceIte] using hl_head
  simp only [BitVec.ofNat_eq_ofNat, hcap_ne0, ↓reduceIte, sepConj_assoc]
  have hnonwrap_lem := intoPb_post_alloc_nonwrap_cl_placed (A := A) (H := H) hdealloc hdrop
    x s0 (sm.setPC ((blkPl_365).base + 156#64)) (sm.readReg64 .x0) hclm
  have hwrap_lem := intoPb_post_alloc_wrap_cl_placed (A := A) (H := H) hdealloc hdrop
    x s0 (sm.setPC ((blkPl_365).base + 156#64)) (sm.readReg64 .x0) hclm
  have hcbz_x0 : (sm.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hx0m_ne
  have hcbz_x25 : (BitVec.ofNat 64 x.chain.links.length == 0#64) = false :=
    ofNat_beq_zero_false_of_lt (by omega) (by omega)
  refine seq_clean (mid := (blkPl_365).base + 156#64)
    (P_mid := memRegion x.out 80 ∗ chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      A.live (sm.readReg64 .x0) (x.chain.links.length * 112) 8 ∗
      memRegion (sm.readReg64 .x0) (x.chain.links.length * 112) ∗
      A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
      vecDequeSlotsAt (chainEpochAt A) 112 x.gChain.linksCap.toNat x.gChain.linksHead.toNat
        x.gChain.linksPtr (x.gChain.epochs.zip x.chain.links) 0 x.gChain.linksCap.toNat ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗ intoPbScratchAt s0 x.gChain x.chain ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun s1 => s1 = sm.setPC ((blkPl_365).base + 156#64)) ?_ ?_
  · wp_steps
    exact SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨Entails.refl _, rfl⟩
  · rintro _ _ _ rfl
    by_cases hnw : x.chain.links.length ≤ x.gChain.linksCap.toNat - x.gChain.linksHead.toNat
    · exact hnonwrap_lem hsp0_align hlen hlen_pos hl_le hl_cap_lt hl_cap_ne hhead_lt
        hnw hx0m_ne hn1 hn2 hn3 rfl hrunm hspm htrm hfpm rfl hx3m hx19m hx20m hx22m
        hx24m hx25m hx26m hx27m hx28m
    · exact hwrap_lem hsp0_align hlen hl_le hl_cap_lt hl_cap_ne hhead_lt
        (by omega) hx0m_ne hn1 hn2 hn3 rfl hrunm hspm htrm hfpm rfl hx3m hx19m hx20m hx22m
        hx24m hx25m hx26m hx27m hx28m

set_option maxHeartbeats 800000 in
/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `withLsCodeLoaded lsmpl (chainIntoPbPinnedSpec A)`. -/
theorem chain_into_pb_pinned_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (withLsCodeLoaded lsmpl (chainIntoPbPinnedSpec A)) := by
  refine subroutine_ok_of_sepWPp fun x R s0 hpc hrun hpre hsp_align => ?_
  obtain ⟨hcl0, hpre'⟩ := extract_withLsCodeLoaded hpre
  refine ⟨(chainIntoPbPinnedSpec A).pre x s0, R, hpre', ?_⟩
  dsimp only [State.spAligned] at hsp_align
  refine SepWPp.of_sepWP (mid := (blkPl_365).base + 116#64) ?_
  wp_conv_pre => dsimp only [chainIntoPbPinnedSpec]
  wp_focus_pure
  rintro ⟨hx8, hx0⟩
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left (chainAt_unpack A x.chainPtr x.gChain x.chain))) ?_
  wp_focus_pure
  rintro ⟨hlen, hl_le, hl_cap_lt, hl_cap_ne, hl_head, hn1, hn2, hn3⟩
  have hl_new_lt : x.chain.links.length * 112 < 2 ^ 63 := by omega
  wp_simp_pre [sepConj_assoc]
  refine sepWP_mono_lscl hcl0 (intoPb_prologue_placed x s0 hsp_align hl_new_lt hpc hrun hx8 hx0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hP1, hsp1, htr1, hfp1, hx3_1, hx19_1, hx20_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
  refine SepWPp.weaken_pre hP1 ?_
  by_cases hnil : x.chain.links = []
  · refine SepWPp.of_sepWP_ret ?_
    refine SepWP.mono (intoPb_empty_links_cl_placed hdealloc hdrop x s0 s1 hcl1 hsp_align hnil hlen hl_cap_lt hl_cap_ne
      hn1 hn2 hn3 hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1 hx26_1 hx28_1) ?_
    rintro sf P_f _ _ ⟨hP_f, hspf, htrf, hcsf⟩
    refine ⟨fun hm => ?_, hspf, hcsf⟩
    dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨htrf, Satisfies.mono (sepConj_mono_left hP_f) hm⟩
  · have hlen_pos : 1 ≤ x.chain.links.length := Nat.pos_of_ne_zero (List.length_pos_iff.mpr hnil).ne'
    refine SepWPp.of_sepWP (mid := (blkPl_365).base + 148#64) ?_
    refine sepWP_mono_lscl hcl1 (intoPb_alloc_step_placed hshim halloc x s0 s1 hsp_align hlen_pos hl_new_lt
      hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1) ?_
    rintro sm Pm hpcm hrunm hclm ⟨hspm, hfpm, hx3m, hx19m, hx20m, hx22m, hx23m, hx24m, hx25m, hx26m, hx27m, hx28m, hbranch⟩
    by_cases hoom : sm.readReg64 .x0 = 0
    · simp only [hoom, ↓reduceIte] at hbranch
      exact intoPb_oom_panic_placed (A := A) hpan_oom x s0 sm Pm R hpcm hrunm hoom hbranch
    · simp only [hoom, ↓reduceIte] at hbranch
      refine SepWPp.weaken_pre hbranch.2 ?_
      refine SepWPp.of_sepWP_ret ?_
      refine SepWP.mono (intoPb_post_alloc_ok_cl_placed hdealloc hdrop x s0 sm hclm hsp_align hlen_pos hlen hl_le
        hl_cap_lt hl_cap_ne hl_head hn1 hn2 hn3 hpcm hrunm hspm hbranch.1 hfpm hoom hx3m
        hx19m hx20m hx22m hx24m hx25m hx26m hx27m hx28m) ?_
      rintro sf P_f _ _ ⟨hP_f, hspf, htrf, hcsf⟩
      refine ⟨fun hm => ?_, hspf, hcsf⟩
      dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨htrf, Satisfies.mono (sepConj_mono_left hP_f) hm⟩

/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `withLsCodeLoaded lsmpl (chainIntoPbSpec A)`. -/
theorem chain_into_pb_cl_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (withLsCodeLoaded lsmpl (chainIntoPbSpec A)) := by
  have hpinned := chain_into_pb_pinned_cl_placed_ok hshim halloc hdealloc hdrop hpan_oom
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (subroutine_ok_apply_outcome hpinned x R hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpec, chainIntoPbSpec] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (chainPBIntoPinnedAt_entails_protoRepr A x.gChain x.out x.chain)))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `withLsCodeLoaded lsmpl (chainIntoPbPinnedSpecX A)`. -/
theorem chain_into_pb_pinned_cl_placed_ok_X [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (withLsCodeLoaded lsmpl (chainIntoPbPinnedSpecX A)) := by
  have hpinned := chain_into_pb_pinned_cl_placed_ok hshim halloc hdealloc hdrop hpan_oom
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl0, hpre0⟩ := extract_withLsCodeLoaded hpre
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (chainIntoPbPinnedSpec A)).pre x s0 ∗
      (memRegion (s0.sp - 16672#64) 12256 ∗ R) := by
    dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpecX, chainIntoPbPinnedSpec] at hpre0 ⊢
    rw [stackAt_chainIntoPbX_split s0.sp] at hpre0
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0, Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre0⟩
  refine (subroutine_ok_apply_outcome hpinned x
    (memRegion (s0.sp - 16672#64) 12256 ∗ R) hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX] at hpost ⊢
    rw [stackAt_chainIntoPbX_split s0.sp]
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpec, chainIntoPbPinnedSpecX] at hpost ⊢
    rw [← sepConj_assoc] at hpost; exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

/-- Code-loaded `[LibsignalPlacement]` proof of `<spqr::chain::Chain>::into_pb` (Block `365`)
against `withLsCodeLoaded lsmpl (chainIntoPbSpecX A)`. -/
theorem chain_into_pb_cl_placed_ok_X [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hshim : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2") sessionShimSpec)
    (halloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc") (rustAllocSpec A))
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hpan_oom : ((blkPC_365).rebase (blkPl_365).base H).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") = some Rust.panicked) :
    subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (blkPl_365).base
      (withLsCodeLoaded lsmpl (chainIntoPbSpecX A)) := by
  have hpinned := chain_into_pb_pinned_cl_placed_ok_X hshim halloc hdealloc hdrop hpan_oom
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (subroutine_ok_apply_outcome hpinned x R hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hconv, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hconv, ?_⟩
    dsimp only [withLsCodeLoaded, chainIntoPbPinnedSpecX, chainIntoPbSpecX] at hpost ⊢
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
      (chainPBIntoPinnedAt_entails_protoRepr A x.gChain x.out x.chain)))) hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

end CryptoVerification.SpqrV1.ChainProofs
