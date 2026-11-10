/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoop
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlaced
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Loop Error Cleanup Proofs for `<spqr::chain::Chain>::from_pb` (Block `364`)

Code-loaded `[LibsignalPlacement]` loop error-cleanup lemmas (`+380`, `+452`, `+520`, `+644`,
`+780`) for Block `364`, threading `LibsignalCodeLoaded lsmpl` into `fromPb_join_err_cl_placed`.
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
open FromPbDecodes

set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+520` when `curPB.recv = none` (`x20 = 0xffffffffffffffff#64`). -/
theorem fromPb_loop_err_520_none_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx20 : s.readReg64 .x20 = 0xffffffffffffffff#64)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  try dsimp only [BitVec.ofNat_eq_ofNat] at herr hpc ⊢
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 792#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold loopScratchAt
    wp_steps
    refine SepWP.focus_weaken
      (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
      (by unfold loopScratchAt; sep_focus) ?_
    wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1⟩
    exact herr s1 convG convEpochs remG remPB sp0_val hcl1 hsp0_align hfromPb_eq hconv_len hrem_len
      hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx27_1

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+520` when `curPB.recv = some recvPb`. -/
theorem fromPb_loop_err_520_some_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (rncap rnptr rpcap rpptr sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 520#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = rpptr) (hx19 : s.readReg64 .x19 = rnptr)
    (hx20 : s.readReg64 .x20 = rncap)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx26 : s.readReg64 .x26 = rpcap) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hrn_cmn := add_one_beq_zero_of_lt_pow63 hrn_lt
  try dsimp only [BitVec.ofNat_eq_ofNat] at herr hdealloc hpc ⊢
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 596#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A rpcap rpptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x12 = rpptr ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x26 = rpcap) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hrn : rncap = 0
    · have hrnb : (rncap == 0#64) = true := beq_iff_eq.mpr hrn
      simp only [hrnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hrnb : (rncap == 0#64) = false := beq_eq_false_iff_ne.mpr hrn
      have hrn_pos : rncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hrn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hrnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc (rnptr, rncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx12_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1⟩
    refine fromPb_seq_clean_lscl hcl1 (mid := (blkPl_364).base + 792#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
        sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hrp : rpcap = 0
      · have hrpb : (rpcap == 0#64) = true := beq_iff_eq.mpr hrp
        simp only [hrpb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps
        refine SepWP.focus_weaken
          (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
          (by unfold loopScratchAt; sep_focus) ?_
        wp_done
      · have hrpb : (rpcap == 0#64) = false := beq_eq_false_iff_ne.mpr hrp
        have hrp_pos : rpcap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hrp (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hrpb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (rpptr, rpcap.toNat, 1)
        wp_steps
        refine SepWP.focus_weaken
          (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
          (by unfold loopScratchAt; sep_focus) ?_
        rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hfp2, hx0_2, hx11_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx27_2⟩
      exact herr s2 convG convEpochs remG remPB sp0_val hcl2 hsp0_align hfromPb_eq hconv_len hrem_len
        hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc2 hrun2 hsp2 htr2 hfp2 hx0_2 hx11_2
        hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx27_2

set_option maxHeartbeats 800000 in
/-- Tail bridge at `+780 .. +792` into `fromPb_join_err_cl_placed`. -/
theorem fromPb_loop_err_780_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 780#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have herr := @fromPb_join_err_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
  try dsimp only [BitVec.ofNat_eq_ofNat] at herr hpc ⊢
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 792#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112) ∧
      sm.readReg64 .x11 = x.gPb.linksPtr ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold loopScratchAt
    wp_steps
    refine SepWP.focus_weaken
      (loopScratchAt_entails_joinScratchAt s0 x sp0_val)
      (by unfold loopScratchAt; sep_focus) ?_
    wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx0_1, hx11_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1⟩
    exact herr s1 convG convEpochs remG remPB sp0_val hcl1 hsp0_align hfromPb_eq hconv_len hrem_len
      hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx0_1 hx11_1
      hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx27_1

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+380` when `curPB.recv = none`. -/
theorem fromPb_loop_err_380_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 380#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx21 : s.readReg64 .x21 = snptr) (hx24 : s.readReg64 .x24 = sncap)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convEpochs.length * 112))
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h780 := @fromPb_loop_err_780_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  try dsimp only [BitVec.ofNat_eq_ofNat] at h780 hdealloc hpc ⊢
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 408#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A spcap spptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x27 = spcap ∧ sm.readReg64 .x28 = spptr) ?_ ?_
  · unfold vecCapPtrDealloc loopScratchAt
    by_cases hsn : sncap = 0
    · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
      simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
      wp_steps; wp_done
    · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
      have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
        intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
      simp only [hsnb, Bool.false_eq_true, ↓reduceIte]
      rw [stackAt_subStack_split_allocHook s0.sp]
      wp_steps
      wp_call hdealloc (snptr, sncap.toNat, 1)
      wp_steps; rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx11_1, hx23_1, hx27_1, hx28_1⟩
    refine fromPb_seq_clean_lscl hcl1 (mid := (blkPl_364).base + 780#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x19 = 0#64 ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x27 = 0#64) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hsp_cap : spcap = 0
      · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
        rw [hsp_cap] at hx27_1
        simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps; wp_done
      · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
        have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hspb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (spptr, spcap.toNat, 1)
        wp_steps; rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hfp2, hx11_2, hx19_2, hx20_2, hx23_2, hx27_2⟩
      exact h780 s2 convG convEpochs remG remPB sp0_val hcl2 hsp0_align hfromPb_eq hconv_len hrem_len
        hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc2 hrun2 hsp2 htr2 hfp2 hx11_2
        hx19_2 hx20_2 hx23_2 hx27_2

set_option maxHeartbeats 800000 in
/-- Error cleanup at `+644` when `curPB.recv = some recvPb` fails `tst`. -/
theorem fromPb_loop_err_644_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr rncap rnptr rpcap rpptr x22_val sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 644#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx12 : s.readReg64 .x12 = rpptr)
    (hx19 : s.readReg64 .x19 = rnptr) (hx20 : s.readReg64 .x20 = rncap)
    (hx21 : s.readReg64 .x21 = snptr) (hx22 : s.readReg64 .x22 = x22_val)
    (hx24 : s.readReg64 .x24 = sncap)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (convEpochs.length * 112))
    (hx26 : s.readReg64 .x26 = rpcap) (hx27 : s.readReg64 .x27 = spcap)
    (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_644_to_704_placed _ A H hdealloc F_frame
    x s0 s convEpochs.length rncap rnptr rpcap rpptr snptr x22_val sncap spcap spptr sp0_val
    hsp0_align hrn_lt hrn_ne hrp_lt hrp_ne hpc hrun hsp htr hfp hx11 hx12 hx19 hx20 hx21 hx22
    hx24 hx25 hx26 hx27 hx28
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 704#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x sp0_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x21 = snptr ∧ sm.readReg64 .x22 = x22_val ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = sncap ∧ sm.readReg64 .x27 = spcap ∧
      sm.readReg64 .x28 = spptr) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx11_1, hx21_1, hx22_1, hx23_1, hx24_1, hx27_1, hx28_1⟩
    refine SepWP.weaken_pre (Entails.of_eq (by
      dsimp only [F_frame]; ac_rfl :
      F_frame ∗ A.pool ∗ loopScratchAt s0 x sp0_val ∗ stackAt (s0.sp - 192#64) chainFromPbSubStack =
      memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)) ?_
    have h780 := @fromPb_loop_err_780_cl_placed _ A H hdealloc hchain_slice hproto_slice x s0
    have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 192#64 hsp0_align (by decide)
    try dsimp only [BitVec.ofNat_eq_ofNat] at h780 hdealloc hpc1 ⊢
    refine fromPb_seq_clean_lscl hcl1 (mid := (blkPl_364).base + 732#64)
      (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
        sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
        sm.readReg64 .x22 = x22_val ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x27 = spcap ∧ sm.readReg64 .x28 = spptr) ?_ ?_
    · unfold vecCapPtrDealloc loopScratchAt
      by_cases hsn : sncap = 0
      · have hsnb : (sncap == 0#64) = true := beq_iff_eq.mpr hsn
        simp only [hsnb, ↓reduceIte, emp_sepConj, sepConj_emp]
        wp_steps; wp_done
      · have hsnb : (sncap == 0#64) = false := beq_eq_false_iff_ne.mpr hsn
        have hsn_pos : sncap.toNat > 0 := Nat.pos_of_ne_zero (by
          intro hz; exact hsn (BitVec.eq_of_toNat_eq (by simpa using hz)))
        simp only [hsnb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (snptr, sncap.toNat, 1)
        wp_steps; rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hfp2, hx11_2, hx20_2, hx22_2, hx23_2, hx27_2, hx28_2⟩
      refine fromPb_seq_clean_lscl hcl2 (mid := (blkPl_364).base + 780#64)
        (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
          arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
          arrayAt (chainEpochPBAt A) 112
            (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
          loopScratchAt s0 x x22_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
          sm.readReg64 .x19 = 0#64 ∧
          sm.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112) ∧
          sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
          sm.readReg64 .x27 = 0#64) ?_ ?_
      · unfold vecCapPtrDealloc loopScratchAt
        by_cases hsp_cap : spcap = 0
        · have hspb : (spcap == 0#64) = true := beq_iff_eq.mpr hsp_cap
          rw [hsp_cap] at hx27_2
          simp only [hspb, ↓reduceIte, emp_sepConj, sepConj_emp]
          wp_steps; wp_done
        · have hspb : (spcap == 0#64) = false := beq_eq_false_iff_ne.mpr hsp_cap
          have hsp_pos : spcap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hsp_cap (BitVec.eq_of_toNat_eq (by simpa using hz)))
          simp only [hspb, Bool.false_eq_true, ↓reduceIte]
          rw [stackAt_subStack_split_allocHook s0.sp]
          wp_steps
          wp_call hdealloc (spptr, spcap.toNat, 1)
          wp_steps; rw [hsp2]; wp_done
      · rintro s3 hpc3 hrun3 hcl3 ⟨hsp3, htr3, hfp3, hx11_3, hx19_3, hx20_3, hx23_3, hx27_3⟩
        exact h780 s3 convG convEpochs remG remPB x22_val hcl3 hsp0_align hfromPb_eq hconv_len hrem_len
          hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc3 hrun3 hsp3 htr3 hfp3 hx11_3
          hx19_3 hx20_3 hx23_3 hx27_3

set_option maxHeartbeats 800000 in
theorem fromPb_loop_err_452_none_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr x9_val sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx20 : s.readReg64 .x20 = 0xffffffffffffffff#64) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = sncap)
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_452_to_520_placed _ A H hdealloc F_frame
    x s0 s sncap snptr spcap spptr x9_val (s.readReg64 .x12) (s.readReg64 .x19)
    0xffffffffffffffff#64 (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (s.readReg64 .x26) sp0_val
    hsp0_align hsn_lt hsn_ne hsp_lt hsp_ne hpc hrun hsp htr hfp hx9 hx11 rfl rfl hx20 hx21
    hx23 hx24 rfl hx27 hx28
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 520#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x x9_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = s.readReg64 .x12 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
      sm.readReg64 .x20 = 0xffffffffffffffff#64 ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x26 = s.readReg64 .x26) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx11_1, _, _, hx20_1, hx23_1, _⟩
    refine SepWP.weaken_pre ?_
      (fromPb_loop_err_520_none_cl_placed hdealloc hchain_slice hproto_slice x s0 s1 convG convEpochs remG remPB x9_val
        hcl1 hsp0_align hfromPb_eq hconv_len hrem_len hsplit_len hl_le hl_lt hl_ne hn_le hn_lt hn_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx20_1 hx23_1)
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)

set_option maxHeartbeats 800000 in
theorem fromPb_loop_err_452_some_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch)
    (remG : List ChainEpochPBGhost) (remPB : List ChainEpochPB)
    (sncap snptr spcap spptr rncap rnptr rpcap rpptr x9_val sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hconv_len : convG.length = convEpochs.length) (hrem_len : remG.length = remPB.length)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hsn_lt : sncap.toNat < 2 ^ 63) (hsn_ne : snptr ≠ 0)
    (hsp_lt : spcap.toNat < 2 ^ 63) (hsp_ne : spptr ≠ 0)
    (hrn_lt : rncap.toNat < 2 ^ 63) (hrn_ne : rnptr ≠ 0)
    (hrp_lt : rpcap.toNat < 2 ^ 63) (hrp_ne : rpptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 452#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = x9_val) (hx11 : s.readReg64 .x11 = x.gPb.linksPtr)
    (hx12 : s.readReg64 .x12 = rpptr) (hx19 : s.readReg64 .x19 = rnptr)
    (hx20 : s.readReg64 .x20 = rncap) (hx21 : s.readReg64 .x21 = snptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = sncap) (hx26 : s.readReg64 .x26 = rpcap)
    (hx27 : s.readReg64 .x27 = spcap) (hx28 : s.readReg64 .x28 = spptr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        vecCapPtrDealloc A sncap snptr ∗ vecCapPtrDealloc A spcap spptr ∗
        vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        loopScratchAt s0 x sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  let F_frame :=
    memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      vecCapPtrDealloc A rncap rnptr ∗ vecCapPtrDealloc A rpcap rpptr ∗
      arrayAt (chainEpochPBAt A) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗
      calleeSavedFromPbAt s0
  have hpart1 := @fromPb_loop_err_452_to_520_placed _ A H hdealloc F_frame
    x s0 s sncap snptr spcap spptr x9_val rpptr rnptr rncap
    (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) rpcap sp0_val
    hsp0_align hsn_lt hsn_ne hsp_lt hsp_ne hpc hrun hsp htr hfp hx9 hx11 hx12 hx19 hx20 hx21
    hx23 hx24 hx26 hx27 hx28
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 520#64)
    (P_mid := F_frame ∗ A.pool ∗ loopScratchAt s0 x x9_val ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x11 = x.gPb.linksPtr ∧
      sm.readReg64 .x12 = rpptr ∧ sm.readReg64 .x19 = rnptr ∧
      sm.readReg64 .x20 = rncap ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x26 = rpcap) ?_ ?_
  · refine SepWP.weaken_pre ?_ hpart1
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx11_1, hx12_1, hx19_1, hx20_1, hx23_1, hx26_1⟩
    refine SepWP.weaken_pre ?_
      (fromPb_loop_err_520_some_cl_placed hdealloc hchain_slice hproto_slice x s0 s1 convG convEpochs remG remPB
        rncap rnptr rpcap rpptr x9_val hcl1 hsp0_align hfromPb_eq hconv_len hrem_len hsplit_len
        hl_le hl_lt hl_ne hn_le hn_lt hn_ne hrn_lt hrn_ne hrp_lt hrp_ne
        hpc1 hrun1 hsp1 htr1 hfp1 hx11_1 hx12_1 hx19_1 hx20_1 hx23_1 hx26_1)
    exact Entails.of_eq (by dsimp only [F_frame]; ac_rfl)

end CryptoVerification.SpqrV1.ChainProofs
