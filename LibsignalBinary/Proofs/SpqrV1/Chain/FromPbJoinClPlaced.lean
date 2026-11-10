/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoin
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded Join-Point and Cleanup Proofs for `<spqr::chain::Chain>::from_pb` (Block `364`)

Code-loaded `[LibsignalPlacement]` bad-direction and join-point lemmas for Block `364`,
threading `withLsCodeLoaded lsmpl` contracts on cross-block drop-glue callees `287`
(`dropChainEpochSliceSpec A`) and `288` (`dropProtoEpochSliceSpec A`).
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
open CryptoVerification.SpqrV1.Layout.L26
open FromPbDecodes

set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] csel_both_zero

private theorem div_112_magic_nat_eq {k : Nat} (hk : k * 112 < 2 ^ 63) :
    (BitVec.ofNat 64 (k * 112) >>> 4) * 0x6db6db6db6db6db7#64 = BitVec.ofNat 64 k :=
  div_112_magic_eq hk

@[local simp, local arm64_norm, local wp_norm]
private theorem sub_self_lsr4_mul_magic (a : BitVec 64) :
    ((a - a) >>> 4) * 0x6db6db6db6db6db7#64 = 0#64 := by
  rw [BitVec.sub_self]; rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sub_self_lsr4_bv_mul_magic (a : BitVec 64) :
    ((a - a) >>> 4#64) * 0x6db6db6db6db6db7#64 = 0#64 := by
  rw [BitVec.sub_self]; rfl

private theorem csel_ult_sub_zero_of_le (n : Nat) (cap : BitVec 64) (hle : n ≤ cap.toNat) :
    (if (BitVec.ofNat 64 n).ult cap = true then 0#64
     else BitVec.ofNat 64 n - cap) = 0#64 := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt hle cap.isLt)]
  by_cases hlt : n < cap.toNat
  · have hult : (BitVec.ofNat 64 n).ult cap = true := by simp [BitVec.ult, hn, hlt]
    simp [hult]
  · have heq : n = cap.toNat := by omega
    have hbv : BitVec.ofNat 64 n = cap := by rw [heq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [hbv, BitVec.sub_self]
    cases (cap.ult cap) <;> rfl

private theorem pool_entails_empty_arrayAt_pool {α : Type} (A : RustAlloc)
    (elem : α → BitVec 64 → SepProp) (stride : Nat) (ptr : BitVec 64) :
    A.pool ⊢ arrayAt elem stride ptr [] ∗ A.pool :=
  Entails.of_eq (emp_sepConj A.pool).symm

theorem fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α} {m : Memory}
    (hcallee : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hcl : LibsignalCodeLoaded lsmpl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  subroutine_ok_mono hcallee
    (fun _ _ s0 hp => by
      have ⟨hm, hpre⟩ := extract_withMemEq hp
      have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hm ▸ hcl
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hcl0, hpre⟩)
    (fun _ _ _ _ hq => hq)

theorem fromPb_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

set_option maxHeartbeats 800000 in
theorem fromPb_bad_direction_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir_uge : BitVec.ule 2#32 x.pb.direction = true)
    (hlen : x.gPb.epochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (_hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 292#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochPBAt A) 112 x.gPb.linksPtr (x.gPb.epochs.zip x.pb.links) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ A H x s0
  have hep_dealloc := @fromPb_epilogue_dealloc_placed _ A H hdealloc x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode :=
    chainFromPb_of_direction_uge_two hdir_uge
  refine SepWP.focus_weaken
    (arrayAt_chainEpochPBAt_entails_protoRepr A x.gPb.epochs x.pb.links x.gPb.linksPtr hlen)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
    (by sep_focus) ?_
  rw [memRegion_88_words4_rest x.out]
  wp_pull_exists
  refine seq_clean (mid := (blkPl_364).base + 316#64)
    (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      memRegion x.gPb.linksPtr (x.pb.links.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x19 = x.gPb.linksPtr ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
  · unfold chainPBHeadersAt
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps_lscl (lsmpl.base 288)
    refine SepWP.focus_weaken
      (err_stateDecode_pack_words A x.out x.pb hfromPb_eq _ _ _ (bitvec_low_byte_clear_zero _))
      (by sep_focus) ?_
    have hcall :=
      fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hproto_slice ‹LibsignalCodeLoaded lsmpl _›
    dsimp only [withMemEq, dropProtoEpochSliceSpec, ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hcall
    wp_call hcall ⟨x.gPb.linksPtr, x.pb.links⟩
    rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 ⟨hsp1, htr1, hx19_1, hx25_1⟩
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := (blkPl_364).base + 344#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x25 = x.pbPtr) ?_ ?_
    · unfold chainPBHeadersAt
      by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp1]; wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2, hx25_2⟩
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        unfold vecCapPtrDealloc
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := (blkPl_364).base + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · unfold chainPBHeadersAt; wp_steps
          refine SepWP.focus_weaken
            (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb)
            (by unfold chainPBHeadersAt; sep_focus) ?_
          wp_done
        · rintro s3 hpc3 hrun3 ⟨hsp3, htr3⟩
          exact hep_ret s3 hsp0_align hpc3 hrun3 hsp3 htr3
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        unfold vecCapPtrDealloc
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := (blkPl_364).base + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · unfold chainPBHeadersAt; wp_steps
          refine SepWP.focus_weaken
            (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb)
            (by unfold chainPBHeadersAt; sep_focus) ?_
          wp_done
        · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx0_3, hx1_3⟩
          exact hep_dealloc s3 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc3 hrun3 hsp3 htr3 hx0_3 hx1_3

set_option maxHeartbeats 800000 in
theorem fromPb_join_err_tail_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 944#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx19 : s.readReg64 .x19 = 0#64) (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap)
    (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr) (hx24 : s.readReg64 .x24 = x.out)
    (hx25 : s.readReg64 .x25 = x.gPb.linksCap) (hx26 : s.readReg64 .x26 = x.gPb.linksPtr)
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ A H x s0
  have hep_dealloc := @fromPb_epilogue_dealloc_placed _ A H hdealloc x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  refine seq_clean (mid := (blkPl_364).base + 956#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.gPb.linksCap ∧
      sm.readReg64 .x26 = x.gPb.linksPtr ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (chainEpoch A) 112 x.gPb.linksPtr) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps_lscl (lsmpl.base 287)
    have hcall :=
      fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hchain_slice ‹LibsignalCodeLoaded lsmpl _›
    dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hcall
    wp_call hcall ⟨x.gPb.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx21_3, hx22_3, hx24_3, hx25_3, hx26_3, hx27_3⟩
    have hjoin3 :
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
          memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ⊢
          memRegion x.gPb.linksPtr (x.pb.links.length * 112) := by
      rw [← hsplit_len]
      exact memRegion_join_three_112 x.gPb.linksPtr convEpochs.length remPB.length
        (by rw [hsplit_len]; exact hlen_lt)
    refine SepWP.focus_weaken hjoin3 (by sep_focus) ?_
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := (blkPl_364).base + 980#64)
      (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x27 = 0#64) ?_ ?_
    · by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp3]; wp_done
    · rintro s4 hpc4 hrun4 ⟨hsp4, htr4, hx21_4, hx22_4, hx24_4, hx27_4⟩
      rw [memRegion_88_words4_rest x.out]
      wp_pull_exists
      unfold vecCapPtrDealloc
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := (blkPl_364).base + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · unfold joinScratchAt; wp_steps
          refine SepWP.focus_weaken
            (err_stateDecode_pack_words A x.out x.pb hfromPb_eq 0#64 sp0_val _ rfl)
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
            (by unfold joinScratchAt; sep_focus) ?_
          wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5⟩
          exact hep_ret s5 hsp0_align hpc5 hrun5 hsp5 htr5
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := (blkPl_364).base + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · unfold joinScratchAt; wp_steps
          refine SepWP.focus_weaken
            (err_stateDecode_pack_words A x.out x.pb hfromPb_eq 0#64 sp0_val _ rfl)
            (by sep_focus) ?_
          refine SepWP.focus_weaken
            (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
            (by unfold joinScratchAt; sep_focus) ?_
          wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5, hx0_5, hx1_5⟩
          exact hep_dealloc s5 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5

set_option maxHeartbeats 800000 in
theorem fromPb_join_err_840_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (remPB : List ChainEpochPB) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode)
    (hsplit_len : convEpochs.length + 1 + remPB.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx26 : s.readReg64 .x26 = x.gPb.linksPtr)
    (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have htail := @fromPb_join_err_tail_cl_placed _ A H hdealloc hchain_slice x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by
    have : convEpochs.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hconv_le_cap : convEpochs.length ≤ x.gPb.linksCap.toNat := by omega
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hcsel1 := csel_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel1_ult := csel_ult_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel2 := csel_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel2_ult := csel_ult_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
  have hcsel3 := csel_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
  have hcsel3_eq := csel_eq_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 944#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x19 = 0#64 ∧ sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧
      sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x24 = x.out ∧
      sm.readReg64 .x25 = x.gPb.linksCap ∧ sm.readReg64 .x26 = x.gPb.linksPtr ∧
      sm.readReg64 .x27 = 0#64) ?_ ?_
  · unfold joinScratchAt
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps_lscl (lsmpl.base 287)
    have hcall :=
      fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hchain_slice ‹LibsignalCodeLoaded lsmpl _›
    dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hcall
    wp_call hcall ⟨x.gPb.linksPtr, convEpochs⟩
    rw [hsp]; wp_done
  · rintro s2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hx19_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2⟩
    exact htail s2 convEpochs remPB sp0_val hcl2 hsp0_align hfromPb_eq hsplit_len hl_le hl_lt hn_lt hn_ne
      hpc2 hrun2 hsp2 htr2 hx19_2 hx21_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2

set_option maxHeartbeats 800000 in
theorem fromPb_join_err_cl_placed [LibsignalPlacement] {A : RustAlloc}
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
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (_hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx29 : s.readReg64 .fp = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 0#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (x.pb.links.length * 112))
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx27 : s.readReg64 .x27 = 0#64) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
        arrayAt (chainEpochPBAt A) 112
          (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remG.zip remPB) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h840 := @fromPb_join_err_840_cl_placed _ A H hdealloc hchain_slice x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hrem_lt : remPB.length * 112 < 2 ^ 63 := by
    have : remPB.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by
    have : convEpochs.length ≤ x.pb.links.length := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right 112 this) hlen_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hsub_rem := sub_links_rem_112 x.gPb.linksPtr convEpochs.length remPB.length
    x.pb.links.length hsplit_len
  have hsub_conv := sub_links_conv_112 x.gPb.linksPtr convEpochs.length
  have hdiv_rem := div_112_magic_eq hrem_lt
  have hdiv_rem_nat := div_112_magic_nat_eq hrem_lt
  have hdiv_conv := div_112_magic_eq hconv_lt
  have hdiv_conv_nat := div_112_magic_nat_eq hconv_lt
  refine SepWP.focus_weaken
    (arrayAt_chainEpochPBAt_entails_protoRepr A remG remPB
      (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) hrem_len)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (arrayAt_chainEpochAt_entails_unpinned A convG convEpochs x.gPb.linksPtr hconv_len)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
    (by sep_focus) ?_
  refine SepWP.focus_weaken
    (chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb) (by sep_focus) ?_
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 840#64)
    (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
      arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112)) 112 ∗
      memRegion (x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112)) (remPB.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x19 = 0#64 ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x26 = x.gPb.linksPtr ∧
      sm.readReg64 .x27 = 0#64) ?_ ?_
  · rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps_lscl (lsmpl.base 288)
    have hcall :=
      fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hproto_slice ‹LibsignalCodeLoaded lsmpl _›
    dsimp only [withMemEq, dropProtoEpochSliceSpec, ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hcall
    wp_call hcall ⟨x.gPb.linksPtr + BitVec.ofNat 64 ((convEpochs.length + 1) * 112), remPB⟩
    rw [hsp]; wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hx27_1⟩
    exact h840 s1 convEpochs remPB sp0_val hcl1 hsp0_align hfromPb_eq hsplit_len hl_le hl_lt hn_lt hn_ne
      hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx26_1 hx27_1

set_option maxHeartbeats 800000 in
theorem fromPb_join_params_none_tail_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State)
    (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 1100#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx19 : s.readReg64 .x19 = 0#64) (hx20 : s.readReg64 .x20 = x.gPb.linksPtr)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx25 : s.readReg64 .x25 = x.gPb.linksCap) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
        memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ A H x s0
  have hep_dealloc := @fromPb_epilogue_dealloc_placed _ A H hdealloc x s0
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  refine seq_clean (mid := (blkPl_364).base + 1112#64)
    (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
      memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .x20 = x.gPb.linksPtr ∧ sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧
      sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (chainEpoch A) 112 x.gPb.linksPtr) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps_lscl (lsmpl.base 287)
    have hcall :=
      fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hchain_slice ‹LibsignalCodeLoaded lsmpl _›
    dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hcall
    wp_call hcall ⟨x.gPb.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s3 hpc3 hrun3 ⟨hsp3, htr3, hx20_3, hx21_3, hx22_3, hx25_3⟩
    rw [hpb_len]
    refine SepWP.focus_weaken
      (linksRawAllocAt_combine_memRegion A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length hl_le hl_lt)
      (by sep_focus) ?_
    refine seq_clean (mid := (blkPl_364).base + 1136#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr) ?_ ?_
    · by_cases hc : x.gPb.linksCap = 0
      · have hcb : (x.gPb.linksCap == 0#64) = true := beq_iff_eq.mpr hc
        simp only [hcb, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hcb : (x.gPb.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hc
        have hpos : x.gPb.linksCap.toNat * 112 > 0 := by
          have : x.gPb.linksCap.toNat > 0 := Nat.pos_of_ne_zero (by
            intro hz; exact hc (BitVec.eq_of_toNat_eq (by simpa using hz)))
          omega
        have hlsl := cap_mul_112_shift_eq x.gPb.linksCap hl_lt
        simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        rw [stackAt_subStack_split_allocHook s0.sp]
        wp_steps
        wp_call hdealloc (x.gPb.linksPtr, x.gPb.linksCap.toNat * 112, 8)
        rw [hsp3]; wp_done
    · rintro s4 hpc4 hrun4 ⟨hsp4, htr4, hx21_4, hx22_4⟩
      unfold vecCapPtrDealloc
      refine SepWP.focus_weaken
        (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val) (by sep_focus) ?_
      by_cases hnr : x.gPb.nextRoot.cap = 0
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = true := beq_iff_eq.mpr hnr
        simp only [hnrb, ↓reduceIte, emp_sepConj, sepConj_emp]
        refine seq_clean (mid := (blkPl_364).base + 1140#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
        · wp_steps; wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5⟩
          exact hep_ret s5 hsp0_align hpc5 hrun5 hsp5 htr5
      · have hnrb : (x.gPb.nextRoot.cap == 0#64) = false := beq_eq_false_iff_ne.mpr hnr
        simp only [hnrb, Bool.false_eq_true, ↓reduceIte]
        refine seq_clean (mid := (blkPl_364).base + 1008#64)
          (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
            A.live x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat 1 ∗
            memRegion x.gPb.nextRoot.ptr x.gPb.nextRoot.cap.toNat ∗
            memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 192#64) chainFromPbSubStack)
          (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
            sm.readReg64 .x0 = x.gPb.nextRoot.ptr ∧ sm.readReg64 .x1 = x.gPb.nextRoot.cap) ?_ ?_
        · wp_steps; wp_done
        · rintro s5 hpc5 hrun5 ⟨hsp5, htr5, hx0_5, hx1_5⟩
          exact hep_dealloc s5 x.gPb.nextRoot.cap x.gPb.nextRoot.ptr
            hsp0_align hnr hn_lt hn_ne hpc5 hrun5 hsp5 htr5 hx0_5 hx1_5

set_option maxHeartbeats 800000 in
theorem fromPb_join_ok_840_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State) (dir : Direction)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hlinks : Chain.linksFromPb x.pb.links = .ok convEpochs)
    (hconv_len : convG.length = convEpochs.length) (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 840#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64) (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length)
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have hep_ret := @fromPb_epilogue_ret_placed _ A H x s0
  have hnone_tail := @fromPb_join_params_none_tail_cl_placed _ A H hdealloc hchain_slice x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by rw [hpb_len]; exact hlen_lt
  have hconv_le_cap : convEpochs.length ≤ x.gPb.linksCap.toNat := by rw [hpb_len]; exact hl_le
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  cases hp : x.pb.params with
  | some cp =>
    have hfromPb_eq : Chain.fromPb x.pb = .ok {
        dir := dir, currentEpoch := x.pb.currentEpoch, sendEpoch := x.pb.sendEpoch,
        nextRoot := x.pb.nextRoot, links := convEpochs, params := cp } :=
      chainFromPb_of_ok hdir hlinks hp
    rw [memRegion_88_words4_rest x.out, memRegion_56_split_chainTail x.out]
    wp_pull_exists
    refine seq_clean (mid := (blkPl_364).base + 1140#64)
      (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗ A.pool ∗
        memRegion (s0.sp - 192#64) 96 ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0) ?_ ?_
    · unfold chainPBHeadersAt optChainParamsPBAt joinScratchAt
      rw [hp]; dsimp only
      wp_steps
      have hhdr :
          (x.pbPtr ↦₆₄ x.gPb.linksCap) ∗ ((x.pbPtr + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.pbPtr + 16#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.pbPtr + 24#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.pbPtr + 32#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.pbPtr + 40#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.pbPtr + 48#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.pbPtr + 56#64) ↦₆₄ x.pb.sendEpoch) ∗
            (((x.pbPtr + 64#64) ↦₃₂ 1#32) ∗ ((x.pbPtr + 64#64 + 4#64) ↦₃₂ cp.maxJump) ∗
              ((x.pbPtr + 64#64 + 8#64) ↦₃₂ cp.maxOooKeys)) ∗
            ((x.pbPtr + 76#64) ↦₃₂ x.pb.direction) ⊢ memRegion x.pbPtr 80 := by
        have := chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb
        unfold chainPBHeadersAt optChainParamsPBAt at this; rw [hp] at this; exact this
      refine SepWP.focus_weaken hhdr (by sep_focus) ?_
      have hpack :
          (x.out ↦₆₄ x.gPb.linksCap) ∗ ((x.out + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.out + 16#64) ↦₆₄ 0#64) ∗ ((x.out + 24#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.out + 32#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.out + 40#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.out + 48#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.out + 56#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.out + 64#64) ↦₆₄ x.pb.sendEpoch) ∗
            ((x.out + 72#64) ↦₃₂ cp.maxJump) ∗ ((x.out + 76#64) ↦₃₂ cp.maxOooKeys) ∗
            ((x.out + 80#64) ↦₃₂ x.pb.direction) ∗ memRegion (x.out + 84#64) 4 ∗
            arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
            linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
            vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ⊢
            chainResultAt A x.out (Chain.fromPb x.pb) := by
        rw [hfromPb_eq, ← hdir_i32, ← hpb_len]
        exact chainResultAt_ok_pack A x.out x.gPb.linksCap x.gPb.linksPtr
          x.gPb.nextRoot.cap x.gPb.nextRoot.ptr convG convEpochs x.pb.nextRoot
          x.pb.currentEpoch x.pb.sendEpoch cp dir
          hconv_len hconv_le_cap hl_lt hl_ne hn_le hn_lt hn_ne
      refine SepWP.focus_weaken hpack (by sep_focus) ?_
      refine SepWP.focus_weaken
        (joinScratchAt_entails_memRegion_96 s0 x.gPb x.pb sp0_val)
        (by unfold joinScratchAt; sep_focus) ?_
      wp_done
    · rintro s2 hpc2 hrun2 ⟨hsp2, htr2⟩
      exact hep_ret s2 hsp0_align hpc2 hrun2 hsp2 htr2
  | none =>
    have hfromPb_eq : Chain.fromPb x.pb = .error .stateDecode :=
      chainFromPb_of_params_none hdir hlinks hp
    have hcsel1 := csel_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel1_ult := csel_ult_sub_zero_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel2 := csel_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel2_ult := csel_ult_min_eq_of_le convEpochs.length x.gPb.linksCap hconv_le_cap
    have hcsel3 := csel_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
    have hcsel3_eq := csel_eq_zero_if_ptr_eq x.gPb.linksPtr convEpochs.length hconv_lt
    have hcsel1_pb := csel_sub_zero_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel1_ult_pb := csel_ult_sub_zero_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel2_pb := csel_min_eq_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel2_ult_pb := csel_ult_min_eq_of_le x.pb.links.length x.gPb.linksCap hl_le
    have hcsel3_pb := csel_zero_if_ptr_eq x.gPb.linksPtr x.pb.links.length hlen_lt
    have hcsel3_eq_pb := csel_eq_zero_if_ptr_eq x.gPb.linksPtr x.pb.links.length hlen_lt
    refine SepWP.focus_weaken
      (arrayAt_chainEpochAt_entails_unpinned A convG convEpochs x.gPb.linksPtr hconv_len)
      (by sep_focus) ?_
    refine SepWP.focus_weaken
      (vecU8BufAt_entails_dealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot hn_le hn_lt)
      (by sep_focus) ?_
    refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 1044#64)
      (P_mid := memRegion x.out 88 ∗ memRegion x.pbPtr 80 ∗
        arrayAt (chainEpoch A) 112 x.gPb.linksPtr convEpochs ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
        sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
        sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
        sm.readReg64 .x24 = x.out) ?_ ?_
    · unfold chainPBHeadersAt optChainParamsPBAt
      rw [hp]; dsimp only
      wp_steps
      have hhdr :
          (x.pbPtr ↦₆₄ x.gPb.linksCap) ∗ ((x.pbPtr + 8#64) ↦₆₄ x.gPb.linksPtr) ∗
            ((x.pbPtr + 16#64) ↦₆₄ BitVec.ofNat 64 x.pb.links.length) ∗
            ((x.pbPtr + 24#64) ↦₆₄ x.gPb.nextRoot.cap) ∗ ((x.pbPtr + 32#64) ↦₆₄ x.gPb.nextRoot.ptr) ∗
            ((x.pbPtr + 40#64) ↦₆₄ BitVec.ofNat 64 x.pb.nextRoot.length) ∗
            ((x.pbPtr + 48#64) ↦₆₄ x.pb.currentEpoch) ∗ ((x.pbPtr + 56#64) ↦₆₄ x.pb.sendEpoch) ∗
            (((x.pbPtr + 64#64) ↦₃₂ 0#32) ∗ memRegion (x.pbPtr + 64#64 + 4#64) 8) ∗
            ((x.pbPtr + 76#64) ↦₃₂ x.pb.direction) ⊢ memRegion x.pbPtr 80 := by
        have := chainPBHeadersAt_entails_memRegion_80 x.pbPtr x.gPb x.pb
        unfold chainPBHeadersAt optChainParamsPBAt at this; rw [hp] at this; exact this
      refine SepWP.focus_weaken hhdr (by sep_focus) ?_
      wp_done
    · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1⟩
      rw [memRegion_88_words4_rest x.out]
      wp_pull_exists
      refine fromPb_seq_clean_lscl hcl1 (mid := (blkPl_364).base + 1100#64)
        (P_mid := chainResultAt A x.out (Chain.fromPb x.pb) ∗ memRegion x.pbPtr 80 ∗
          memRegion x.gPb.linksPtr (convEpochs.length * 112) ∗
          linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
          vecCapPtrDealloc A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr ∗ A.pool ∗
          joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 192#64) chainFromPbSubStack)
        (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .x19 = 0#64 ∧ sm.readReg64 .x20 = x.gPb.linksPtr ∧
          sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
          sm.readReg64 .x25 = x.gPb.linksCap) ?_ ?_
      · unfold joinScratchAt
        rw [stackAt_subStack_split_dropStack32 s0.sp]
        wp_steps_lscl (lsmpl.base 287)
        refine SepWP.focus_weaken
          (err_stateDecode_pack_words A x.out x.pb hfromPb_eq _ _ _ (bitvec_low_byte_clear_zero _))
          (by sep_focus) ?_
        have hcall :=
          fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hchain_slice ‹LibsignalCodeLoaded lsmpl _›
        dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hcall
        wp_call hcall ⟨x.gPb.linksPtr, convEpochs⟩
        rw [hsp1]; wp_done
      · rintro s2 hpc2 hrun2 hcl2 ⟨hsp2, htr2, hx19_2, hx20_2, hx21_2, hx22_2, hx25_2⟩
        exact hnone_tail s2 convEpochs sp0_val hcl2 hsp0_align hpb_len hl_le hl_lt hn_lt hn_ne
          hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2 hx21_2 hx22_2 hx25_2

set_option maxHeartbeats 800000 in
theorem fromPb_join_ok_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hchain_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hproto_slice : subroutine_ok ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 288) (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A)))
    (x : ChainFromPbCall) (s0 s : State) (dir : Direction)
    (convG : List ChainEpochGhost) (convEpochs : List ChainEpoch) (sp0_val : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hdir : Direction.fromI32? x.pb.direction = some dir) (hdir_i32 : dir.toI32 = x.pb.direction)
    (hlinks : Chain.linksFromPb x.pb.links = .ok convEpochs)
    (hconv_len : convG.length = convEpochs.length) (hpb_len : convEpochs.length = x.pb.links.length)
    (hl_le : x.pb.links.length ≤ x.gPb.linksCap.toNat)
    (hl_lt : x.gPb.linksCap.toNat * 112 < 2 ^ 63) (hl_ne : x.gPb.linksPtr ≠ 0)
    (hn_le : x.pb.nextRoot.length ≤ x.gPb.nextRoot.cap.toNat)
    (hn_lt : x.gPb.nextRoot.cap.toNat < 2 ^ 63) (hn_ne : x.gPb.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_364).base + 792#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 192#64) (htr : TraceCalleeSaved s s0)
    (hx29 : s.readReg64 .fp = s0.sp - 96#64)
    (hx0 : s.readReg64 .x0 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx11 : s.readReg64 .x11 = x.gPb.linksPtr) (hx19 : s.readReg64 .x19 = 1#64)
    (hx20 : s.readReg64 .x20 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx21 : s.readReg64 .x21 = x.gPb.nextRoot.cap) (hx22 : s.readReg64 .x22 = x.gPb.nextRoot.ptr)
    (hx23 : s.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))
    (hx24 : s.readReg64 .x24 = x.out) (hx25 : s.readReg64 .x25 = x.pbPtr) :
    SepWP ((blkPC_364).rebase (blkPl_364).base H) (s0.readReg64 .lr) s
      (memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
        arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
        linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
        vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
        joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 192#64) chainFromPbSubStack)
      (fromPbRetPost A x s0) := by
  have h840 := @fromPb_join_ok_840_cl_placed _ A H hdealloc hchain_slice x s0
  have hlen_lt : x.pb.links.length * 112 < 2 ^ 63 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right 112 hl_le) hl_lt
  have hconv_lt : convEpochs.length * 112 < 2 ^ 63 := by rw [hpb_len]; exact hlen_lt
  have hfsp_align : ((s0.sp - 192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 192#64 hsp0_align (by decide)
  have hsub_conv := sub_links_conv_112 x.gPb.linksPtr convEpochs.length
  have hdiv_conv := div_112_magic_eq hconv_lt
  have hdiv_conv_nat := div_112_magic_nat_eq hconv_lt
  have hsub_pb := sub_links_conv_112 x.gPb.linksPtr x.pb.links.length
  have hdiv_pb := div_112_magic_eq hlen_lt
  have hdiv_pb_nat := div_112_magic_nat_eq hlen_lt
  refine fromPb_seq_clean_lscl hcl (mid := (blkPl_364).base + 840#64)
    (P_mid := memRegion x.out 88 ∗ chainPBHeadersAt x.pbPtr x.gPb x.pb ∗
      arrayAt (chainEpochAt A) 112 x.gPb.linksPtr (convG.zip convEpochs) ∗
      linksRawAllocAt A x.gPb.linksCap x.gPb.linksPtr x.pb.links.length ∗
      vecU8BufAt A x.gPb.nextRoot.cap x.gPb.nextRoot.ptr x.pb.nextRoot ∗ A.pool ∗
      joinScratchAt s0 x.gPb x.pb sp0_val ∗ calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 192#64) chainFromPbSubStack)
    (Q := fun sm => sm.sp = s0.sp - 192#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧ sm.readReg64 .x19 = 1#64 ∧
      sm.readReg64 .x20 = BitVec.ofNat 64 convEpochs.length ∧
      sm.readReg64 .x21 = x.gPb.nextRoot.cap ∧ sm.readReg64 .x22 = x.gPb.nextRoot.ptr ∧
      sm.readReg64 .x23 = x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112) ∧
      sm.readReg64 .x24 = x.out ∧ sm.readReg64 .x25 = x.pbPtr) ?_ ?_
  · refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool A (fun ep addr => ProtoRepr.chainEpochPBAt A addr ep) 112
        (x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112))) (by sep_focus) ?_
    rw [stackAt_subStack_split_dropStack32 s0.sp]
    wp_steps_lscl (lsmpl.base 288)
    have hcall :=
      fromPb_subroutine_ok_withMemEq_of_withLsCodeLoaded hproto_slice ‹LibsignalCodeLoaded lsmpl _›
    dsimp only [withMemEq, dropProtoEpochSliceSpec, ProtoRepr.chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hcall
    wp_call hcall ⟨x.gPb.linksPtr + BitVec.ofNat 64 (convEpochs.length * 112), []⟩
    rw [hsp, memRegion_zero, emp_sepConj]; wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1⟩
    exact h840 s1 dir convG convEpochs sp0_val hcl1 hsp0_align hdir hdir_i32 hlinks hconv_len hpb_len
      hl_le hl_lt hl_ne hn_le hn_lt hn_ne hpc1 hrun1 hsp1 htr1 hfp1 hx19_1 hx20_1 hx21_1 hx22_1
      hx23_1 hx24_1 hx25_1

end CryptoVerification.SpqrV1.ChainProofs
