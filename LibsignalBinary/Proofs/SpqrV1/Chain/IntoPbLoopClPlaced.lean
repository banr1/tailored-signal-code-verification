/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoop
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbDecodes
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Code-Loaded `[LibsignalPlacement]` Epilogue for `<spqr::chain::Chain>::into_pb` (Block `365`)

Code-loaded `[LibsignalPlacement]` epilogue (`chainIntoPb_epilogue_cl_placed`) and
`withLsCodeLoaded` sequencing helpers for Block `365`, taking
`withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)` on cross-block callee `287`.
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

/-- Specialize a `withLsCodeLoaded` `subroutine_ok` contract at a call site whose memory `m`
    already satisfies `LibsignalCodeLoaded lsmpl m` (`withMemEq m spec`). -/
theorem chain_subroutine_ok_withMemEq_of_withLsCodeLoaded [LibsignalPlacement] {α : Type}
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

/-- Introduce a `withLsCodeLoaded lsmpl spec` `subroutine_ok` contract by fixing initial memory `m`
    with `LibsignalCodeLoaded lsmpl m`. -/
theorem chain_subroutine_ok_withLsCodeLoaded_intro [LibsignalPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ m : Memory, LibsignalCodeLoaded lsmpl m →
      subroutine_ok prog entry (withMemEq m spec)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl spec) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  obtain ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  refine (h s0.mem hcl).mono_outcome x R s0 hpc hrun ?_ halign fun _ hout => hout
  dsimp only [withMemEq]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨rfl, hpre'⟩

/-- `seq_clean` variant threading `LibsignalCodeLoaded lsmpl ·.mem` across `mid`. -/
theorem chain_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` epilogue of `<spqr::chain::Chain>::into_pb` at `+820`,
    using `withLsCodeLoaded lsmpl` for cross-block callee `287`. -/
theorem chainIntoPb_epilogue_cl_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A)))
    (x : ChainIntoPbCall) (s0 s : State) (newLinksPtr : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63)
    (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hl_new_ne : newLinksPtr ≠ 0)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63)
    (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = 0#64)
    (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = newLinksPtr)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗
        chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost A x s0) := by
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  have hdrop_emp1 := pool_entails_empty_arrayAt_pool_intoPb A (chainEpoch A) 112 x.gChain.linksPtr
  refine chain_seq_clean_lscl hcl (mid := (blkPl_365).base + 840#64)
    (P_mid := memRegion x.out 80 ∗
      chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A) 112 newLinksPtr
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool ∗
      intoPbScratchAt s0 x.gChain x.chain ∗
      calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
      sm.readReg64 .x23 = 0#64 ∧
      sm.readReg64 .x24 = newLinksPtr ∧
      sm.readReg64 .x25 = x.chain.sendEpoch ∧
      sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      sm.readReg64 .x27 = x.chain.currentEpoch ∧
      sm.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · refine SepWP.focus_weaken hdrop_emp1 (by sep_focus) ?_
    unfold intoPbScratchAt
    wp_steps_lscl (lsmpl.base 287)
    have hdrop_call :=
      chain_subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop ‹LibsignalCodeLoaded lsmpl _›
    dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hdrop_call
    wp_call hdrop_call ⟨x.gChain.linksPtr, []⟩
    rw [hsp, memRegion_zero, emp_sepConj]
    wp_done
  · rintro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
    refine chain_seq_clean_lscl hcl1 (mid := (blkPl_365).base + 852#64)
      (P_mid := memRegion x.out 80 ∗
        chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x24 = newLinksPtr ∧
        sm.readReg64 .x25 = x.chain.sendEpoch ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.chain.currentEpoch ∧
        sm.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · refine SepWP.focus_weaken hdrop_emp1 (by sep_focus) ?_
      wp_steps_lscl (lsmpl.base 287)
      have hdrop_call :=
        chain_subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop ‹LibsignalCodeLoaded lsmpl _›
      dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hdrop_call
      wp_call hdrop_call ⟨x.gChain.linksPtr, []⟩
      rw [hsp1, memRegion_zero, emp_sepConj]
      wp_done
    · rintro s2 hpc2 hrun2 _hcl2 ⟨hsp2, htr2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2⟩
      refine seq_clean (mid := (blkPl_365).base + 880#64)
        (P_mid := memRegion x.out 80 ∗
          chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
          vecU8BufAt A x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool ∗
          intoPbScratchAt s0 x.gChain x.chain ∗
          calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32)
        (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x24 = newLinksPtr ∧
          sm.readReg64 .x25 = x.chain.sendEpoch ∧
          sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          sm.readReg64 .x27 = x.chain.currentEpoch) ?_ ?_
      · unfold intoPbScratchAt
        by_cases hcap : x.gChain.linksCap = 0
        · have hcapb : (x.gChain.linksCap == 0#64) = true := beq_iff_eq.mpr hcap
          simp only [hcapb, ↓reduceIte, emp_sepConj, sepConj_emp]
          wp_steps
          wp_done
        · have hcapb : (x.gChain.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
          have hcap_pos : x.gChain.linksCap.toNat * 112 > 0 := by
            have hpos := BitVec.toNat_pos_of_ne_zero hcap; omega
          have hsz_bv := cap_mul_112_shift_eq x.gChain.linksCap hl_cap_lt
          have hsplit_stack := stackAt_dropStack32_split_allocHook (s0.sp - 288#64)
          simp only [hcapb, Bool.false_eq_true, ↓reduceIte]
          rw [hsplit_stack]
          wp_steps
          wp_call hdealloc (x.gChain.linksPtr, x.gChain.linksCap.toNat * 112, 8)
          rw [hsp2, ← hsplit_stack]
          wp_done
      · rintro sm hpcm hrunm ⟨hspm, htrm, hfpm, hx19m, hx20m, hx21m, hx22m, hx24m, hx25m, hx26m, hx27m⟩
        rw [memRegion_80_split_out x.out]
        wp_pull_exists
        unfold chainHeaderCellsAt calleeSavedFromPbAt
        wp_steps
        refine SepWP.focus_weaken
          (restore_stack_chainIntoPb s0 x.gChain x.chain)
          (by unfold calleeSavedFromPbAt; sep_focus) ?_
        refine SepWP.focus_weaken
          (chainHeaderCellsAt_entails_memRegion_88 x.chainPtr x.gChain x.chain)
          (by unfold chainHeaderCellsAt; sep_focus) ?_
        refine SepWP.focus_weaken
          (Entails.trans
            (chainPBAt_pack_out A x.out newLinksPtr x.gChain x.chain hlen hl_new_lt hl_new_ne hn1 hn2 hn3)
            (chainPBAt_entails_chainPBIntoPinnedAt A x.out newLinksPtr x.gChain x.chain))
          (by sep_focus) ?_
        unfold intoPbPinnedRetPost
        wp_done

end CryptoVerification.SpqrV1.ChainProofs
