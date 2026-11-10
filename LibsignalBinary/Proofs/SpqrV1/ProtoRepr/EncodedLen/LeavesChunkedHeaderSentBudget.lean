/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved` Placed Verification of `Chunked.{Ct1Sampled,HeaderSent}::encoded_len`

Block-subset `CallPinnedEncLenAtF` bridges and `[LibsignalPlacement]` `subroutine_ok` theorems with
`VmPreserved` for `V1State.Chunked.Ct1Sampled::encoded_len` (Blocks `179`, `407`) and
`V1State.Chunked.HeaderSent::encoded_len` (Blocks `188`, `414`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded
   blkPC_179 blkPl_179 blkPC_407 blkPl_407 blkPC_188 blkPl_188 blkPC_414 blkPl_414)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.SpqrV1.ProtoRepr
  (PinnedEncLenGhost FrozenInv SepWPpF CallPinnedEncLenAtF
   ct1Sampled_entry_pinned_wp_p2 headerSent_entry_pinned_wp_p2
   chunkedHeaderSentPBAt_eq_exists_pinned bl_reloc_target_eq)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen (EpochEncLenCalleeSaved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved subroutine_ok_of_withVmPreserved
   LsBlocksCodeLoaded withLsBlocksCodeLoaded
   ls_subroutine_ok_of_block_in ls_subroutine_ok_blocks_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget
  (chunkedCt1SampledEncodedLenPinnedSpec chunkedHeaderSentEncodedLenPinnedSpec
   chunkedHeaderSentEncodedLenSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedBudget
  (chunkedCt1SampledEncodedLen_lscl_ok_of_pinned
   ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOkExt
   ChunkedCt1SampledEncodedLenLocal1PlacedOkExt
   ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOk
   ChunkedCt1SampledEncodedLenLocal1PlacedOk
   ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOkExt
   ChunkedCt1SampledEncodedLenLocal2PlacedOkExt
   ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOk
   ChunkedCt1SampledEncodedLenLocal2PlacedOk)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyBudget
  (polynomialEncoderEncodedLen_local1_pinned_placed_ok_hooks
   polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks
   polynomialDecoderEncodedLen_local1_pinned_placed_ok_hooks
   polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71Budget
  (ekSentEncodedLen_local1_pinned_placed_ok_hooks
   ekSentEncodedLen_local2_pinned_placed_ok_hooks)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93Budget
  (ct1SentEncodedLen_local1_pinned_placed_ok_hooks
   ct1SentEncodedLen_local2_pinned_placed_ok_hooks)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

/-! ## 1. Block-Subset `SepWPpF` & `CallPinnedEncLenAtF` Bridges -/

local instance instFrozenInvLsBlocks (blks : List Nat) (pl : MultiPlacement) :
    FrozenInv (LsBlocksCodeLoaded blks pl) where
  keeps h hkf := h.of_keepsFrozen hkf

private theorem subroutine_ok_of_sepWPpF_blocks {α : Type} {prog : Program} {entry : BitVec 64}
    {blks : List Nat} {pl : MultiPlacement} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State), s0.pc = entry → s0.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      ∃ P Fr : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
        SepWPpF (LsBlocksCodeLoaded blks pl) prog (s0.readReg64 Reg.lr) s0 P
          (fun sf P_f => ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.post x s0 sf ∗ R)) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ spec.onPanic x s0 sf ∗ R))) :
    subroutine_ok prog entry (withLsBlocksCodeLoaded blks pl spec) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsBlocksCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre'⟩
  obtain ⟨P, Fr, hm, hwp⟩ := h x R s0 hpc hrun hpre' hsp
  refine ⟨P, Fr, hm, ?_⟩
  have hwp0 := hwp hcl0
  intro Fr' hm' hL
  obtain ⟨sf, hsteps, hout⟩ := hwp0 Fr' hm' hL
  refine ⟨sf, hsteps, ?_⟩
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, ⟨_, hq⟩⟩ | hpan | hoom
  · exact Or.inl ⟨hpcf, hrunf, P_f, hmf, hq⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hoom)

private theorem callPinnedEncLenAtF_of_bl_blocks [LibsignalPlacement]
    {callerProg calleeProg : Program} {blks : List Nat} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {k : Nat}
    {Ghost Model : Type} {repr : Ghost → BitVec 64 → Model → SepProp}
    {encLen : Model → Nat} {stackSz : Nat} {spec : Spec (PinnedEncLenGhost Ghost Model)}
    (hspec_pre : ∀ x s, spec.pre x s =
      (⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗ repr x.g x.a x.m ∗ stackAt s.sp stackSz))
    (hspec_post : ∀ x s0 sf, spec.post x s0 sf =
      (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
        repr x.g x.a x.m ∗ stackAt s0.sp stackSz))
    (hspec_panic : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝)
    (hspec_exit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hj : j ∈ blks)
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) spec)
    (hfetch : callerProg.fetch (entry + BitVec.ofNat 64 k) =
      some (.bl (lsmpl.base j - entry - BitVec.ofNat 64 k)) := by simp only [arm64_norm])
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded blks lsmpl) callerProg entry k repr encLen stackSz := by
  intro ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound hcont hcl0
  subst hsp
  have htarget : entry + BitVec.ofNat 64 k + (lsmpl.base j - entry - BitVec.ofNat 64 k) =
      lsmpl.base j :=
    bl_reloc_target_eq entry (BitVec.ofNat 64 k) (lsmpl.base j)
  have hcall : subroutine_ok callerProg (lsmpl.base j) (withLsBlocksCodeLoaded blks lsmpl spec) :=
    ls_subroutine_ok_of_block_in (callerProg := callerProg) hj hcallee
  apply SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl0
    (mid := entry + BitVec.ofNat 64 (k + 4))
  wp_steps
  have hlr_eq : entry + BitVec.ofNat 64 k + 4#64 = entry + BitVec.ofNat 64 (k + 4) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine SepWP.call_subroutine_frame (x := ⟨a, g, m⟩) (F := F)
    (ret_pc := entry + BitVec.ofNat 64 (k + 4)) hcall
    (by simp_all) (by simp_all)
    (by simp only [State.spAligned, beq_iff_eq]; simp_all)
    (by simp_all) ?_ ?_ ?_ ?_ (h_oom := ?_)
  · intro R hm
    dsimp only [withLsBlocksCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm (spec.pre _ _) ⌜LsBlocksCodeLoaded blks lsmpl _⌝,
      satisfies_pure_sepConj]
    refine ⟨by simp_all, ?_⟩
    rw [hspec_pre]
    simp only [sepConj_assoc, satisfies_pure_sepConj, arm64_norm]
    refine ⟨⟨by simp_all, hbound⟩, ?_⟩
    convert hm using 1
    · sep_ac_rfl
    · rfl
  · intro R' sf _ hpan
    dsimp only [withLsBlocksCodeLoaded] at hpan
    rw [hspec_panic, satisfies_pure_sepConj] at hpan
    exact hpan.1
  · intro R' code sf _ hex
    dsimp only [withLsBlocksCodeLoaded] at hex
    rw [hspec_exit, satisfies_pure_sepConj] at hex
    exact hex.1
  · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
    dsimp only [withLsBlocksCodeLoaded]
    rw [hspec_post]
    simp only [arm64_norm] at hsp_sf ⊢
    apply SepWP.weaken_pre
      (P' := ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen m) ∧ sf.trace = s.trace⌝ ∗
        ((repr g a m ∗ stackAt s.sp stackSz) ∗ F))
    · exact Entails.of_eq (by sep_ac_rfl)
    · apply SepWP.pure_elim
      rintro ⟨hx0_sf, htr_sf⟩
      apply SepWP.done hpc_sf hrun_sf
      have ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hv⟩ := hcs_sf
      have hcs_saved : EpochEncLenCalleeSaved s sf := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
      have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := by
        simp_all
      intro hcl_sf
      exact hcont sf hpc_sf hrun_sf hsp_sf htr_sf hx0_sf hcs_saved hfp_sf hcl_sf
  · intro R' sf _ hoom
    dsimp only [withLsBlocksCodeLoaded] at hoom
    rw [hspec_oom] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Placed Proofs for `Chunked.Ct1Sampled::encoded_len` (Blocks `179`, `407`) -/

theorem chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_179).rebase (blkPl_179).base H)
      (blkPl_179).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenPinnedSpec A)) := by
  refine ls_subroutine_ok_blocks_vmPreserved
    (progQ := (blkPC_179).rebase (blkPl_179).base (hooksException H))
    (blks := [179, 180, 173, 186]) (i := 179)
    (by decide) (by decide) (by decide +kernel) (hok := subroutine_ok_of_sepWPpF_blocks ?_)
  refine ct1Sampled_entry_pinned_wp_p2 (LsBlocksCodeLoaded [179, 180, 173, 186] lsmpl) _ A _
    (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (ct1SentEncodedLen_local1_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialEncoderEncodedLen_local1_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialDecoderEncodedLen_local1_pinned_placed_ok_hooks A (hooksException H)))

theorem chunkedCt1SampledEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_179).rebase (blkPl_179).base H)
      (blkPl_179).base
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget.chunkedCt1SampledEncodedLenSpec A)) :=
  chunkedCt1SampledEncodedLen_lscl_ok_of_pinned
    (chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_hooks A H)

theorem chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOkExt A ext :=
  chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem chunkedCt1SampledEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    ChunkedCt1SampledEncodedLenLocal1PlacedOkExt A ext :=
  chunkedCt1SampledEncodedLen_lscl_ok_of_pinned
    (chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem chunkedCt1SampledEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChunkedCt1SampledEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chunkedCt1SampledEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChunkedCt1SampledEncodedLenLocal1PlacedOk C A ctl abs :=
  chunkedCt1SampledEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_407).rebase (blkPl_407).base H)
      (blkPl_407).base (withLsCodeLoaded lsmpl (chunkedCt1SampledEncodedLenPinnedSpec A)) := by
  refine ls_subroutine_ok_blocks_vmPreserved
    (progQ := (blkPC_407).rebase (blkPl_407).base (hooksException H))
    (blks := [407, 408, 401, 413]) (i := 407)
    (by decide) (by decide) (by decide +kernel) (hok := subroutine_ok_of_sepWPpF_blocks ?_)
  refine ct1Sampled_entry_pinned_wp_p2 (LsBlocksCodeLoaded [407, 408, 401, 413] lsmpl) _ A _
    (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (ct1SentEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))

theorem chunkedCt1SampledEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_407).rebase (blkPl_407).base H)
      (blkPl_407).base
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsChunkedV1Budget.chunkedCt1SampledEncodedLenSpec A)) :=
  chunkedCt1SampledEncodedLen_lscl_ok_of_pinned
    (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_hooks A H)

theorem chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOkExt A ext :=
  chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem chunkedCt1SampledEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    ChunkedCt1SampledEncodedLenLocal2PlacedOkExt A ext :=
  chunkedCt1SampledEncodedLen_lscl_ok_of_pinned
    (chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem chunkedCt1SampledEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChunkedCt1SampledEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  chunkedCt1SampledEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chunkedCt1SampledEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChunkedCt1SampledEncodedLenLocal2PlacedOk C A ctl abs :=
  chunkedCt1SampledEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## 3. Unpinning Bridges, Propositions & Placed Proofs for `Chunked.HeaderSent::encoded_len` (Blocks `188`, `414`) -/

theorem chunkedHeaderSentEncodedLen_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (chunkedHeaderSentEncodedLenPinnedSpec A)) :
    subroutine_ok prog entry (chunkedHeaderSentEncodedLenSpec A) := by
  refine subroutine_ok_outcome_intro fun ⟨a, m⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [chunkedHeaderSentEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLenSpec,
    chunkedHeaderSentPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [chunkedHeaderSentEncodedLenPinnedSpec, chunkedHeaderSentEncodedLenSpec,
      withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLenSpec,
      chunkedHeaderSentPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem chunkedHeaderSentEncodedLen_lscl_ok_of_pinned {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded pl (chunkedHeaderSentEncodedLenPinnedSpec A))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (chunkedHeaderSentEncodedLenSpec A)) := by
  refine subroutine_ok_outcome_intro fun ⟨a, m⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded, chunkedHeaderSentEncodedLenSpec, withVmPreserved] at hpre
  simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLenSpec,
    chunkedHeaderSentPBAt_eq_exists_pinned,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, chunkedHeaderSentEncodedLenPinnedSpec,
      chunkedHeaderSentEncodedLenSpec, withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    simp only [CryptoVerification.SpqrV1.ProtoRepr.chunkedHeaderSentEncodedLenSpec,
      chunkedHeaderSentPBAt_eq_exists_pinned,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

def ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_188).rebase (blkPl_188).base (Rust.withPanics ext))
    (blkPl_188).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenPinnedSpec A))

def ChunkedHeaderSentEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_188).rebase (blkPl_188).base (Rust.withPanics ext))
    (blkPl_188).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenSpec A))

def ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChunkedHeaderSentEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedHeaderSentEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_414).rebase (blkPl_414).base (Rust.withPanics ext))
    (blkPl_414).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenPinnedSpec A))

def ChunkedHeaderSentEncodedLenLocal2PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_414).rebase (blkPl_414).base (Rust.withPanics ext))
    (blkPl_414).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenSpec A))

def ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChunkedHeaderSentEncodedLenLocal2PlacedOk [LibsignalPlacement] (C : Crypto)
    (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChunkedHeaderSentEncodedLenLocal2PlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_188).rebase (blkPl_188).base H)
      (blkPl_188).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenPinnedSpec A)) := by
  refine ls_subroutine_ok_blocks_vmPreserved
    (progQ := (blkPC_188).rebase (blkPl_188).base (hooksException H))
    (blks := [188, 189, 173, 186]) (i := 188)
    (by decide) (by decide) (by decide +kernel) (hok := subroutine_ok_of_sepWPpF_blocks ?_)
  refine headerSent_entry_pinned_wp_p2 (LsBlocksCodeLoaded [188, 189, 173, 186] lsmpl) _ A _
    (Or.inr ⟨inst, hooksException H, Or.inl ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (ekSentEncodedLen_local1_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialEncoderEncodedLen_local1_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialDecoderEncodedLen_local1_pinned_placed_ok_hooks A (hooksException H)))

theorem chunkedHeaderSentEncodedLen_local1_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_188).rebase (blkPl_188).base H)
      (blkPl_188).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenSpec A)) :=
  chunkedHeaderSentEncodedLen_lscl_ok_of_pinned
    (chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_hooks A H)

theorem chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOkExt A ext :=
  chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem chunkedHeaderSentEncodedLen_local1_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    ChunkedHeaderSentEncodedLenLocal1PlacedOkExt A ext :=
  chunkedHeaderSentEncodedLen_lscl_ok_of_pinned
    (chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext A ext)

theorem chunkedHeaderSentEncodedLen_local1_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChunkedHeaderSentEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chunkedHeaderSentEncodedLen_local1_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChunkedHeaderSentEncodedLenLocal1PlacedOk C A ctl abs :=
  chunkedHeaderSentEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_hooks [inst : LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_414).rebase (blkPl_414).base H)
      (blkPl_414).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenPinnedSpec A)) := by
  refine ls_subroutine_ok_blocks_vmPreserved
    (progQ := (blkPC_414).rebase (blkPl_414).base (hooksException H))
    (blks := [414, 415, 401, 413]) (i := 414)
    (by decide) (by decide) (by decide +kernel) (hok := subroutine_ok_of_sepWPpF_blocks ?_)
  refine headerSent_entry_pinned_wp_p2 (LsBlocksCodeLoaded [414, 415, 401, 413] lsmpl) _ A _
    (Or.inr ⟨inst, hooksException H, Or.inr ⟨rfl, rfl⟩⟩) ?_ ?_ ?_
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (ekSentEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialEncoderEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))
  · exact callPinnedEncLenAtF_of_bl_blocks (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (by decide)
      (subroutine_ok_of_withVmPreserved
        (polynomialDecoderEncodedLen_local2_pinned_placed_ok_hooks A (hooksException H)))

theorem chunkedHeaderSentEncodedLen_local2_placed_ok_hooks [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_414).rebase (blkPl_414).base H)
      (blkPl_414).base (withLsCodeLoaded lsmpl (chunkedHeaderSentEncodedLenSpec A)) :=
  chunkedHeaderSentEncodedLen_lscl_ok_of_pinned
    (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_hooks A H)

theorem chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOkExt A ext :=
  chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_hooks A (Rust.withPanics ext)

theorem chunkedHeaderSentEncodedLen_local2_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (ext : String → Option (State → State)) :
    ChunkedHeaderSentEncodedLenLocal2PlacedOkExt A ext :=
  chunkedHeaderSentEncodedLen_lscl_ok_of_pinned
    (chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A ext)

theorem chunkedHeaderSentEncodedLen_local2_pinned_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChunkedHeaderSentEncodedLenLocal2PinnedPlacedOk C A ctl abs :=
  chunkedHeaderSentEncodedLen_local2_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem chunkedHeaderSentEncodedLen_local2_placed_ok [LibsignalPlacement]
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (abs : String → Option (State → State)) :
    ChunkedHeaderSentEncodedLenLocal2PlacedOk C A ctl abs :=
  chunkedHeaderSentEncodedLen_local2_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentBudget
