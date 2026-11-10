/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1StatePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlaced
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
import ProofLib.SepLogic.WP.StateNorm
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed -- shake: keep

/-!
# `VmPreserved` Placed Helpers and Call Bridges for `V1State::encoded_len` (Block `484`)

Defines `v1State484Blocks` and proves `VmPreserved`-threaded `SepWPpF` and `BL` call bridges for CLI
Block `484` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement LibsignalHooks LibsignalCodeLoaded IsLsBlockProg lsmpl)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.Placed
  (lsProg_479 lsProg_500 lsProg_470 lsProg_496 lsProg_482
   lsProg_492 lsProg_499 lsProg_487 lsProg_469)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced
  (lsProg_484 blkPl_484 lsProg_495 blkPl_495 lsProg_486 blkPl_486 lsProg_480 lsProg_493)
open CryptoVerification.SpqrV1.ProtoRepr
  (PinnedEncLenGhost FrozenInv SepWPpF CallPinnedEncLenAtF bl_reloc_target_eq
   callPinnedEncLenAtF_of_bl_plain callPinnedEncLenAtF_of_bl_lscl
   Unchunked2PBGhost keysUnsampledPBPinnedAt keysUnsampledPBEncodedLen
   optKeysUnsampledPBPinnedAt optKeysUnsampledCap
   headerSentPBPinnedAt headerSentPBEncodedLen
   polynomialEncoderPBPinnedAt polynomialEncoderPBEncodedLen
   optPolynomialEncoderPBFieldEncodedLen
   polynomialDecoderPBPinnedAt polynomialDecoderPBEncodedLen
   ChunkedHeaderSentPBGhost chunkedHeaderSentPBPinnedAt chunkedHeaderSentPBEncodedLen
   chunkedHeaderSentUnpacked chunkedHeaderSentPBPinnedAt_eq_unpacked chunkedHeaderSentUnpacked_bounds
   ekSentPBPinnedAt ekSentPBEncodedLen optEkSentPBFieldEncodedLen
   ekSentCt1ReceivedPBPinnedAt ekSentCt1ReceivedPBEncodedLen
   noHeaderReceivedPBPinnedAt noHeaderReceivedPBEncodedLen
   headerReceivedPBPinnedAt headerReceivedPBEncodedLen
   ChunkedCt1SampledPBGhost chunkedCt1SampledPBPinnedAt chunkedCt1SampledPBEncodedLen
   chunkedCt1SampledUnpacked chunkedCt1SampledPBPinnedAt_eq_unpacked chunkedCt1SampledUnpacked_bounds
   ct1SentEkReceivedPBPinnedAt ct1SentEkReceivedPBEncodedLen
   ct1SentPBPinnedAt ct1SentPBEncodedLen optCt1SentPBFieldEncodedLen
   ct2SentPBPinnedAt ct2SentPBEncodedLen
   polyEncodedLenStack chunkedEncodedLenStack stackAt_chunkedEncodedLen_eq
   v1StatePBEncodedLen)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen (EpochEncLenCalleeSaved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (subroutine_ok_of_withVmPreserved LsBlocksCodeLoaded withLsBlocksCodeLoaded
   ls_subroutine_ok_of_block_in)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedHeaderSentPlacedBudget
  (chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesChunkedPlacedBudget
  (chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget
  (polynomialEncoderEncodedLen_local1_pinned_placed_ok_x
   polynomialDecoderEncodedLen_local1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71PlacedBudget
  (keysUnsampledEncodedLen_local1_pinned_placed_ok_x
   noHeaderReceivedEncodedLen_local1_pinned_placed_ok_x
   ct2SentEncodedLen_local1_pinned_placed_ok_x
   ekSentEncodedLen_local1_pinned_placed_ok_x
   headerReceivedEncodedLen_local1_pinned_placed_ok_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
  (headerSentEncodedLen_local1_pinned_placed_ok_x
   ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x
   ct1SentEncodedLen_local1_pinned_placed_ok_x
   ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr

/-! ## 1. Block-Subset `SepWPpF` & `CallPinnedEncLenAtF` Bridges (`v1State484Blocks`) -/

/-- Closed transitive call-tree block list for Block `484` (`V1State::encoded_len [local#3]`). -/
abbrev v1State484Blocks : List Nat :=
  [484, 495, 486, 480, 493, 479, 500, 470, 496, 482, 492, 499, 487, 469]

instance instFrozenInvLsBlocks (blks : List Nat) (pl : MultiPlacement) :
    FrozenInv (LsBlocksCodeLoaded blks pl) where
  keeps h hkf := h.of_keepsFrozen hkf

theorem subroutine_ok_of_sepWPpF_blocks {α : Type} {prog : Program} {entry : BitVec 64}
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

theorem callPinnedEncLenAtF_of_bl_blocks [LibsignalPlacement]
    {callerProg calleeProg : Program} {blks : List Nat} {i j : Nat} {H : LibsignalHooks}
    [_hcaller : IsLsBlockProg callerProg i H] [_hcallee_prog : IsLsBlockProg calleeProg j H]
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
    (_hfetch : callerProg.fetch (entry + BitVec.ofNat 64 k) =
      some (.bl (lsmpl.base j - entry - BitVec.ofNat 64 k)) := by simp only [arm64_norm])
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded blks lsmpl) callerProg entry k repr encLen stackSz := by
  intro _ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound hcont hcl0
  subst hsp
  have _htarget : entry + BitVec.ofNat 64 k + (lsmpl.base j - entry - BitVec.ofNat 64 k) =
      lsmpl.base j :=
    bl_reloc_target_eq entry (BitVec.ofNat 64 k) (lsmpl.base j)
  have hcall : subroutine_ok callerProg (lsmpl.base j) (withLsBlocksCodeLoaded blks lsmpl spec) :=
    ls_subroutine_ok_of_block_in (callerProg := callerProg) hj hcallee
  apply SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl0
    (mid := entry + BitVec.ofNat 64 (k + 4))
  wp_steps
  have _hlr_eq : entry + BitVec.ofNat 64 k + 4#64 = entry + BitVec.ofNat 64 (k + 4) := by
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
      have ⟨_h19, _h20, _h21, _h22, _h23, _h24, _h25, _h26, _h27, _h28, _h29, _hv⟩ := hcs_sf
      have hcs_saved : EpochEncLenCalleeSaved s sf := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
      have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := by simp_all
      intro hcl_sf
      exact hcont sf hpc_sf hrun_sf hsp_sf htr_sf hx0_sf hcs_saved hfp_sf hcl_sf
  · intro R' sf _ hoom
    dsimp only [withLsBlocksCodeLoaded] at hoom
    rw [hspec_oom] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

theorem callPinnedEncLenAtF_of_bl_blocks_ls [LibsignalPlacement]
    {callerProg calleeProg : Program} {blks : List Nat} {i j : Nat} {H : LibsignalHooks}
    [_hcaller : IsLsBlockProg callerProg i H] [_hcallee_prog : IsLsBlockProg calleeProg j H]
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
    (hcallee : subroutine_ok calleeProg (lsmpl.base j) (withLsBlocksCodeLoaded blks lsmpl spec))
    (_hfetch : callerProg.fetch (entry + BitVec.ofNat 64 k) =
      some (.bl (lsmpl.base j - entry - BitVec.ofNat 64 k)) := by simp only [arm64_norm])
    (hspec_oom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded blks lsmpl) callerProg entry k repr encLen stackSz := by
  intro _ret g a sp m s F Q Qp hpc hrun hsp halign hx0 hbound hcont hcl0
  subst hsp
  have _htarget : entry + BitVec.ofNat 64 k + (lsmpl.base j - entry - BitVec.ofNat 64 k) =
      lsmpl.base j :=
    bl_reloc_target_eq entry (BitVec.ofNat 64 k) (lsmpl.base j)
  have hcall : subroutine_ok callerProg (lsmpl.base j)
      (withLsBlocksCodeLoaded blks lsmpl (withLsBlocksCodeLoaded blks lsmpl spec)) :=
    ls_subroutine_ok_of_block_in (callerProg := callerProg) hj hcallee
  apply SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl0
    (mid := entry + BitVec.ofNat 64 (k + 4))
  wp_steps
  have _hlr_eq : entry + BitVec.ofNat 64 k + 4#64 = entry + BitVec.ofNat 64 (k + 4) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine SepWP.call_subroutine_frame (x := ⟨a, g, m⟩) (F := F)
    (ret_pc := entry + BitVec.ofNat 64 (k + 4)) hcall
    (by simp_all) (by simp_all)
    (by simp only [State.spAligned, beq_iff_eq]; simp_all)
    (by simp_all) ?_ ?_ ?_ ?_ (h_oom := ?_)
  · intro R hm
    dsimp only [withLsBlocksCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ ⌜LsBlocksCodeLoaded blks lsmpl _⌝,
      satisfies_pure_sepConj]
    refine ⟨by simp_all, ?_⟩
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
      have ⟨_h19, _h20, _h21, _h22, _h23, _h24, _h25, _h26, _h27, _h28, _h29, _hv⟩ := hcs_sf
      have hcs_saved : EpochEncLenCalleeSaved s sf := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
      have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := by simp_all
      intro hcl_sf
      exact hcont sf hpc_sf hrun_sf hsp_sf htr_sf hx0_sf hcs_saved hfp_sf hcl_sf
  · intro R' sf _ hoom
    dsimp only [withLsBlocksCodeLoaded] at hoom
    rw [hspec_oom] at hoom
    exact (not_satisfies_false_sepConj hoom).elim

/-! ## 2. Block `484` `BL` Call Bridges on `LibsignalCodeLoaded lsmpl` -/

local macro "v1State_484_bl_lscl_plain " k:num calleeOk:ident A:term:max H:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_plain (k := $k)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (by simp only [arm64_norm]; rfl)
      (by first | simp only [arm64_norm] | (rw [bl_reloc_target_eq]; simp only [arm64_norm]))
      (subroutine_ok_of_withVmPreserved ($calleeOk $A $H)))

theorem subroutine_ok_of_lscl_withVmPreserved {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry
      (CryptoVerification.withLsCodeLoaded pl
        (LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget.withVmPreserved spec))) :
    subroutine_ok prog entry (CryptoVerification.withLsCodeLoaded pl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine (h.to_outcome x R s0 hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.withLsCodeLoaded,
      LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget.withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

local macro "v1State_484_bl_lscl_chunked " k:num calleeOk:ident A:term:max H:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_lscl (k := $k)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (by simp only [arm64_norm]; rfl)
      (by first | simp only [arm64_norm] | (rw [bl_reloc_target_eq]; simp only [arm64_norm]))
      (subroutine_ok_of_lscl_withVmPreserved ($calleeOk $A $H)))

theorem v1State_484_bl_ku [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1024
      (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 1024 keysUnsampledEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ks1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 600
      (headerSentPBPinnedAt A) headerSentPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 600 headerSentEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ks2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 664
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 664 polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_hs [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 376
      (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack :=
  v1State_484_bl_lscl_chunked 376 chunkedHeaderSentEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_cr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 408
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 408 ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_cr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 472
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 472 polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_escr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 124
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 124 ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_escr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 188
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 188 polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_nhr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1076
      (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 1076 noHeaderReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_nhr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1140
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 1140 polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_hr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 756
      (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 756 headerReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_hr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 820
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 820 polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_cs [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 520
      (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack :=
  v1State_484_bl_lscl_chunked 520 chunkedCt1SampledEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ercs1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 912
      (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 912 ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ercs2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 976
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 976 polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ca1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 260
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 260 ct1SentEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_ca2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 324
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 324 polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_c2s1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1192
      (ct2SentPBPinnedAt A) ct2SentPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 1192 ct2SentEncodedLen_local1_pinned_placed_ok_x A H

theorem v1State_484_bl_c2s2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LibsignalCodeLoaded lsmpl) (lsProg_484 H) (blkPl_484).base 1256
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1State_484_bl_lscl_plain 1256 polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlacedBudget
