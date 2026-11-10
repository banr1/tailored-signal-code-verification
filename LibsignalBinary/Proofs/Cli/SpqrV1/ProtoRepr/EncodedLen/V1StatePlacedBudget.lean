/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.DefsV1StatePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesPolyPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked59_71PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.LeavesUnchunked82_93PlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesBPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateBranchesPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudgetAux1
import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudgetAux2
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1Placed -- shake: keep
meta import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlaced -- shake: keep
meta import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpers -- shake: keep

/-!
# `VmPreserved` Placed Master Proof and Contracts for `V1State::encoded_len` (Block `484`)

Proves `VmPreserved`-threaded `[LibsignalPlacement]` `subroutine_ok` contracts (both explicit
jump-table and `LibsignalRoLoaded`-discharged) for `V1State::encoded_len [local#3]` on CLI Block
`484`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Heap (VmPreserved)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (LibsignalPlacement LibsignalCodeLoaded LibsignalRoLoaded extract_withLsCodeLoaded
   withLsCodeLoaded lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.LibsignalSpqrV1 (V1State)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.EncodedLen.ChunkedPlaced
  (lsProg_484 blkPl_484)
open CryptoVerification.Cli.SpqrV1.ProtoRepr
  (cliV1StateJtSym v1StateJumpTableBytes_lsro_cli_intro
   step_v1State_keysSampled_placed step_v1State_ct1Received_placed
   step_v1State_ekSentCt1Received_placed step_v1State_noHeaderReceived_placed
   step_v1State_headerReceived_placed step_v1State_ekReceivedCt1Sampled_placed
   step_v1State_ct1Acknowledged_placed step_v1State_ct2Sampled_placed)
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
  (noneCap_add_one_beq_zero noneCap_add_one_bne_zero)
open CryptoVerification.SpqrV1.ProtoRepr
  (FrozenInv SepWPpF CallPinnedEncLenAtF bl_reloc_target_eq
   V1StateEncodedLenPinnedGhost V1StateEncodedLenGhost
   v1StatePBPinnedAt v1StatePBAt_eq_exists_pinned v1StatePBEncodedLen v1StateInnerPBPinnedAt
   v1StateEncodedLenStack chunkedEncodedLenStack polyEncodedLenStack
   stackAt_v1StateEncodedLen_eq stackAt_chunked_eq_poly
   v1StateJumpTableBytes v1StateJumpTableBytesAt v1StateJumpTableBytes_eq
   fold_v1StateJumpTableBytesAt v1State_post_of_body
   noneCap2 noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
   noneCap_add_two_beq_zero noneCap_add_two_bne_zero
   keysUnsampledPBPinnedAt keysUnsampledPBEncodedLen
   optKeysUnsampledPBPinnedAt optKeysUnsampledCap optKeysUnsampledPBPinnedAt_cap_bounds
   headerSentPBPinnedAt headerSentPBEncodedLen
   optHeaderSentPBPinnedAt optHeaderSentCap optHeaderSentPBPinnedAt_cap_bounds
   polynomialEncoderPBPinnedAt polynomialEncoderPBEncodedLen
   optPolynomialEncoderPBPinnedAt optPolyEncCap optPolynomialEncoderPBPinnedAt_cap_bounds
   polynomialDecoderPBPinnedAt polynomialDecoderPBEncodedLen
   optPolynomialDecoderPBPinnedAt optPolyDecCap optPolynomialDecoderPBPinnedAt_cap_bounds
   chunkedHeaderSentPBPinnedAt chunkedHeaderSentPBEncodedLen
   ekSentPBPinnedAt ekSentPBEncodedLen
   ekSentCt1ReceivedPBPinnedAt ekSentCt1ReceivedPBEncodedLen
   optEkSentCt1ReceivedPBPinnedAt optEkSentCt1ReceivedCap optEkSentCt1ReceivedPBPinnedAt_cap_bounds
   noHeaderReceivedPBPinnedAt noHeaderReceivedPBEncodedLen
   optNoHeaderReceivedPBPinnedAt optNoHeaderReceivedCap optNoHeaderReceivedPBPinnedAt_cap_bounds
   headerReceivedPBPinnedAt headerReceivedPBEncodedLen
   optHeaderReceivedPBPinnedAt optHeaderReceivedCap optHeaderReceivedPBPinnedAt_cap_bounds
   chunkedCt1SampledPBPinnedAt chunkedCt1SampledPBEncodedLen
   ct1SentEkReceivedPBPinnedAt ct1SentEkReceivedPBEncodedLen
   optCt1SentEkReceivedPBPinnedAt optCt1SentEkReceivedCap optCt1SentEkReceivedPBPinnedAt_cap_bounds
   ct1SentPBPinnedAt ct1SentPBEncodedLen
   optCt1SentPBPinnedAt optCt1SentPBPinnedAt_eq optCt1SentRest optCt1SentCap
   optCt1SentPBPinnedAt_cap_bounds optCt1SentRest_disc_bounds
   ct2SentPBPinnedAt ct2SentPBEncodedLen
   optCt2SentPBPinnedAt optCt2SentCap optCt2SentPBPinnedAt_cap_bounds
   step_v1State_none_placed step_v1State_prologue_to_64_placed
   step_v1State_keysUnsampled_placed step_v1State_headerSent_placed
   step_v1State_ct1Sampled_placed)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved withLsRoLoaded subroutine_ok_of_withVmPreserved
   LsBlocksCodeLoaded withLsBlocksCodeLoaded ls_subroutine_ok_blocks_vmPreserved)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
  (v1StateEncodedLenRoPinnedSpec v1StateEncodedLenRoSpec
   v1StateEncodedLenPinnedSpec v1StateEncodedLenSpec)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersBudget
  (v1StateEncodedLen_ro_lscl_ok_of_pinned)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StateHelpersPlacedBudget
  (v1State484Blocks subroutine_ok_of_sepWPpF_blocks
   callPinnedEncLenAtF_of_bl_blocks callPinnedEncLenAtF_of_bl_blocks_ls)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudgetAux1
  (headerSent_495_blocks_ok)
open LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudgetAux2
  (ct1Sampled_486_blocks_ok)
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
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero

local notation "cliV1JtAddr" => lsρ cliV1StateJtSym

/-! ## 1. `v1State484Blocks` `BL` Call Bridges for Block `484` -/

local macro "v1_bl_blocks_plain " k:num calleeOk:ident A:term:max H:term:max : term =>
  `(callPinnedEncLenAtF_of_bl_blocks (blks := v1State484Blocks) (k := $k)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
      (by decide)
      (subroutine_ok_of_withVmPreserved ($calleeOk $A $H))
      (_hfetch := by simp only [arm64_norm]))

private theorem bl_484_ku [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 1024
      (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 1024 keysUnsampledEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_ks1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 600
      (headerSentPBPinnedAt A) headerSentPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 600 headerSentEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_ks2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 664
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 664 polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_hs [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 376
      (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack :=
  callPinnedEncLenAtF_of_bl_blocks_ls (blks := v1State484Blocks) (k := 376)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (by decide) (headerSent_495_blocks_ok A H)
    (_hfetch := by simp only [arm64_norm])

private theorem bl_484_cr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 408
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 408 ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_cr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 472
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 472 polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_escr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 124
      (ekSentCt1ReceivedPBPinnedAt A) ekSentCt1ReceivedPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 124 ekSentCt1ReceivedEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_escr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 188
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 188 polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_nhr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 1076
      (noHeaderReceivedPBPinnedAt A) noHeaderReceivedPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 1076 noHeaderReceivedEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_nhr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 1140
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 1140 polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_hr1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 756
      (headerReceivedPBPinnedAt A) headerReceivedPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 756 headerReceivedEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_hr2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 820
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 820 polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_cs [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 520
      (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack :=
  callPinnedEncLenAtF_of_bl_blocks_ls (blks := v1State484Blocks) (k := 520)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (by decide) (ct1Sampled_486_blocks_ok A H)
    (_hfetch := by simp only [arm64_norm])

private theorem bl_484_ercs1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 912
      (ct1SentEkReceivedPBPinnedAt A) ct1SentEkReceivedPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 912 ct1SentEkReceivedEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_ercs2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 976
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 976 polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_ca1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 260
      (ct1SentPBPinnedAt A) ct1SentPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 260 ct1SentEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_ca2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 324
      (polynomialDecoderPBPinnedAt A) polynomialDecoderPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 324 polynomialDecoderEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_c2s1 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 1192
      (ct2SentPBPinnedAt A) ct2SentPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 1192 ct2SentEncodedLen_local1_pinned_placed_ok_x A H

private theorem bl_484_c2s2 [LibsignalPlacement] (A : RustAlloc) (H : String → Option (State → State)) :
    CallPinnedEncLenAtF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (blkPl_484).base 1256
      (polynomialEncoderPBPinnedAt A) polynomialEncoderPBEncodedLen polyEncodedLenStack :=
  v1_bl_blocks_plain 1256 polynomialEncoderEncodedLen_local1_pinned_placed_ok_x A H

/-! ## 2. Master Entry-Point Proof (`v1State_484_entry_ro_pinned_wp_placed`) -/

theorem v1State_484_entry_ro_pinned_wp_placed [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State))
    (x : V1StateEncodedLenPinnedGhost) (R : SepProp) (s0 : State)
    (hpc0 : s0.pc = (blkPl_484).base) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec A cliV1JtAddr).pre x s0 ∗ R)
    (hsp : s0.spAligned = true) :
    ∃ P Fr, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPpF (LsBlocksCodeLoaded v1State484Blocks lsmpl) (lsProg_484 H) (s0.readReg64 .lr) s0 P
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec A cliV1JtAddr).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ Fr) →
            (sf.mem ⊨ (CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec A cliV1JtAddr).onPanic x s0 sf ∗ R)) := by
  v1State_484_fetches_range H 64 80
  rcases x with ⟨a, g, m⟩
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp; exact hsp
  simp only [CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec, v1StateJumpTableBytes_eq,
    stackAt_v1StateEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v32, v24, v16, v8, ⟨hx0, hfit⟩, hpre⟩
  refine ⟨((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
      stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
      v1StateJumpTableBytesAt cliV1JtAddr ∗
      v1StatePBPinnedAt A g a m ∗ R, emp,
    by rw [sepConj_emp]; convert hpre using 1; sep_ac_rfl, ?_⟩
  rcases m with ⟨inner⟩
  cases inner with
  | none =>
    have hP_eq (u32 u24 u16 : BitVec 64) :
        (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
          ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
          stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
          v1StateJumpTableBytesAt cliV1JtAddr ∗
          v1StatePBPinnedAt A g a ⟨none⟩ ∗ R) =
        (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
          ((s0.sp - 16#64) ↦₆₄ u16) ∗
          (((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 8#64) 216 ∗ R) ∗
          (a ↦₆₄ noneCap2)) := by
      dsimp only [v1StatePBPinnedAt]; sep_ac_rfl
    refine step_v1State_none_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H a s0.sp v32 v24 v16
      hpc0 hrun rfl halign hx0 (hP_eq v32 v24 v16) ?_
    intro sf hpcf hrunf hspf htrf hx0f hcsf
    refine ⟨?_, hspf, hcsf⟩
    intro hm_f
    rw [← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
    exact v1State_post_of_body A cliV1JtAddr a g ⟨none⟩ R s0 sf _ _ _ v8 hx0f htrf hm_f
  | some is =>
    cases is with
    | keysUnsampled v =>
      have hcap : (optKeysUnsampledCap g.a.gKeysUnsampled v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optKeysUnsampledCap g.a.gKeysUnsampled v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optKeysUnsampledPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000000#64) ∗
            memRegion (a + 64#64) 160 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.keysUnsampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optKeysUnsampledPBPinnedAt A g.a.gKeysUnsampled (a + 8#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 64#64) 160 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000000#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000000#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 80 s1 0#64 hx8_1
      refine step_v1State_keysUnsampled_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H
        (bl_484_ku A H) g.a.gKeysUnsampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.keysUnsampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | keysSampled v =>
      have hcap1 : (optHeaderSentCap g.a.gKeysSampled.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optHeaderSentCap g.a.gKeysSampled.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optHeaderSentPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000001#64) ∗
            optPolynomialEncoderPBPinnedAt A g.a.gKeysSampled.2 (a + 112#64) v.sendingHdr ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hcap2 : (optPolyEncCap g.a.gKeysSampled.2 v.sendingHdr + 1#64 == 0#64) = !v.sendingHdr.isSome ∧
          (optPolyEncCap g.a.gKeysSampled.2 v.sendingHdr + 1#64 != 0#64) = v.sendingHdr.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000001#64) ∗
            optHeaderSentPBPinnedAt A g.a.gKeysSampled.1 (a + 8#64) v.uc ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.keysSampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optHeaderSentPBPinnedAt A g.a.gKeysSampled.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.a.gKeysSampled.2 (a + 112#64) v.sendingHdr ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 168#64) 56 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000001#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000001#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 576 s1 1#64 hx8_1
      refine step_v1State_keysSampled_placed
        (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H (bl_484_ks1 A H) (bl_484_ks2 A H)
        g.a.gKeysSampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.keysSampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | headerSent v =>
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.headerSent v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (chunkedHeaderSentPBPinnedAt A g.a.gHeaderSent (a + 8#64) v ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 184#64) 40 ∗
                ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000002#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000002#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 372 s1 2#64 hx8_1
      refine step_v1State_headerSent_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H
        (bl_484_hs A H) g.a.gHeaderSent a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.headerSent v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Received v =>
      have hcap1 : (optEkSentCt1ReceivedCap g.a.gCt1Received.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optEkSentCt1ReceivedCap g.a.gCt1Received.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000003#64) ∗
            optPolynomialEncoderPBPinnedAt A g.a.gCt1Received.2 (a + 112#64) v.sendingEk ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hcap2 : (optPolyEncCap g.a.gCt1Received.2 v.sendingEk + 1#64 == 0#64) = !v.sendingEk.isSome ∧
          (optPolyEncCap g.a.gCt1Received.2 v.sendingEk + 1#64 != 0#64) = v.sendingEk.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000003#64) ∗
            optEkSentCt1ReceivedPBPinnedAt A g.a.gCt1Received.1 (a + 8#64) v.uc ∗
            memRegion (a + 168#64) 56 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Received v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optEkSentCt1ReceivedPBPinnedAt A g.a.gCt1Received.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.a.gCt1Received.2 (a + 112#64) v.sendingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 168#64) 56 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000003#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000003#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 384 s1 3#64 hx8_1
      refine step_v1State_ct1Received_placed
        (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H (bl_484_cr1 A H) (bl_484_cr2 A H)
        g.a.gCt1Received a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ct1Received v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ekSentCt1Received v =>
      have hcap1 : (optEkSentCt1ReceivedCap g.a.gEkSentCt1Received.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optEkSentCt1ReceivedCap g.a.gEkSentCt1Received.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optEkSentCt1ReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000004#64) ∗
            optPolynomialDecoderPBPinnedAt A g.a.gEkSentCt1Received.2 (a + 112#64) v.receivingCt2 ∗
            memRegion (a + 152#64) 72 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hcap2 : (optPolyDecCap g.a.gEkSentCt1Received.2 v.receivingCt2 + 1#64 == 0#64) = !v.receivingCt2.isSome ∧
          (optPolyDecCap g.a.gEkSentCt1Received.2 v.receivingCt2 + 1#64 != 0#64) = v.receivingCt2.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 112#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000004#64) ∗
            optEkSentCt1ReceivedPBPinnedAt A g.a.gEkSentCt1Received.1 (a + 8#64) v.uc ∗
            memRegion (a + 152#64) 72 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ekSentCt1Received v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optEkSentCt1ReceivedPBPinnedAt A g.a.gEkSentCt1Received.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.a.gEkSentCt1Received.2 (a + 112#64) v.receivingCt2 ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 152#64) 72 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000004#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000004#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 100 s1 4#64 hx8_1
      refine step_v1State_ekSentCt1Received_placed
        (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H (bl_484_escr1 A H) (bl_484_escr2 A H)
        g.a.gEkSentCt1Received a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ekSentCt1Received v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | noHeaderReceived v =>
      have hcap1 : (optNoHeaderReceivedCap g.a.gNoHeaderReceived.2 v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optNoHeaderReceivedCap g.a.gNoHeaderReceived.2 v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optNoHeaderReceivedPBPinnedAt_cap_bounds (p := a + 48#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000005#64) ∗
            optPolynomialDecoderPBPinnedAt A g.a.gNoHeaderReceived.1 (a + 8#64) v.receivingHdr ∗
            memRegion (a + 104#64) 120 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hcap2 : (optPolyDecCap g.a.gNoHeaderReceived.1 v.receivingHdr + 1#64 == 0#64) = !v.receivingHdr.isSome ∧
          (optPolyDecCap g.a.gNoHeaderReceived.1 v.receivingHdr + 1#64 != 0#64) = v.receivingHdr.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000005#64) ∗
            optNoHeaderReceivedPBPinnedAt A g.a.gNoHeaderReceived.2 (a + 48#64) v.uc ∗
            memRegion (a + 104#64) 120 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.noHeaderReceived v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optPolynomialDecoderPBPinnedAt A g.a.gNoHeaderReceived.1 (a + 8#64) v.receivingHdr ∗
              optNoHeaderReceivedPBPinnedAt A g.a.gNoHeaderReceived.2 (a + 48#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 104#64) 120 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000005#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000005#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 712 s1 5#64 hx8_1
      refine step_v1State_noHeaderReceived_placed
        (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H (bl_484_nhr1 A H) (bl_484_nhr2 A H)
        g.a.gNoHeaderReceived a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.noHeaderReceived v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | headerReceived v =>
      have hcap1 : (optHeaderReceivedCap g.b.gHeaderReceived.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optHeaderReceivedCap g.b.gHeaderReceived.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optHeaderReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000006#64) ∗
            optPolynomialDecoderPBPinnedAt A g.b.gHeaderReceived.2 (a + 88#64) v.receivingEk ∗
            memRegion (a + 128#64) 96 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hcap2 : (optPolyDecCap g.b.gHeaderReceived.2 v.receivingEk + 1#64 == 0#64) = !v.receivingEk.isSome ∧
          (optPolyDecCap g.b.gHeaderReceived.2 v.receivingEk + 1#64 != 0#64) = v.receivingEk.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 88#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000006#64) ∗
            optHeaderReceivedPBPinnedAt A g.b.gHeaderReceived.1 (a + 8#64) v.uc ∗
            memRegion (a + 128#64) 96 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.headerReceived v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optHeaderReceivedPBPinnedAt A g.b.gHeaderReceived.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.b.gHeaderReceived.2 (a + 88#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 128#64) 96 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000006#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000006#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 732 s1 6#64 hx8_1
      refine step_v1State_headerReceived_placed
        (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H (bl_484_hr1 A H) (bl_484_hr2 A H)
        g.b.gHeaderReceived a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.headerReceived v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Sampled v =>
      have ⟨hw_beq, hw_bne, hw_ult⟩ :
          (optCt1SentCap g.b.gCt1Sampled.uc v.uc + 2#64 == 0#64) = false ∧
          (optCt1SentCap g.b.gCt1Sampled.uc v.uc + 2#64 != 0#64) = true ∧
          ((optCt1SentCap g.b.gCt1Sampled.uc v.uc ^^^ 0x8000000000000000#64).ult 11#64) = false := by
        apply optCt1SentRest_disc_bounds (p := a)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc) ∗
            optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64) v.sendingCt1 ∗
            optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 184#64) v.receivingEk ∗
            ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
            ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt, chunkedCt1SampledPBPinnedAt] at hpre
        rw [optCt1SentPBPinnedAt_eq] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentRest A g.b.gCt1Sampled.uc a v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64) v.sendingCt1 ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 184#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt, chunkedCt1SampledPBPinnedAt]
        rw [optCt1SentPBPinnedAt_eq]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp (optCt1SentCap g.b.gCt1Sampled.uc v.uc) v32 v24 v16
        hpc0 hrun rfl halign hx0 hw_beq hw_bne (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 520 s1 7#64 (by rw [hx8_1, hw_ult]; rfl)
      rw [fold_v1StateJumpTableBytesAt]
      have hP_cs :
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
            (optCt1SentRest A g.b.gCt1Sampled.uc a v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gCt1Sampled.sendingCt1 (a + 128#64) v.sendingCt1 ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Sampled.receivingEk (a + 184#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ optCt1SentCap g.b.gCt1Sampled.uc v.uc)) =
          (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
            chunkedCt1SampledPBPinnedAt A g.b.gCt1Sampled a v ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            (v1StateJumpTableBytesAt cliV1JtAddr ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) := by
        dsimp only [chunkedCt1SampledPBPinnedAt]
        rw [optCt1SentPBPinnedAt_eq]; sep_ac_rfl
      refine step_v1State_ct1Sampled_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H
        (bl_484_cs A H) g.b.gCt1Sampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hP_cs ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ct1Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ekReceivedCt1Sampled v =>
      have hcap1 : (optCt1SentEkReceivedCap g.b.gEkReceivedCt1Sampled.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optCt1SentEkReceivedCap g.b.gEkReceivedCt1Sampled.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optCt1SentEkReceivedPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000008#64) ∗
            optPolynomialEncoderPBPinnedAt A g.b.gEkReceivedCt1Sampled.2 (a + 136#64) v.sendingCt1 ∗
            memRegion (a + 192#64) 32 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hcap2 : (optPolyEncCap g.b.gEkReceivedCt1Sampled.2 v.sendingCt1 + 1#64 == 0#64) = !v.sendingCt1.isSome ∧
          (optPolyEncCap g.b.gEkReceivedCt1Sampled.2 v.sendingCt1 + 1#64 != 0#64) = v.sendingCt1.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 136#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000008#64) ∗
            optCt1SentEkReceivedPBPinnedAt A g.b.gEkReceivedCt1Sampled.1 (a + 8#64) v.uc ∗
            memRegion (a + 192#64) 32 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ekReceivedCt1Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentEkReceivedPBPinnedAt A g.b.gEkReceivedCt1Sampled.1 (a + 8#64) v.uc ∗
              optPolynomialEncoderPBPinnedAt A g.b.gEkReceivedCt1Sampled.2 (a + 136#64) v.sendingCt1 ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 192#64) 32 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000008#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000008#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 888 s1 8#64 hx8_1
      refine step_v1State_ekReceivedCt1Sampled_placed
        (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H (bl_484_ercs1 A H) (bl_484_ercs2 A H)
        g.b.gEkReceivedCt1Sampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ekReceivedCt1Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct1Acknowledged v =>
      have hcap1 : (optCt1SentCap g.b.gCt1Acknowledged.1 v.uc + 1#64 == 0#64) = !v.uc.isSome ∧
          (optCt1SentCap g.b.gCt1Acknowledged.1 v.uc + 1#64 != 0#64) = v.uc.isSome := by
        apply optCt1SentPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000009#64) ∗
            optPolynomialDecoderPBPinnedAt A g.b.gCt1Acknowledged.2 (a + 136#64) v.receivingEk ∗
            memRegion (a + 176#64) 48 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hcap2 : (optPolyDecCap g.b.gCt1Acknowledged.2 v.receivingEk + 1#64 == 0#64) = !v.receivingEk.isSome ∧
          (optPolyDecCap g.b.gCt1Acknowledged.2 v.receivingEk + 1#64 != 0#64) = v.receivingEk.isSome := by
        apply optPolynomialDecoderPBPinnedAt_cap_bounds (p := a + 136#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x8000000000000009#64) ∗
            optCt1SentPBPinnedAt A g.b.gCt1Acknowledged.1 (a + 8#64) v.uc ∗
            memRegion (a + 176#64) 48 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ct1Acknowledged v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optCt1SentPBPinnedAt A g.b.gCt1Acknowledged.1 (a + 8#64) v.uc ∗
              optPolynomialDecoderPBPinnedAt A g.b.gCt1Acknowledged.2 (a + 136#64) v.receivingEk ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 176#64) 48 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x8000000000000009#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x8000000000000009#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 236 s1 9#64 hx8_1
      refine step_v1State_ct1Acknowledged_placed
        (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H (bl_484_ca1 A H) (bl_484_ca2 A H)
        g.b.gCt1Acknowledged a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ct1Acknowledged v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f
    | ct2Sampled v =>
      have hcap1 : (optCt2SentCap g.b.gCt2Sampled.2 v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
          (optCt2SentCap g.b.gCt2Sampled.2 v.uc + 2#64 != 0#64) = v.uc.isSome := by
        apply optCt2SentPBPinnedAt_cap_bounds (p := a + 64#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x800000000000000a#64) ∗
            optPolynomialEncoderPBPinnedAt A g.b.gCt2Sampled.1 (a + 8#64) v.sendingCt2 ∗
            memRegion (a + 120#64) 104 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hcap2 : (optPolyEncCap g.b.gCt2Sampled.1 v.sendingCt2 + 1#64 == 0#64) = !v.sendingCt2.isSome ∧
          (optPolyEncCap g.b.gCt2Sampled.1 v.sendingCt2 + 1#64 != 0#64) = v.sendingCt2.isSome := by
        apply optPolynomialEncoderPBPinnedAt_cap_bounds (p := a + 8#64)
          (R := v1StateJumpTableBytesAt cliV1JtAddr ∗ (a ↦₆₄ 0x800000000000000a#64) ∗
            optCt2SentPBPinnedAt A g.b.gCt2Sampled.2 (a + 64#64) v.uc ∗
            memRegion (a + 120#64) 104 ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗
            ((s0.sp - 24#64) ↦₆₄ v24) ∗ ((s0.sp - 16#64) ↦₆₄ v16) ∗
            ((s0.sp - 8#64) ↦₆₄ v8) ∗ stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗ R)
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt] at hpre
        convert hpre using 1; sep_ac_rfl
      have hP_eq (u32 u24 u16 : BitVec 64) :
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
            stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
            v1StateJumpTableBytesAt cliV1JtAddr ∗
            v1StatePBPinnedAt A g a ⟨some (.ct2Sampled v)⟩ ∗ R) =
          (((s0.sp - 32#64) ↦₆₄ u32) ∗ ((s0.sp - 24#64) ↦₆₄ u24) ∗
            ((s0.sp - 16#64) ↦₆₄ u16) ∗
            (optPolynomialEncoderPBPinnedAt A g.b.gCt2Sampled.1 (a + 8#64) v.sendingCt2 ∗
              optCt2SentPBPinnedAt A g.b.gCt2Sampled.2 (a + 64#64) v.uc ∗
              stackAt (s0.sp - 32#64) polyEncodedLenStack ∗
              (v1StateJumpTableBytesAt cliV1JtAddr ∗ memRegion (a + 120#64) 104 ∗
                memRegion (s0.sp - 32#64 - 48#64) 32 ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R)) ∗
            (a ↦₆₄ 0x800000000000000a#64)) := by
        dsimp only [v1StatePBPinnedAt, v1StateInnerPBPinnedAt]
        rw [stackAt_chunked_eq_poly (s0.sp - 32#64)]; sep_ac_rfl
      refine step_v1State_prologue_to_64_placed (LsBlocksCodeLoaded v1State484Blocks lsmpl) H
        a s0.sp 0x800000000000000a#64 v32 v24 v16
        hpc0 hrun rfl halign hx0 (by decide) (by decide) (hP_eq v32 v24 v16) ?_
      intro s1 P1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hx9_1 hcs1 hP1
      subst hP1
      step_v1State_jump_to_F ((blkPl_484).base) 868 s1 10#64 hx8_1
      refine step_v1State_ct2Sampled_placed
        (LsBlocksCodeLoaded v1State484Blocks lsmpl) A H (bl_484_c2s1 A H) (bl_484_c2s2 A H)
        g.b.gCt2Sampled a s0.sp v hfit
        (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
        (by simp [arm64_norm, hx0_1])
        ⟨by simp [arm64_norm, hcs1.2.1], by simp [arm64_norm, hcs1.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.1], by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.1],
         by simp [arm64_norm, hcs1.2.2.2.2.2.2.2.2.2]⟩
        hcap1 hcap2 (by simp only [v1StateJumpTableBytesAt, sepConj_assoc]; rfl) ?_
      intro sf hpcf hrunf hspf htrf hx0f hcsf
      refine ⟨?_, hspf, hcsf⟩
      intro hm_f
      rw [fold_v1StateJumpTableBytesAt, ← hP_eq (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19)] at hm_f
      exact v1State_post_of_body A cliV1JtAddr a g ⟨some (.ct2Sampled v)⟩ R s0 sf _ _ _ v8
        hx0f (by simp [arm64_norm, htrf, htr1]) hm_f

/-! ## 3. Explicit `.rodata` Jump-Table Placed Contracts (`lsρ cliV1StateJtSym`) -/

def V1StateEncodedLenLocal1PinnedPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 H) (blkPl_484).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr))

def V1StateEncodedLenLocal1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 H) (blkPl_484).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A cliV1JtAddr))

def V1StateEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr))

def V1StateEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
    (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A cliV1JtAddr))

def V1StateEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def V1StateEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem v1StateEncodedLen_local1_pinned_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr)) := by
  refine ls_subroutine_ok_blocks_vmPreserved
    (progQ := lsProg_484 (hooksException H))
    (blks := v1State484Blocks) (i := 484)
    (by decide) (by decide) (by decide +kernel) (hok := subroutine_ok_of_sepWPpF_blocks ?_)
  exact v1State_484_entry_ro_pinned_wp_placed A (hooksException H)

theorem v1StateEncodedLen_local1_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoSpec A cliV1JtAddr)) :=
  v1StateEncodedLen_ro_lscl_ok_of_pinned
    (v1StateEncodedLen_local1_pinned_placed_ok_x A H)

theorem v1StateEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    V1StateEncodedLenLocal1PinnedPlacedOkExt A ext :=
  v1StateEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem v1StateEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    V1StateEncodedLenLocal1PlacedOkExt A ext :=
  v1StateEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem v1StateEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    V1StateEncodedLenLocal1PinnedPlacedOk C A ctl abs :=
  v1StateEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem v1StateEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    V1StateEncodedLenLocal1PlacedOk C A ctl abs :=
  v1StateEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

/-! ## 4. `LibsignalRoLoaded` Jump-Table-Discharged Placed Contracts (`*_ro_*` / `ro_*`) -/

private theorem subroutine_ok_v1State_ro_pinned_of_roBase [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (v1StateEncodedLenRoPinnedSpec A cliV1JtAddr))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (withLsRoLoaded lsmpl (v1StateEncodedLenPinnedSpec A))) := by
  refine subroutine_ok_mono h (fun x R s0 hp => ?_) (fun x R s0 sf hq => ?_)
  · obtain ⟨hcl, hp1⟩ := extract_withLsCodeLoaded hp
    dsimp only [withLsRoLoaded] at hp1
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp1
    obtain ⟨hro, hp2⟩ := hp1
    have hp3 := v1StateJumpTableBytes_lsro_cli_intro hro hp2
    dsimp only [withLsCodeLoaded, v1StateEncodedLenRoPinnedSpec, v1StateEncodedLenPinnedSpec,
      withVmPreserved, CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenPinnedSpec, lsρ] at hp3 ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp3⟩
  · dsimp only [withLsCodeLoaded, withLsRoLoaded,
      v1StateEncodedLenRoPinnedSpec, v1StateEncodedLenPinnedSpec, withVmPreserved,
      CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenRoPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenPinnedSpec] at hq ⊢
    have hperm : sf.mem ⊨
        (cliV1JtAddr ↦ᵣ v1StateJumpTableBytes) ∗
        ((⌜VmPreserved s0 sf⌝ ∗
          (⌜sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen x.m) ∧ sf.trace = s0.trace⌝ ∗
            v1StatePBPinnedAt A x.g x.a x.m ∗ stackAt s0.sp v1StateEncodedLenStack)) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hq
    exact Satisfies.of_sep_right hperm

private theorem subroutine_ok_v1State_ro_unpin [LibsignalPlacement]
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (withLsRoLoaded lsmpl (v1StateEncodedLenPinnedSpec A)))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl
        (withLsRoLoaded lsmpl (v1StateEncodedLenSpec A))) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsCodeLoaded, withLsRoLoaded, v1StateEncodedLenSpec,
    v1StateEncodedLenPinnedSpec, withVmPreserved,
    CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenSpec] at hpre
  rw [v1StatePBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine hpinned.mono_outcome ⟨x.a, g, x.m⟩ R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeLoaded, withLsRoLoaded, v1StateEncodedLenPinnedSpec,
      v1StateEncodedLenSpec, withVmPreserved] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, hpost⟩
    refine ⟨hvm, ?_⟩
    dsimp only [CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenPinnedSpec,
      CryptoVerification.SpqrV1.ProtoRepr.v1StateEncodedLenSpec] at hpost ⊢
    rw [v1StatePBAt_eq_exists_pinned]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem subroutine_ok_swap_lsro_lscl {α : Type} {pl : MultiPlacement}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry
      (withLsCodeLoaded pl (withLsRoLoaded pl spec))) :
    subroutine_ok prog entry
      (withLsRoLoaded pl (withLsCodeLoaded pl spec)) := by
  refine subroutine_ok_mono h
    (fun _ _ _ hp => Satisfies.mono (Entails.of_eq (by
      dsimp only [withLsCodeLoaded, withLsRoLoaded]
      sep_ac_rfl)) hp)
    (fun _ _ _ _ hq => hq)
    (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ he => he)
    (fun _ _ _ _ ho => ho)

def V1StateEncodedLenLocal1RoPinnedPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 H) (blkPl_484).base
    (withLsCodeLoaded lsmpl
      (withLsRoLoaded lsmpl (v1StateEncodedLenPinnedSpec A)))

def V1StateEncodedLenLocal1RoPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 H) (blkPl_484).base
    (withLsCodeLoaded lsmpl
      (withLsRoLoaded lsmpl (v1StateEncodedLenSpec A)))

def V1StateEncodedLenLocal1RoPinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
    (withLsCodeLoaded lsmpl
      (withLsRoLoaded lsmpl (v1StateEncodedLenPinnedSpec A)))

def V1StateEncodedLenLocal1RoPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
    (withLsCodeLoaded lsmpl
      (withLsRoLoaded lsmpl (v1StateEncodedLenSpec A)))

def V1StateEncodedLenLocal1RoPinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal1RoPinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def V1StateEncodedLenLocal1RoPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  V1StateEncodedLenLocal1RoPlacedOkExt A (tripleRatchetExterns C ctl abs)

theorem v1StateEncodedLen_local1_ro_pinned_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsCodeLoaded lsmpl
        (withLsRoLoaded lsmpl (v1StateEncodedLenPinnedSpec A))) :=
  subroutine_ok_v1State_ro_pinned_of_roBase
    (v1StateEncodedLen_local1_pinned_placed_ok_x A H)

theorem v1StateEncodedLen_local1_ro_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsCodeLoaded lsmpl
        (withLsRoLoaded lsmpl (v1StateEncodedLenSpec A))) :=
  subroutine_ok_v1State_ro_unpin
    (v1StateEncodedLen_local1_ro_pinned_placed_ok_x A H)

theorem v1StateEncodedLen_local1_ro_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    V1StateEncodedLenLocal1RoPinnedPlacedOkExt A ext :=
  v1StateEncodedLen_local1_ro_pinned_placed_ok_x A (Rust.withPanics ext)

theorem v1StateEncodedLen_local1_ro_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    V1StateEncodedLenLocal1RoPlacedOkExt A ext :=
  v1StateEncodedLen_local1_ro_placed_ok_x A (Rust.withPanics ext)

theorem v1StateEncodedLen_local1_ro_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    V1StateEncodedLenLocal1RoPinnedPlacedOk C A ctl abs :=
  v1StateEncodedLen_local1_ro_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem v1StateEncodedLen_local1_ro_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    V1StateEncodedLenLocal1RoPlacedOk C A ctl abs :=
  v1StateEncodedLen_local1_ro_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ro_v1StateEncodedLen_local1_pinned_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenPinnedSpec A))) :=
  subroutine_ok_swap_lsro_lscl
    (v1StateEncodedLen_local1_ro_pinned_placed_ok_x A H)

theorem ro_v1StateEncodedLen_local1_placed_ok_x [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok (lsProg_484 H) (blkPl_484).base
      (withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenSpec A))) :=
  subroutine_ok_swap_lsro_lscl
    (v1StateEncodedLen_local1_ro_placed_ok_x A H)

theorem ro_v1StateEncodedLen_local1_pinned_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
      (withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenPinnedSpec A))) :=
  ro_v1StateEncodedLen_local1_pinned_placed_ok_x A (Rust.withPanics ext)

theorem ro_v1StateEncodedLen_local1_placed_ok_ext [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) :
    subroutine_ok (lsProg_484 (Rust.withPanics ext)) (blkPl_484).base
      (withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenSpec A))) :=
  ro_v1StateEncodedLen_local1_placed_ok_x A (Rust.withPanics ext)

theorem ro_v1StateEncodedLen_local1_pinned_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    subroutine_ok (lsProg_484 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_484).base
      (withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenPinnedSpec A))) :=
  ro_v1StateEncodedLen_local1_pinned_placed_ok_ext A (tripleRatchetExterns C ctl abs)

theorem ro_v1StateEncodedLen_local1_placed_ok [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) :
    subroutine_ok (lsProg_484 (Rust.withPanics (tripleRatchetExterns C ctl abs))) (blkPl_484).base
      (withLsRoLoaded lsmpl
        (withLsCodeLoaded lsmpl (v1StateEncodedLenSpec A))) :=
  ro_v1StateEncodedLen_local1_placed_ok_ext A (tripleRatchetExterns C ctl abs)

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.EncodedLen.V1StatePlacedBudget
