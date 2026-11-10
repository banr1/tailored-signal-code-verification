/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemEncapsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemCoinsHelpersPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Stage 3 KEM Seed Packing and `kyber::encapsulate` (`[LibsignalPlacement]`, `+0x0ee8 → +0x0fb4`)

Packs the 32 low coin bytes into `[fsp + 0xfe0 .. fsp + 0x1000)`, invokes `kyber::encapsulate`,
splits the `1600`-byte output into `ct` (`1568` B) and `ss` (`32` B), and transports `A.pool`
across `+0x0ee8 → +0x0fb4` (`0` heap events).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 200000

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalPlacement lsρ)
open CryptoVerification.CliHandshake.InitiatePlaced (blkPl_521 lsProg_521)
open CryptoVerification.E2E
  (PreKeyBundleFields UnreachedPqxdhPrimitives initiateKemCoins initiateTapeLen toU8)
open CryptoVerification.E2E.Pqxdh.Initiator
  (KyberEncapsCall bytesToBv8 initiatorModelPrims kyberEncapsStubSpec)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (and_ff32_hi56_3 and_ff_hi56_3 extractLsb_hi56_3 zext64_trunc32_hi56_3_and_ff)
open CryptoVerification.E2E.Pqxdh.Shared (pqxdhEntryStack pqxdhHookStack)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed padCoins)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtStage3Placed InInitiatePlaced cliCoinsFillStack cliCoinsFillStackPlaced coinsCursorAtPlaced
   initEntryPlaced initPcPlaced initProgPlaced lsKemEncapsSym stage3KeySlotsAt stk_sub_ge_base)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
  (bundleEOf_props bytesToBv8_toU8_eq coinWord coinWord_truncate8 dhLenWord dhPrefix dhRemAt
   kemEncaps_out_eq memRegion_merge_at sepWPp_conseq_oom sepWPp_exists_elim_oom
   sepWPp_pure_elim_oom sep_replace stackAt_sub_split_init stk_sub_le_2pow64)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemEncapsPlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitPanicPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.CollapsePlacedBudget
  (s3_block_in_vm_placed s3_block_to_call_vm_placed s3_done_call_vm s3_done_in_vm)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DefsPlacedBudget
  (kyberEncaps_ok_at_init_placed s3_call_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpersPlacedBudget
  (S3InvPrefixPlaced)
open Arm64.Obj (MultiPlacement)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgExtPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

attribute [local irreducible] Program.fetch Program.externAt? S3InvPrefixPlaced coinsCursorAtPlaced coinWord
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

private theorem memRegion4_split1 (p : BitVec 64) :
    memRegion p 4 =
      (∃∗ b0, p ↦₈ b0) ∗ (∃∗ b1, (p + 1#64) ↦₈ b1) ∗
      (∃∗ b2, (p + 2#64) ↦₈ b2) ∗ (∃∗ b3, (p + 3#64) ↦₈ b3) := by
  rw [← memRegion_merge_at p 1 3 (p + 1#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 1#64) 1 2 (p + 2#64) (by bv_omega) (by decide),
      ← memRegion_merge_at (p + 2#64) 1 1 (p + 3#64) (by bv_omega) (by decide),
      ProofLib.memRegion_one, ProofLib.memRegion_one, ProofLib.memRegion_one, ProofLib.memRegion_one]

private theorem pack4_bytes_eq (p : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) =
      (p ↦ₛ [b0, b1, b2, b3]) := by
  rw [pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons, pointsToBytes_cons,
      pointsToBytes_nil]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp, sepConj_assoc]

private theorem vec32_chunks4_eq (v : List.Vector (BitVec 8) 32) :
    v.toList =
      [v.get ⟨0, by decide⟩, v.get ⟨1, by decide⟩, v.get ⟨2, by decide⟩, v.get ⟨3, by decide⟩] ++
      ([v.get ⟨4, by decide⟩, v.get ⟨5, by decide⟩, v.get ⟨6, by decide⟩, v.get ⟨7, by decide⟩] ++
      ([v.get ⟨8, by decide⟩, v.get ⟨9, by decide⟩, v.get ⟨10, by decide⟩, v.get ⟨11, by decide⟩] ++
      ([v.get ⟨12, by decide⟩, v.get ⟨13, by decide⟩, v.get ⟨14, by decide⟩, v.get ⟨15, by decide⟩] ++
      ([v.get ⟨16, by decide⟩, v.get ⟨17, by decide⟩, v.get ⟨18, by decide⟩, v.get ⟨19, by decide⟩] ++
      ([v.get ⟨20, by decide⟩, v.get ⟨21, by decide⟩, v.get ⟨22, by decide⟩, v.get ⟨23, by decide⟩] ++
      ([v.get ⟨24, by decide⟩, v.get ⟨25, by decide⟩, v.get ⟨26, by decide⟩, v.get ⟨27, by decide⟩] ++
       [v.get ⟨28, by decide⟩, v.get ⟨29, by decide⟩, v.get ⟨30, by decide⟩, v.get ⟨31, by decide⟩])))))) := by
  apply List.ext_getElem
  · simp [v.toList_length]
  · intro i hi1 hi2
    have hi : i < 32 := by simpa [v.toList_length] using hi1
    simp only [List.Vector.get]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
        _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      first | rfl | omega

private theorem kemCoins32_pointsTo_eq (fsp : BitVec 64)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    ((fsp + 0xfe0#64) ↦₈ (coinWord t 0 (by decide)).truncate 8) ∗
    ((fsp + 0xfe1#64) ↦₈ (coinWord t 1 (by decide)).truncate 8) ∗
    ((fsp + 0xfe2#64) ↦₈ (coinWord t 2 (by decide)).truncate 8) ∗
    ((fsp + 0xfe3#64) ↦₈ (coinWord t 3 (by decide)).truncate 8) ∗
    ((fsp + 0xfe4#64) ↦₈ (coinWord t 4 (by decide)).truncate 8) ∗
    ((fsp + 0xfe5#64) ↦₈ (coinWord t 5 (by decide)).truncate 8) ∗
    ((fsp + 0xfe6#64) ↦₈ (coinWord t 6 (by decide)).truncate 8) ∗
    ((fsp + 0xfe7#64) ↦₈ (coinWord t 7 (by decide)).truncate 8) ∗
    ((fsp + 0xfe8#64) ↦₈ (coinWord t 8 (by decide)).truncate 8) ∗
    ((fsp + 0xfe9#64) ↦₈ (coinWord t 9 (by decide)).truncate 8) ∗
    ((fsp + 0xfea#64) ↦₈ (coinWord t 10 (by decide)).truncate 8) ∗
    ((fsp + 0xfeb#64) ↦₈ (coinWord t 11 (by decide)).truncate 8) ∗
    ((fsp + 0xfec#64) ↦₈ (coinWord t 12 (by decide)).truncate 8) ∗
    ((fsp + 0xfed#64) ↦₈ (coinWord t 13 (by decide)).truncate 8) ∗
    ((fsp + 0xfee#64) ↦₈ (coinWord t 14 (by decide)).truncate 8) ∗
    ((fsp + 0xfef#64) ↦₈ (coinWord t 15 (by decide)).truncate 8) ∗
    ((fsp + 0xff0#64) ↦₈ (coinWord t 16 (by decide)).truncate 8) ∗
    ((fsp + 0xff1#64) ↦₈ (coinWord t 17 (by decide)).truncate 8) ∗
    ((fsp + 0xff2#64) ↦₈ (coinWord t 18 (by decide)).truncate 8) ∗
    ((fsp + 0xff3#64) ↦₈ (coinWord t 19 (by decide)).truncate 8) ∗
    ((fsp + 0xff4#64) ↦₈ (coinWord t 20 (by decide)).truncate 8) ∗
    ((fsp + 0xff5#64) ↦₈ (coinWord t 21 (by decide)).truncate 8) ∗
    ((fsp + 0xff6#64) ↦₈ (coinWord t 22 (by decide)).truncate 8) ∗
    ((fsp + 0xff7#64) ↦₈ (coinWord t 23 (by decide)).truncate 8) ∗
    ((fsp + 0xff8#64) ↦₈ (coinWord t 24 (by decide)).truncate 8) ∗
    ((fsp + 0xff9#64) ↦₈ (coinWord t 25 (by decide)).truncate 8) ∗
    ((fsp + 0xffa#64) ↦₈ (coinWord t 26 (by decide)).truncate 8) ∗
    ((fsp + 0xffb#64) ↦₈ (coinWord t 27 (by decide)).truncate 8) ∗
    ((fsp + 0xffc#64) ↦₈ (coinWord t 28 (by decide)).truncate 8) ∗
    ((fsp + 0xffd#64) ↦₈ (coinWord t 29 (by decide)).truncate 8) ∗
    ((fsp + 0xffe#64) ↦₈ (coinWord t 30 (by decide)).truncate 8) ∗
    ((fsp + 0xfff#64) ↦₈ (coinWord t 31 (by decide)).truncate 8) =
      ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) := by
  simp only [coinWord_truncate8]
  conv_rhs => rw [vec32_chunks4_eq (initiateKemCoins t)]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  dsimp only [List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  simp only [← pack4_bytes_eq, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem p32_4 {p0 p1 p2 p3 : BitVec 64} {w0 w1 w2 w3 : BitVec 32} {R R' : SepProp}
    (h : R ⊢ R') :
    (p0 ↦₃₂ w0) ∗ (p1 ↦₃₂ w1) ∗ (p2 ↦₃₂ w2) ∗ (p3 ↦₃₂ w3) ∗ R ⊢
      memRegion p0 4 ∗ memRegion p1 4 ∗ memRegion p2 4 ∗ memRegion p3 4 ∗ R' :=
  sepConj_mono (pointsTo32_entails_memRegion p0 w0)
    (sepConj_mono (pointsTo32_entails_memRegion p1 w1)
      (sepConj_mono (pointsTo32_entails_memRegion p2 w2)
        (sepConj_mono (pointsTo32_entails_memRegion p3 w3) h)))

private theorem mem4_elim_bytes {prog : Program} {ret : BitVec 64} {s : State}
    {p : BitVec 64} {B R : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ u0 u1 u2 u3 : BitVec 8,
      SepWPp prog ret s
        (B ∗ ((p ↦₈ u0) ∗ ((p + 1#64) ↦₈ u1) ∗ ((p + 2#64) ↦₈ u2) ∗ ((p + 3#64) ↦₈ u3) ∗ R))
        Q Qp oom) :
    SepWPp prog ret s ((memRegion p 4 ∗ B) ∗ R) Q Qp oom := by
  rw [sepConj_assoc, memRegion4_split1 p]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact sepWPp_exists_elim_oom fun u0 => sepWPp_exists_elim_oom fun u1 =>
    sepWPp_exists_elim_oom fun u2 => sepWPp_exists_elim_oom fun u3 =>
      sepWPp_conseq_oom (by sep_frame) (h u3 u2 u1 u0)

private theorem scratch96_collapse (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21
      w22 w23 : BitVec 32) :
    memRegion fsp 8 ∗
      ((fsp + 0x68#64) ↦₃₂ w0) ∗ ((fsp + 0x60#64) ↦₃₂ w1) ∗
      ((fsp + 0x5c#64) ↦₃₂ w2) ∗ ((fsp + 0x58#64) ↦₃₂ w3) ∗
      ((fsp + 0x54#64) ↦₃₂ w4) ∗ ((fsp + 0x50#64) ↦₃₂ w5) ∗
      ((fsp + 0x4c#64) ↦₃₂ w6) ∗ ((fsp + 0x48#64) ↦₃₂ w7) ∗
      ((fsp + 0x44#64) ↦₃₂ w8) ∗ ((fsp + 0x40#64) ↦₃₂ w9) ∗
      ((fsp + 0x3c#64) ↦₃₂ w10) ∗ ((fsp + 0x38#64) ↦₃₂ w11) ∗
      ((fsp + 0x34#64) ↦₃₂ w12) ∗ ((fsp + 0x30#64) ↦₃₂ w13) ∗
      ((fsp + 0x2c#64) ↦₃₂ w14) ∗ ((fsp + 0x28#64) ↦₃₂ w15) ∗
      ((fsp + 0x24#64) ↦₃₂ w16) ∗ ((fsp + 0x20#64) ↦₃₂ w17) ∗
      ((fsp + 0x1c#64) ↦₃₂ w18) ∗ ((fsp + 0x18#64) ↦₃₂ w19) ∗
      ((fsp + 0x14#64) ↦₃₂ w20) ∗ ((fsp + 0x10#64) ↦₃₂ w21) ∗
      ((fsp + 0x0c#64) ↦₃₂ w22) ∗ ((fsp + 0x08#64) ↦₃₂ w23) ∗
      memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ⊢
      memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 := by
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
      (p32_4 (p32_4 (p32_4 (p32_4 (p32_4 (p32_4 (Entails.refl _)))))))) ?_
  have hlow :
      memRegion fsp 8 ∗ memRegion (fsp + 0x08#64) 4 ∗ memRegion (fsp + 0x0c#64) 4 ∗
      memRegion (fsp + 0x10#64) 4 ∗ memRegion (fsp + 0x14#64) 4 ∗ memRegion (fsp + 0x18#64) 4 ∗
      memRegion (fsp + 0x1c#64) 4 ∗ memRegion (fsp + 0x20#64) 4 ∗ memRegion (fsp + 0x24#64) 4 ∗
      memRegion (fsp + 0x28#64) 4 ∗ memRegion (fsp + 0x2c#64) 4 ∗ memRegion (fsp + 0x30#64) 4 ∗
      memRegion (fsp + 0x34#64) 4 ∗ memRegion (fsp + 0x38#64) 4 ∗ memRegion (fsp + 0x3c#64) 4 ∗
      memRegion (fsp + 0x40#64) 4 ∗ memRegion (fsp + 0x44#64) 4 ∗ memRegion (fsp + 0x48#64) 4 ∗
      memRegion (fsp + 0x4c#64) 4 ∗ memRegion (fsp + 0x50#64) 4 ∗ memRegion (fsp + 0x54#64) 4 ∗
      memRegion (fsp + 0x58#64) 4 ∗ memRegion (fsp + 0x5c#64) 4 = memRegion fsp 0x60 := by
    rw [memRegion_merge_at (fsp + 0x58#64) 4 4 (fsp + 0x5c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x54#64) 4 8 (fsp + 0x58#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x50#64) 4 12 (fsp + 0x54#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x4c#64) 4 16 (fsp + 0x50#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x48#64) 4 20 (fsp + 0x4c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x44#64) 4 24 (fsp + 0x48#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x40#64) 4 28 (fsp + 0x44#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x3c#64) 4 32 (fsp + 0x40#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x38#64) 4 36 (fsp + 0x3c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x34#64) 4 40 (fsp + 0x38#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x30#64) 4 44 (fsp + 0x34#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x2c#64) 4 48 (fsp + 0x30#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x28#64) 4 52 (fsp + 0x2c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x24#64) 4 56 (fsp + 0x28#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x20#64) 4 60 (fsp + 0x24#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x1c#64) 4 64 (fsp + 0x20#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x18#64) 4 68 (fsp + 0x1c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x14#64) 4 72 (fsp + 0x18#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x10#64) 4 76 (fsp + 0x14#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x0c#64) 4 80 (fsp + 0x10#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0x08#64) 4 84 (fsp + 0x0c#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at fsp 8 88 (fsp + 0x08#64) (by clear * -; bv_omega) (by decide)]
  have h60 := memRegion_merge_at (fsp + 0x60#64) 4 4 (fsp + 0x64#64) (by clear * -; bv_omega) (by decide)
  have h68 := memRegion_merge_at (fsp + 0x68#64) 4 4 (fsp + 0x6c#64) (by clear * -; bv_omega) (by decide)
  rw [← hlow, ← h60, ← h68]; sep_frame

set_option maxHeartbeats 1600000 in
/-- Stack-parameterized Stage 3 KEM seed packing and `kyber::encapsulate` (`+0x0ee8 → +0x0fb4`). -/
theorem kem_encaps_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 se : State} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (cfStk : Nat) (hcfStk : cfStk ≤ stk - cliInitiateFrame)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 se 0xee8) (htr : se.trace = s0.trace)
    (hx20 : se.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : se.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx25 : se.readReg64 (.gpr 25#5) = (coinWord (padCoins x.coins) 24 (by decide)).setWidth 64)
    (hx22 : se.readReg64 (.gpr 22#5) = (coinWord (padCoins x.coins) 25 (by decide)).setWidth 64)
    (hx26 : se.readReg64 (.gpr 26#5) = (coinWord (padCoins x.coins) 26 (by decide)).setWidth 64)
    (hx23 : se.readReg64 (.gpr 23#5) = (coinWord (padCoins x.coins) 27 (by decide)).setWidth 64)
    (hx27 : se.readReg64 (.gpr 27#5) = (coinWord (padCoins x.coins) 28 (by decide)).setWidth 64)
    (hx28 : se.readReg64 (.gpr 28#5) = (coinWord (padCoins x.coins) 29 (by decide)).setWidth 64)
    (hx24 : se.readReg64 (.gpr 24#5) = (coinWord (padCoins x.coins) 30 (by decide)).setWidth 64)
    (hnext : ∀ sf : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      InInitiatePlaced s0 sf 0xfb4 → sf.trace = s0.trace →
      sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim st sf ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
          memRegion (fsp + 0x1c40#64) 32 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) se
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st se ∗ stackAt fsp cfStk ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cfStk) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗ memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗ ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom := by
  dsimp only
  set fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  set t := padCoins x.coins
  obtain ⟨_, _, _, _, _, _, hkpk_eq, _⟩ := bundleEOf_props hs3.bundleEq
  have hsub_pq : pqxdhEntryStack ≤ stk - cliInitiateFrame :=
    Nat.le_trans (by decide) (stk_sub_ge_base hstk)
  have hstk_le64 := stk_sub_le_2pow64 hstk64
  have hfe0_split : memRegion (fsp + 0xfe0#64) 32 =
      memRegion (fsp + 0xfe0#64) 4 ∗ memRegion (fsp + 0xfe4#64) 4 ∗
      memRegion (fsp + 0xfe8#64) 4 ∗ memRegion (fsp + 0xfec#64) 4 ∗
      memRegion (fsp + 0xff0#64) 4 ∗ memRegion (fsp + 0xff4#64) 4 ∗
      memRegion (fsp + 0xff8#64) 4 ∗ memRegion (fsp + 0xffc#64) 4 ∗ emp := by
    rw [sepConj_emp,
        memRegion_merge_at (fsp + 0xff8#64) 4 4 (fsp + 0xffc#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xff4#64) 4 8 (fsp + 0xff8#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xff0#64) 4 12 (fsp + 0xff4#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfec#64) 4 16 (fsp + 0xff0#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe8#64) 4 20 (fsp + 0xfec#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe4#64) 4 24 (fsp + 0xfe8#64) (by clear * -; bv_omega) (by decide),
        memRegion_merge_at (fsp + 0xfe0#64) 4 28 (fsp + 0xfe4#64) (by clear * -; bv_omega) (by decide)]
  refine sepWPp_conseq_oom
    (sep_replace (Entails.of_eq hfe0_split) (by dsimp only [fsp]; sep_frame) (Entails.refl _)) ?_
  refine mem4_elim_bytes fun u0 u1 u2 u3 =>
    mem4_elim_bytes fun u4 u5 u6 u7 =>
    mem4_elim_bytes fun u8 u9 u10 u11 =>
    mem4_elim_bytes fun u12 u13 u14 u15 =>
    mem4_elim_bytes fun u16 u17 u18 u19 =>
    mem4_elim_bytes fun u20 u21 u22 u23 =>
    mem4_elim_bytes fun u24 u25 u26 u27 =>
    mem4_elim_bytes fun u28 u29 u30 u31 => ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd, emp_sepConj, sepConj_assoc]
  obtain ⟨halign_e, _, hfsp_e⟩ := hctrl.step_ctx fsp
  refine' s3_block_in_vm_placed hh 0xf50
    (Φ := fun sm =>
      sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
      sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
    hctrl ?_ ?_; rotate_left 1
  · have hpc : se.pc = (blkPl_521).base + BitVec.ofNat 64 0xee8 := hctrl.pc
    have hrun := hctrl.run
    dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
    (try dsimp only [fsp] at *); rw [← hctrl.sp] at *
    try simp only [arm64_norm, wp_norm] at hx20 hx21 hx25 hx22 hx26 hx23 hx27 hx28 hx24
    by_vm_steps (
      wp_steps
      refine s3_done_in_vm (by wp_norm_lhs) (Entails.refl _)
        ⟨by wp_norm_goal, by wp_norm_goal,
         by simp only [hx20, arm64_norm, wp_norm],
         by simp only [hx21, arm64_norm, wp_norm]⟩
        (hpc := by (try wp_norm_goal); try (clear * -; bv_omega)))
  · intro sm1 hvm1 htr1 hctrl1 ⟨hx0_1, hx1_1, hx20_1, hx21_1⟩
    rw [hctrl.sp] at *
    (try iterate 6 rw [BitVec.add_comm _ fsp])
    (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
    obtain ⟨halign_1, _, hfsp_1⟩ := hctrl1.step_ctx fsp
    refine' s3_block_to_call_vm_placed hh
      (lsρ lsKemEncapsSym)
      0xfb4 (Φ := fun sm =>
        sm.readReg64 .x0 = fsp + 0x9c0#64 ∧ sm.readReg64 .x1 = fsp + 0xfe0#64 ∧
        sm.readReg64 .x8 = fsp + 0x1600#64 ∧
        sm.readReg64 (.gpr 20#5) = fsp + 0x348#64 ∧ sm.readReg64 (.gpr 21#5) = fsp + 0x388#64)
      hctrl1 ?_ ?_; rotate_left 1
    · have hpc : sm1.pc = (blkPl_521).base + BitVec.ofNat 64 0xf50 := hctrl1.pc
      have hrun := hctrl1.run
      dsimp only [initPcPlaced, initEntryPlaced, initProgPlaced, initProgExtPlaced, lsProg_521, BitVec.ofNat_eq_ofNat] at hpc ⊢
      (try dsimp only [fsp] at *); rw [← hctrl1.sp] at *
      try simp only [arm64_norm, wp_norm] at hx0_1 hx1_1 hx20_1 hx21_1
      by_vm_steps (
        wp_steps
        refine s3_done_call_vm (by wp_norm_lhs) (Entails.refl _)
          ⟨by simp only [hx0_1, arm64_norm, wp_norm],
           by simp only [hx1_1, arm64_norm, wp_norm],
           by wp_norm_goal,
           by simp only [hx20_1, arm64_norm, wp_norm],
           by simp only [hx21_1, arm64_norm, wp_norm]⟩
          (hpc := by (try wp_norm_goal); try (clear * -; bv_omega))
          (hlr := by (try wp_norm_goal); try (clear * -; bv_omega)))
    · intro sm2 hvm2 hc2 hp2 hl2 ht2 ⟨hx0_2, hx1_2, hx8_2, hx20_2, hx21_2⟩
      rw [hctrl1.sp] at *
      (try iterate 6 rw [BitVec.add_comm _ fsp])
      (try iterate 6 rw [BitVec.add_comm _ (s0.sp - BitVec.ofNat 64 cliInitiateFrame)])
      have htr2 : sm2.trace = s0.trace := ht2.trans (htr1.trans htr)
      have hstk_merge :
          stackAt fsp cfStk ∗
            memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
              (stk - cliInitiateFrame - cfStk) =
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
            (pqxdhEntryStack - pqxdhHookStack) ∗
          stackAt fsp pqxdhHookStack := by
        rw [sepConj_comm (stackAt fsp cfStk),
            ← stackAt_sub_split_init fsp hcfStk hstk_le64,
            stackAt_sub_split_init fsp hsub_pq hstk_le64,
            stackAt_sub_split_init fsp (by decide : pqxdhHookStack ≤ pqxdhEntryStack) (by decide),
            ← sepConj_assoc]
      have hout1600 :
          ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
            memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ⊢
            memRegion (fsp + 0x1600#64) 1600 ∗ memRegion (fsp + 0x1c40#64) 32 := by
        refine Entails.trans (sepConj_mono_left (pointsTo32_entails_memRegion _ _)) ?_
        rw [← memRegion_merge_at (fsp + 0x1618#64) 1576 32 (fsp + 0x1c40#64) (by clear * -; bv_omega) (by decide),
            ← sepConj_assoc, ← sepConj_assoc,
            memRegion_merge_at (fsp + 0x1600#64) 4 20 (fsp + 0x1604#64) (by clear * -; bv_omega) (by decide),
            memRegion_merge_at (fsp + 0x1600#64) (4 + 20) 1576 (fsp + 0x1618#64) (by clear * -; bv_omega) (by decide)]
        exact Entails.refl _
      let g : KyberEncapsCall :=
        { pkPtr := fsp + 0x9c0#64
          pk1568 := toU8 be.kpkPub.toList
          coinsPtr := fsp + 0xfe0#64
          coins32 := toU8 (initiateKemCoins t).toList
          outPtr := fsp + 0x1600#64 }
      obtain ⟨h_some, h_out⟩ := kemEncaps_out_eq X ⟨W.C, W.Q⟩ be t
      have hpk_bv : bytesToBv8 g.pk1568 = x.bundle.kpk := by
        dsimp only [g]; rw [bytesToBv8_toU8_eq, hkpk_eq]
      have hcoins_bv : bytesToBv8 g.coins32 = (initiateKemCoins t).toList :=
        bytesToBv8_toU8_eq _
      have hpk_len : g.pk1568.length = 1568 := by
        dsimp only [g, toU8]; simp [be.kpkPub.toList_length]
      have hcoins_len : g.coins32.length = 32 := by
        dsimp only [g, toU8]; simp [(initiateKemCoins t).toList_length]
      have hcollapse_pre := scratch96_collapse fsp
        (coinWord t 0 (by decide)) (coinWord t 1 (by decide)) (coinWord t 2 (by decide))
        (coinWord t 3 (by decide)) (coinWord t 4 (by decide)) (coinWord t 5 (by decide))
        (coinWord t 6 (by decide)) (coinWord t 7 (by decide)) (coinWord t 8 (by decide))
        (coinWord t 9 (by decide)) (coinWord t 10 (by decide)) (coinWord t 11 (by decide))
        (coinWord t 12 (by decide)) (coinWord t 13 (by decide)) (coinWord t 14 (by decide))
        (coinWord t 15 (by decide)) (coinWord t 16 (by decide)) (coinWord t 17 (by decide))
        (coinWord t 18 (by decide)) (coinWord t 19 (by decide)) (coinWord t 20 (by decide))
        (coinWord t 21 (by decide)) (coinWord t 22 (by decide)) (coinWord t 23 (by decide))
      refine s3_call_placed hh (kyberEncaps_ok_at_init_placed mmpl gh W X hh) g _
        hc2 htr2 hp2 hl2 hpanic
        (by
          simp only [withVmPreserved, kyberEncapsStubSpec, hpk_bv, hcoins_bv, hc2.sp, sepConj_assoc]
          dsimp only [g, fsp] at hx0_2 hx1_2 hx8_2 ⊢
          refine Entails.pure_right ⟨hx0_2, hx1_2, hx8_2, hpk_len, hcoins_len, h_some⟩ ?_
          have hkem := kemCoins32_pointsTo_eq (s0.sp - BitVec.ofNat 64 cliInitiateFrame) t
          dsimp only [t, fsp] at hkem hcollapse_pre hout1600 hstk_merge ⊢
          refine sep_replace hcollapse_pre (by sep_frame) ?_
          refine sep_replace hout1600 (by sep_frame) ?_
          refine sep_replace (Entails.of_eq hkem) (by sep_frame) ?_
          refine sep_replace (Entails.of_eq hstk_merge) (by sep_frame) ?_
          simp only [sepConj_assoc]
          sep_frame) ?_ ?_ ?_ ?_
      · intro _ _ h; simp [withVmPreserved, kyberEncapsStubSpec, Spec.onPanic] at h
      · intro _ _ _ h; simp [withVmPreserved, kyberEncapsStubSpec, Spec.onExit] at h
      · intro _ _ h; simp [withVmPreserved, kyberEncapsStubSpec, Spec.onOom] at h
      · intro sf _ _ _ hcs_f _ hof
        simp only [withVmPreserved, kyberEncapsStubSpec, hpk_bv, hcoins_bv, h_out, hc2.sp,
          sepConj_assoc]
        refine sepWPp_pure_elim_oom fun hvm_f => sepWPp_pure_elim_oom fun htr_f => ?_
        have hpool_f : A.pool lim st se = A.pool lim st sf :=
          ((A.pool_transport lim st se sm1 hvm1).symm.trans
            (A.pool_transport lim st sm1 sm2 hvm2).symm).trans
            (A.pool_transport lim st sm2 sf hvm_f).symm
        let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
        let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
        have hout_split :
            ((fsp + 0x1600#64) ↦ₛ (ct.toList ++ ss.toList)) =
              ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗ ((fsp + 0x1c20#64) ↦ₛ ss.toList) := by
          rw [pointsToBytes_append, ct.toList_length]
          simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
        have hstk_back :
            memRegion (fsp - BitVec.ofNat 64 pqxdhEntryStack)
                (pqxdhEntryStack - pqxdhHookStack) ∗ stackAt fsp pqxdhHookStack =
              stackAt fsp pqxdhEntryStack :=
          (stackAt_sub_split_init fsp (by decide : pqxdhHookStack ≤ pqxdhEntryStack) (by decide)).symm
        refine sepWPp_conseq_oom ?_
          (hnext sf (hof htr_f) (htr_f.trans htr2)
            (hcs_f.2.1.trans hx20_2) (hcs_f.2.2.1.trans hx21_2))
        dsimp only [g, fsp, ct, ss, t] at h_out hout_split hstk_back ⊢
        rw [hpool_f, h_out, hout_split]
        exact sep_replace (Entails.of_eq hstk_back) (by sep_frame) (by sep_frame)

theorem kem_encaps_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 se : State} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 se 0xee8) (htr : se.trace = s0.trace)
    (hx20 : se.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : se.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx25 : se.readReg64 (.gpr 25#5) = (coinWord (padCoins x.coins) 24 (by decide)).setWidth 64)
    (hx22 : se.readReg64 (.gpr 22#5) = (coinWord (padCoins x.coins) 25 (by decide)).setWidth 64)
    (hx26 : se.readReg64 (.gpr 26#5) = (coinWord (padCoins x.coins) 26 (by decide)).setWidth 64)
    (hx23 : se.readReg64 (.gpr 23#5) = (coinWord (padCoins x.coins) 27 (by decide)).setWidth 64)
    (hx27 : se.readReg64 (.gpr 27#5) = (coinWord (padCoins x.coins) 28 (by decide)).setWidth 64)
    (hx28 : se.readReg64 (.gpr 28#5) = (coinWord (padCoins x.coins) 29 (by decide)).setWidth 64)
    (hx24 : se.readReg64 (.gpr 24#5) = (coinWord (padCoins x.coins) 30 (by decide)).setWidth 64)
    (hnext : ∀ sf : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      InInitiatePlaced s0 sf 0xfb4 → sf.trace = s0.trace →
      sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim st sf ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
          memRegion (fsp + 0x1c40#64) 32 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) se
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st se ∗ stackAt fsp cliCoinsFillStack ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStack) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗ memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗ ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  kem_encaps_placed_ok_at cliCoinsFillStack
    (Nat.le_trans (by decide) (stk_sub_ge_base hstk))
    hh hstk hstk64 hs3 hpanic hctrl htr hx20 hx21 hx25 hx22 hx26 hx23 hx27 hx28 hx24 hnext

theorem kem_encaps_hooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr secretsPtr : BitVec 64} {opkId : BitVec 32}
    {dh1 dh2 dh3 : SignalPqxdh.Bytes} {dh4? : Option SignalPqxdh.Bytes}
    {stk : Nat} {s0 s3 se : State} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hs3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hctrl : InInitiatePlaced s0 se 0xee8) (htr : se.trace = s0.trace)
    (hx20 : se.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64)
    (hx21 : se.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64)
    (hx25 : se.readReg64 (.gpr 25#5) = (coinWord (padCoins x.coins) 24 (by decide)).setWidth 64)
    (hx22 : se.readReg64 (.gpr 22#5) = (coinWord (padCoins x.coins) 25 (by decide)).setWidth 64)
    (hx26 : se.readReg64 (.gpr 26#5) = (coinWord (padCoins x.coins) 26 (by decide)).setWidth 64)
    (hx23 : se.readReg64 (.gpr 23#5) = (coinWord (padCoins x.coins) 27 (by decide)).setWidth 64)
    (hx27 : se.readReg64 (.gpr 27#5) = (coinWord (padCoins x.coins) 28 (by decide)).setWidth 64)
    (hx28 : se.readReg64 (.gpr 28#5) = (coinWord (padCoins x.coins) 29 (by decide)).setWidth 64)
    (hx24 : se.readReg64 (.gpr 24#5) = (coinWord (padCoins x.coins) 30 (by decide)).setWidth 64)
    (hnext : ∀ sf : State,
      let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
      let t := padCoins x.coins
      let ct := (W.Q.encaps be.kpkPub (initiateKemCoins t)).1
      let ss := (W.Q.encaps be.kpkPub (initiateKemCoins t)).2
      InInitiatePlaced s0 sf 0xfb4 → sf.trace = s0.trace →
      sf.readReg64 (.gpr 20#5) = fsp + 0x348#64 →
      sf.readReg64 (.gpr 21#5) = fsp + 0x388#64 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) sf
        (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
          A.pool lim st sf ∗ stackAt fsp pqxdhEntryStack ∗
          memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
            (stk - cliInitiateFrame - pqxdhEntryStack) ∗
          A.live secretsPtr 192 1 ∗
          (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
          dhRemAt secretsPtr dh4? ∗
          memRegion fsp 0x60 ∗ memRegion (fsp + 0x60#64) 8 ∗ memRegion (fsp + 0x68#64) 8 ∗
          ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
          stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
          memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
          memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
          ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗
          ((fsp + 0xfe0#64) ↦ₛ (initiateKemCoins t).toList) ∗
          memRegion (fsp + 0x1000#64) 0x600 ∗
          ((fsp + 0x1600#64) ↦ₛ ct.toList) ∗
          ((fsp + 0x1c20#64) ↦ₛ ss.toList) ∗
          memRegion (fsp + 0x1c40#64) 32 ∗
          ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
          ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
        Q Qp oom) :
    let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
    let t := padCoins x.coins
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) se
      (S3InvPrefixPlaced A x s0 ∗ coinsCursorAtPlaced x.coinsP x.coins 160 ∗
        A.pool lim st se ∗ stackAt fsp cliCoinsFillStackPlaced ∗
        memRegion (fsp - BitVec.ofNat 64 (stk - cliInitiateFrame))
          (stk - cliInitiateFrame - cliCoinsFillStackPlaced) ∗
        A.live secretsPtr 192 1 ∗ (secretsPtr ↦ₛ bytesToBv8 (dhPrefix dh1 dh2 dh3 dh4?)) ∗
        dhRemAt secretsPtr dh4? ∗ memRegion fsp 8 ∗
        ((fsp + 0x68#64) ↦₃₂ coinWord t 0 (by decide)) ∗ ((fsp + 0x60#64) ↦₃₂ coinWord t 1 (by decide)) ∗
        ((fsp + 0x5c#64) ↦₃₂ coinWord t 2 (by decide)) ∗ ((fsp + 0x58#64) ↦₃₂ coinWord t 3 (by decide)) ∗
        ((fsp + 0x54#64) ↦₃₂ coinWord t 4 (by decide)) ∗ ((fsp + 0x50#64) ↦₃₂ coinWord t 5 (by decide)) ∗
        ((fsp + 0x4c#64) ↦₃₂ coinWord t 6 (by decide)) ∗ ((fsp + 0x48#64) ↦₃₂ coinWord t 7 (by decide)) ∗
        ((fsp + 0x44#64) ↦₃₂ coinWord t 8 (by decide)) ∗ ((fsp + 0x40#64) ↦₃₂ coinWord t 9 (by decide)) ∗
        ((fsp + 0x3c#64) ↦₃₂ coinWord t 10 (by decide)) ∗ ((fsp + 0x38#64) ↦₃₂ coinWord t 11 (by decide)) ∗
        ((fsp + 0x34#64) ↦₃₂ coinWord t 12 (by decide)) ∗ ((fsp + 0x30#64) ↦₃₂ coinWord t 13 (by decide)) ∗
        ((fsp + 0x2c#64) ↦₃₂ coinWord t 14 (by decide)) ∗ ((fsp + 0x28#64) ↦₃₂ coinWord t 15 (by decide)) ∗
        ((fsp + 0x24#64) ↦₃₂ coinWord t 16 (by decide)) ∗ ((fsp + 0x20#64) ↦₃₂ coinWord t 17 (by decide)) ∗
        ((fsp + 0x1c#64) ↦₃₂ coinWord t 18 (by decide)) ∗ ((fsp + 0x18#64) ↦₃₂ coinWord t 19 (by decide)) ∗
        ((fsp + 0x14#64) ↦₃₂ coinWord t 20 (by decide)) ∗ ((fsp + 0x10#64) ↦₃₂ coinWord t 21 (by decide)) ∗
        ((fsp + 0x0c#64) ↦₃₂ coinWord t 22 (by decide)) ∗ ((fsp + 0x08#64) ↦₃₂ coinWord t 23 (by decide)) ∗
        memRegion (fsp + 0x64#64) 4 ∗ memRegion (fsp + 0x6c#64) 4 ∗
        ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
        stage3KeySlotsAt A.repAlloc fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
        memRegion (fsp + 0x930#64) 8 ∗ memRegion (fsp + 0x938#64) 0x20 ∗
        memRegion (fsp + 0x958#64) 0x48 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
        ((fsp + 0x9c0#64) ↦ₛ x.bundle.kpk) ∗ memRegion (fsp + 0xfe0#64) 32 ∗
        memRegion (fsp + 0x1000#64) 0x600 ∗ ((fsp + 0x1600#64) ↦₃₂ coinWord t 31 (by decide)) ∗
        memRegion (fsp + 0x1604#64) 20 ∗ memRegion (fsp + 0x1618#64) 0x648 ∗
        ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
        ((fsp + 0x1c70#64) ↦₆₄ dhLenWord dh4?) ∗ memRegion (fsp + 0x1c78#64) 0x18)
      Q Qp oom :=
  kem_encaps_placed_ok_at cliCoinsFillStackPlaced
    (Nat.le_trans (by decide) (stk_sub_ge_base hstk))
    hh hstk hstk64 hs3 hpanic hctrl htr hx20 hx21 hx25 hx22 hx26 hx23 hx27 hx28 hx24 hnext

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.KemEncapsPlacedBudget
