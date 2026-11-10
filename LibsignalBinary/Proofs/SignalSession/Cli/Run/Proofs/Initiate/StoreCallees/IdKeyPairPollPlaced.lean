/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LscroKitPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.PollCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPoll
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import all Init.Data.String.Defs

/-!
# `IdentityFiles::get_identity_key_pair::{closure#0}` (`[LibsignalPlacement]`, Block `567`)

Verifies `idKeyPairPoll_placed_ok_of_deps` on `lsProg_567 H` and `idKeyPairPoll_cli_placed_ok`
against `idKeyPairPollSpecPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
  withLsCodeRoLoaded extract_withLsCodeRoLoaded
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.StoreDefs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll.KpNorm

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local wp_norm]
  sp_setPC_pre sp_setMem_setPC_pre sp_writeVReg128_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre fs_writeVReg128_pre
  trace_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg64_writeVReg128_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_setPC_pre readReg_writeVReg128_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  readVReg128_writeReg_pre readVReg128_writeVReg128_pre
  pc_writeVReg128_pre pstate_writeVReg128_pre mem_writeVReg128_pre status_writeVReg128_pre
  speWord_one_eq okTagVec_eq_neg2 awc_speWord1_two awc_okTagVec_two
  extractLsb_append_lo extractLsb_append_hi

attribute [local arm64_norm]
  sp_setPC_pre sp_setMem_setPC_pre sp_writeVReg128_pre
  fs_setPC_pre fs_setMem_pre fs_setPState_pre
  fs_writeReg64_pre fs_writeReg32_pre fs_writeReg_pre fs_writeVReg128_pre
  trace_writeVReg128_pre trace_writeReg32_pre trace_writeReg_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg64_writeVReg128_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg32_writeVReg128_pre
  readReg_setPC_pre readReg_setMem_setPC_pre readReg_writeVReg128_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre readVReg128_writeReg32_pre
  readVReg128_writeReg_pre readVReg128_writeVReg128_pre
  pc_writeVReg128_pre pstate_writeVReg128_pre mem_writeVReg128_pre status_writeVReg128_pre
  speWord_one_eq okTagVec_eq_neg2 awc_speWord1_two awc_okTagVec_two
  extractLsb_append_lo extractLsb_append_hi

/-! ## Symbol Resolution and Frame Layout Helpers -/

private theorem kp567_dirGet_target [LibsignalPlacement] :
    (blkPl_567).ρ dirGetName = lsmpl.base 589 := by
  simp only [arm64_norm]

private theorem kp567_tryFrom_target [LibsignalPlacement] :
    (blkPl_567).ρ identityKeyPairTryFromName = lsmpl.base 84 := by
  simp only [arm64_norm]

private theorem close_panic_subgoal_placed (s0 : State) {sf : State} {t : List TraceEvent}
    {F R : SepProp}
    (hm : sf.mem ⊨ ((⌜(allocFailedEvent ∈ List.drop t.length sf.trace) ∧ t <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R)
    (htr : t = s0.trace) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  refine allowPanic_frame ?_ (by rwa [sepConj_assoc] at hm)
  rintro ⟨hfail, hpref⟩
  unfold allocFailedIn
  rw [htr] at hfail hpref
  exact ⟨hfail, hpref⟩

private theorem utf8_read_len_eq_placed : BitVec.ofNat 64 (utf8 "read").length = 4#64 := by
  decide +kernel

private theorem cells_22_kp_placed (sp : BitVec 64) :
    cells (sp - 176#64) 22 =
      (∃∗ v0 : BitVec 64, (sp - 176#64) ↦₆₄ v0) ∗
      memRegion (sp - 168#64) 72 ∗
      memRegion (sp - 96#64) 48 ∗
      (∃∗ s29 : BitVec 64, (sp - 48#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 40#64) ↦₆₄ s30) ∗
      (∃∗ s22 : BitVec 64, (sp - 32#64) ↦₆₄ s22) ∗
      (∃∗ s21 : BitVec 64, (sp - 24#64) ↦₆₄ s21) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  conv_lhs =>
    rw [show (22 : Nat) = 1 + 21 from rfl,
        ProofLib.cells_split_sub sp 176 168 1 21,
        show (21 : Nat) = 9 + 12 from rfl,
        ProofLib.cells_split_sub sp 168 96 9 12,
        show (12 : Nat) = 6 + 6 from rfl,
        ProofLib.cells_split_sub sp 96 48 6 6,
        show (6 : Nat) = 1 + 5 from rfl,
        ProofLib.cells_split_sub sp 48 40 1 5,
        show (5 : Nat) = 1 + 4 from rfl,
        ProofLib.cells_split_sub sp 40 32 1 4,
        show (4 : Nat) = 1 + 3 from rfl,
        ProofLib.cells_split_sub sp 32 24 1 3,
        show (3 : Nat) = 1 + 2 from rfl,
        ProofLib.cells_split_sub sp 24 16 1 2,
        show (2 : Nat) = 1 + 1 from rfl,
        ProofLib.cells_split_sub sp 16 8 1 1,
        ← ProofLib.memRegion_cells (sp - 168#64) 9 (by decide),
        ← ProofLib.memRegion_cells (sp - 96#64) 6 (by decide)]
  cells_unfold

private theorem getResultAt_err_sp_96_placed (A : RustAlloc) (sp : BitVec 64) :
    getResultAt A (sp - 96#64) (.error ()) =
      ∃∗ fnPtr : BitVec 64, ∃∗ sBs : List (BitVec 8), ∃∗ sCap : BitVec 64, ∃∗ sPtr : BitVec 64,
        ((sp - 96#64) ↦₆₄ speWord 1) ∗
        ((sp - 88#64) ↦₆₄ sCap) ∗ ((sp - 80#64) ↦₆₄ sPtr) ∗
        ((sp - 72#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((sp - 64#64) ↦₆₄ fnPtr) ∗ ((sp - 56#64) ↦₆₄ 4#64) ∗
        (fnPtr ↦ᵣ utf8 "read") := by
  dsimp only [getResultAt, speAt, vecU8, strRefAt]
  simp_rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
  dsimp only [vecHeader]
  rw [utf8_read_len_eq_placed]
  have e8 : sp - 96#64 + 8#64 = sp - 88#64 := by bv_omega
  have e16 : sp - 88#64 + 8#64 = sp - 80#64 := by bv_omega
  have e24 : sp - 88#64 + 16#64 = sp - 72#64 := by bv_omega
  have e32 : sp - 96#64 + 32#64 = sp - 64#64 := by bv_omega
  have e40 : sp - 64#64 + 8#64 = sp - 56#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    e8, e16, e24, e32, e40]

private theorem getResultAt_ok_sp_96_placed (A : RustAlloc) (sp : BitVec 64)
    (bs : List (BitVec 8)) :
    getResultAt A (sp - 96#64) (.ok bs) =
      ∃∗ bCap : BitVec 64, ∃∗ bPtr : BitVec 64,
        ⌜bs.length ≤ bCap.toNat ∧ bCap.toNat < 2 ^ 63 ∧ bPtr ≠ 0#64⌝ ∗
        ((sp - 96#64) ↦₆₄ okTagVec) ∗
        ((sp - 88#64) ↦₆₄ bCap) ∗ ((sp - 80#64) ↦₆₄ bPtr) ∗
        ((sp - 72#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (bPtr ↦ₛ bs) ∗ Store.IdTrustPoll.Helpers.vecU8BufRest A bCap bPtr bs.length ∗
        memRegion (sp - 64#64) 16 := by
  dsimp only [getResultAt, vecResultAt, vecU8]
  simp_rw [Store.IdTrustPoll.Helpers.vecU8At_eq_expose]
  have e8 : sp - 96#64 + 8#64 = sp - 88#64 := by bv_omega
  have e16 : sp - 88#64 + 8#64 = sp - 80#64 := by bv_omega
  have e24 : sp - 88#64 + 16#64 = sp - 72#64 := by bv_omega
  have e32 : sp - 96#64 + 32#64 = sp - 64#64 := by bv_omega
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    e8, e16, e24, e32]
  congr 1; funext bCap; congr 1; funext bPtr
  ac_rfl

private theorem sp_96_cells4_fold_48_placed (sp : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗
      ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3) ∗
      memRegion (sp - 64#64) 16 ⊢
    memRegion (sp - 96#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 40)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 8) (k := 32)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 8) (k := 24)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
    (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
        (sepConj_mono_left (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _)))))

private theorem sp_96_cells6_fold_48_placed (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ w0) ∗ ((sp - 88#64) ↦₆₄ w1) ∗
      ((sp - 80#64) ↦₆₄ w2) ∗ ((sp - 72#64) ↦₆₄ w3) ∗
      ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ⊢
    memRegion (sp - 96#64) 48 := by
  have h16 : ((sp - 64#64) ↦₆₄ w4) ∗ ((sp - 56#64) ↦₆₄ w5) ⊢ memRegion (sp - 64#64) 16 := by
    rw [ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 8)
          (b' := sp - 56#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
      (IsBlock.entails_memRegion (IsBlock.pointsTo64 _ _))
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h16))))
    (sp_96_cells4_fold_48_placed sp w0 w1 w2 w3)

private theorem sp_168_err_split_placed (sp : BitVec 64) :
    memRegion (sp - 168#64) 72 =
      (∃∗ b0 : BitVec 8, (sp - 168#64) ↦₈ b0) ∗
      memRegion (sp - 167#64) 7 ∗
      (∃∗ u0 : BitVec 64, (sp - 160#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (sp - 152#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (sp - 144#64) ↦₆₄ u2) ∗
      (∃∗ u3 : BitVec 64, (sp - 136#64) ↦₆₄ u3) ∗
      (∃∗ u4 : BitVec 64, (sp - 128#64) ↦₆₄ u4) ∗
      (∃∗ u5 : BitVec 64, (sp - 120#64) ↦₆₄ u5) ∗
      memRegion (sp - 112#64) 16 := by
  rw [ProofLib.memRegion_split' (b := sp - 168#64) (n := 1) (k := 71)
        (b' := sp - 167#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 167#64) (n := 7) (k := 64)
        (b' := sp - 160#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 160#64) (n := 8) (k := 56)
        (b' := sp - 152#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 152#64) (n := 8) (k := 48)
        (b' := sp - 144#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 144#64) (n := 8) (k := 40)
        (b' := sp - 136#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 136#64) (n := 8) (k := 32)
        (b' := sp - 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 128#64) (n := 8) (k := 24)
        (b' := sp - 120#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 120#64) (n := 8) (k := 16)
        (b' := sp - 112#64) rfl (by bv_omega) (by decide),
      memRegion_one (sp - 168#64),
      ProofLib.memRegion_eight (sp - 160#64),
      ProofLib.memRegion_eight (sp - 152#64),
      ProofLib.memRegion_eight (sp - 144#64),
      ProofLib.memRegion_eight (sp - 136#64),
      ProofLib.memRegion_eight (sp - 128#64),
      ProofLib.memRegion_eight (sp - 120#64)]

private theorem sp_168_err_fold_placed (A : RustAlloc) (sp sCap sPtr fnPtr : BitVec 64)
    (sBs : List (BitVec 8)) :
    ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
      ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
      ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
      SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
      ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
      (fnPtr ↦ᵣ utf8 "read") ∗
      memRegion (sp - 112#64) 16 ⊢
    idKeyPairOutAt A (sp - 168#64) (.error ()) := by
  dsimp only [idKeyPairOutAt]
  have e1 : sp - 168#64 + 1#64 = sp - 167#64 := by bv_omega
  have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
  have e56 : sp - 168#64 + 0x38#64 = sp - 112#64 := by bv_omega
  rw [e1, e8, e56]
  have htop :
      ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
        ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
        ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
        (fnPtr ↦ᵣ utf8 "read") ∗
        memRegion (sp - 112#64) 16 =
      ((sp - 168#64) ↦₈ 1#8) ∗ memRegion (sp - 167#64) 7 ∗
        (((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
          ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
          SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
          ((sp - 128#64) ↦₆₄ fnPtr) ∗ ((sp - 120#64) ↦₆₄ 4#64) ∗
          (fnPtr ↦ᵣ utf8 "read")) ∗
        memRegion (sp - 112#64) 16 := by
    ac_rfl
  rw [htop]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono ?_ (Entails.refl _)))
  refine Entails.sepExists_right (.proto (utf8 "read") .invalidState) ?_
  dsimp only [RunDrop.speOwnedAt, speAt]
  have h40 : ((sp - 120#64) ↦₆₄ 4#64) =
      ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) := by
    rw [utf8_read_len_eq_placed]
    have s40 : sp - 128#64 + 8#64 = sp - 120#64 := by bv_omega
    rw [s40]
  rw [h40]
  have s8 : sp - 160#64 + 8#64 = sp - 152#64 := by bv_omega
  have s32 : sp - 160#64 + 32#64 = sp - 128#64 := by bv_omega
  rw [s8, s32]
  have hvec :
      (((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
        ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
      SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ⊢
      ∃∗ bs : List (BitVec 8), vecU8 A (sp - 152#64) bs := by
    have heq :
        (((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
          ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs =
        vecU8At A (sp - 152#64) sCap sPtr sBs := by
      rw [SpqrV1.Alloc.vecU8At_eq_header_sep_buf]
      dsimp only [vecHeader]
      have v8 : sp - 152#64 + 8#64 = sp - 144#64 := by bv_omega
      have v16 : sp - 152#64 + 16#64 = sp - 136#64 := by bv_omega
      rw [v8, v16]
    rw [heq]
    exact Entails.sepExists_right sBs
      (Entails.sepExists_right sCap (Entails.sepExists_right sPtr (Entails.refl _)))
  have hstr :
      ((sp - 128#64) ↦₆₄ fnPtr) ∗
        ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") ⊢
      strRefAt (sp - 128#64) (utf8 "read") :=
    Entails.sepExists_right fnPtr (Entails.refl _)
  have hgrp :
      ((sp - 160#64) ↦₆₄ speWord 1) ∗ ((sp - 152#64) ↦₆₄ sCap) ∗
        ((sp - 144#64) ↦₆₄ sPtr) ∗ ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length) ∗
        SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs ∗
        ((sp - 128#64) ↦₆₄ fnPtr) ∗
        ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
        (fnPtr ↦ᵣ utf8 "read") =
      ((sp - 160#64) ↦₆₄ speWord 1) ∗
        ((((sp - 152#64) ↦₆₄ sCap) ∗ ((sp - 144#64) ↦₆₄ sPtr) ∗
          ((sp - 136#64) ↦₆₄ BitVec.ofNat 64 sBs.length)) ∗
          SpqrV1.Alloc.vecU8Buf A sCap sPtr sBs) ∗
        (((sp - 128#64) ↦₆₄ fnPtr) ∗
          ((sp - 128#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (utf8 "read").length) ∗
          (fnPtr ↦ᵣ utf8 "read")) := by
    ac_rfl
  refine Entails.trans (Entails.of_eq (by ac_rfl)) (Entails.trans (Entails.of_eq hgrp) ?_)
  exact sepConj_mono_right (sepConj_mono hvec hstr)

private theorem tryFrom_to_idKeyPairOutAt_placed (A : RustAlloc) (p : BitVec 64)
    (r : Except SignalProtocolError IdentityKeyPair) :
    identityKeyPairResultAt A p r ⊢
      idKeyPairOutAt A p (match r with | .ok kp => .ok kp | .error _ => .error ()) := by
  cases r with
  | ok kp =>
    exact Entails.refl _
  | error e =>
    dsimp only [identityKeyPairResultAt, idKeyPairOutAt]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
    exact Entails.sepExists_right (.proto [] e) (Entails.refl _)

private theorem memRegion_72_eq_cells9_placed (p : BitVec 64) :
    memRegion p 72 =
      (∃∗ w0 : BitVec 64, p ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (p + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (p + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (p + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (p + 32#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (p + 40#64) ↦₆₄ w5) ∗
      (∃∗ w6 : BitVec 64, (p + 48#64) ↦₆₄ w6) ∗
      (∃∗ w7 : BitVec 64, (p + 56#64) ↦₆₄ w7) ∗
      (∃∗ w8 : BitVec 64, (p + 64#64) ↦₆₄ w8) := by
  rw [memRegion_split p 8 64 (by decide),
    memRegion_split (p + 8#64) 8 56 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 48 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 8 40 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [ProofLib.memRegion_eight, BitVec.add_assoc]
  rfl

private theorem kp72_words_sp168_placed (sp out : BitVec 64) {bs : List (BitVec 8)}
    (hlen : bs.length = 72) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64),
      ((sp - 168#64) ↦ₛ bs) =
        ((sp - 168#64) ↦₆₄ w0) ∗ ((sp - 160#64) ↦₆₄ w1) ∗
        ((sp - 152#64) ↦₆₄ w2) ∗ ((sp - 144#64) ↦₆₄ w3) ∗
        ((sp - 136#64) ↦₆₄ w4) ∗ ((sp - 128#64) ↦₆₄ w5) ∗
        ((sp - 120#64) ↦₆₄ w6) ∗ ((sp - 112#64) ↦₆₄ w7) ∗
        ((sp - 104#64) ↦₆₄ w8) ∧
      (out ↦ₛ bs) =
        (out ↦₆₄ w0) ∗ ((out + 8#64) ↦₆₄ w1) ∗
        ((out + 16#64) ↦₆₄ w2) ∗ ((out + 24#64) ↦₆₄ w3) ∗
        ((out + 32#64) ↦₆₄ w4) ∗ ((out + 40#64) ↦₆₄ w5) ∗
        ((out + 48#64) ↦₆₄ w6) ∗ ((out + 56#64) ↦₆₄ w7) ∗
        ((out + 64#64) ↦₆₄ w8) := by
  obtain ⟨q3, q0, q1, q2, w8, hforall⟩ := PollCommon.pointsToBytes72_split_qwords hlen
  refine ⟨q3.extractLsb' 0 64, q3.extractLsb' 64 64,
          q0.extractLsb' 0 64, q0.extractLsb' 64 64,
          q1.extractLsb' 0 64, q1.extractLsb' 64 64,
          q2.extractLsb' 0 64, q2.extractLsb' 64 64, w8, ?_, ?_⟩
  · rw [hforall (sp - 168#64)]
    unfold Arm64.pointsTo128
    have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
    have e16 : sp - 168#64 + 16#64 = sp - 152#64 := by bv_omega
    have e24 : sp - 152#64 + 8#64 = sp - 144#64 := by bv_omega
    have e32 : sp - 168#64 + 32#64 = sp - 136#64 := by bv_omega
    have e40 : sp - 136#64 + 8#64 = sp - 128#64 := by bv_omega
    have e48 : sp - 168#64 + 48#64 = sp - 120#64 := by bv_omega
    have e56 : sp - 120#64 + 8#64 = sp - 112#64 := by bv_omega
    have e64 : sp - 168#64 + 64#64 = sp - 104#64 := by bv_omega
    rw [e16, e32, e48, e64, e8, e24, e40, e56]
    ac_rfl
  · rw [hforall out]
    unfold Arm64.pointsTo128
    have o24 : out + 16#64 + 8#64 = out + 24#64 := by bv_omega
    have o40 : out + 32#64 + 8#64 = out + 40#64 := by bv_omega
    have o56 : out + 48#64 + 8#64 = out + 56#64 := by bv_omega
    rw [o24, o40, o56]
    ac_rfl

private theorem kp72_words_fold_memRegion_placed (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 : BitVec 64) :
    ((sp - 168#64) ↦₆₄ w0) ∗ ((sp - 160#64) ↦₆₄ w1) ∗
      ((sp - 152#64) ↦₆₄ w2) ∗ ((sp - 144#64) ↦₆₄ w3) ∗
      ((sp - 136#64) ↦₆₄ w4) ∗ ((sp - 128#64) ↦₆₄ w5) ∗
      ((sp - 120#64) ↦₆₄ w6) ∗ ((sp - 112#64) ↦₆₄ w7) ∗
      ((sp - 104#64) ↦₆₄ w8) ⊢
    memRegion (sp - 168#64) 72 := by
  rw [memRegion_72_eq_cells9_placed (sp - 168#64)]
  have e8 : sp - 168#64 + 8#64 = sp - 160#64 := by bv_omega
  have e16 : sp - 168#64 + 16#64 = sp - 152#64 := by bv_omega
  have e24 : sp - 168#64 + 24#64 = sp - 144#64 := by bv_omega
  have e32 : sp - 168#64 + 32#64 = sp - 136#64 := by bv_omega
  have e40 : sp - 168#64 + 40#64 = sp - 128#64 := by bv_omega
  have e48 : sp - 168#64 + 48#64 = sp - 120#64 := by bv_omega
  have e56 : sp - 168#64 + 56#64 = sp - 112#64 := by bv_omega
  have e64 : sp - 168#64 + 64#64 = sp - 104#64 := by bv_omega
  rw [e8, e16, e24, e32, e40, e48, e56, e64]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right w3 (Entails.refl _))
          (sepConj_mono (Entails.sepExists_right w4 (Entails.refl _))
            (sepConj_mono (Entails.sepExists_right w5 (Entails.refl _))
              (sepConj_mono (Entails.sepExists_right w6 (Entails.refl _))
                (sepConj_mono (Entails.sepExists_right w7 (Entails.refl _))
                  (Entails.sepExists_right w8 (Entails.refl _)))))))))

private def kpPostAnsPlaced (A : RustAlloc) (out : BitVec 64)
    (expected : Except Unit IdentityKeyPair) (s0 sf : State) : SepProp :=
  ∃∗ ans : Except Unit IdentityKeyPair,
    ⌜ans = expected ∧ sf.trace = s0.trace⌝ ∗ idKeyPairOutAt A out ans

private theorem kpPostAnsPlaced_intro (A : RustAlloc) (out : BitVec 64)
    (expected ans : Except Unit IdentityKeyPair) (B : List (BitVec 8) → SepProp)
    (bs : List (BitVec 8)) (s0 sf : State)
    (hB : idKeyPairOutAt A out ans =
      ∃∗ bs' : List (BitVec 8), ⌜bs'.length = 72⌝ ∗ (out ↦ₛ bs') ∗ B bs')
    (hbs : bs.length = 72)
    (hpure : ans = expected ∧ sf.trace = s0.trace) :
    (out ↦ₛ bs) ∗ B bs ⊢ kpPostAnsPlaced A out expected s0 sf := by
  have htrue : ((ans = expected ∧ sf.trace = s0.trace) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hpure⟩
  have hlen_true : ((bs.length = 72) : Prop) = True :=
    propext ⟨fun _ => trivial, fun _ => hbs⟩
  unfold kpPostAnsPlaced
  refine Entails.sepExists_right ans ?_
  rw [htrue, pure_true, emp_sepConj, hB]
  refine Entails.sepExists_right bs ?_
  rw [hlen_true, pure_true, emp_sepConj]
  exact Entails.refl _

private theorem focus_kpPostAnsPlaced (A : RustAlloc) (out : BitVec 64)
    (expected ans : Except Unit IdentityKeyPair) (B : List (BitVec 8) → SepProp)
    (bs : List (BitVec 8)) (s0 : State)
    {prog : Program} {ret_pc : BitVec 64} {s_ret : State}
    {P R : SepProp} {post : State → SepProp → Prop}
    (hB : idKeyPairOutAt A out ans =
      ∃∗ bs' : List (BitVec 8), ⌜bs'.length = 72⌝ ∗ (out ↦ₛ bs') ∗ B bs')
    (hbs : bs.length = 72)
    (hf : P = ((out ↦ₛ bs) ∗ B bs) ∗ R)
    (hpure : ans = expected ∧ s_ret.trace = s0.trace)
    (hnext : SepWP prog ret_pc s_ret (kpPostAnsPlaced A out expected s0 s_ret ∗ R) post) :
    SepWP prog ret_pc s_ret P post :=
  SepWP.focus_weaken (kpPostAnsPlaced_intro A out expected ans B bs s0 s_ret hB hbs hpure)
    (hf := hf) hnext

/-! ## Inner Specification and Symbolic Execution (Block `567`) -/

private def cliIdKeyPairPollInnerPlacedSpec [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (calleeStk : Nat) :
    Spec IdOwnPollGhostPlaced where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "identity-key-pair")) ∧
      ∀ bs, x.own.get rd s.fs.files (utf8 "identity-key-pair") = .ok bs →
        bs.length < 2 ^ 32⌝ ∗
      (lsρ PollCommon.idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A x.self x.own ∗
      memRegion x.out 72 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
      stackAt (s.sp - 176#64) calleeStk ∗ cells (s.sp - 176#64) 22
  post := fun x s0 sf =>
    kpPostAnsPlaced A x.out ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files) s0 sf ∗
      (lsρ PollCommon.idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A x.self x.own ∗
      FromRecordCallees.lsLogOff ∗ A.pool ∗
      stackAt (s0.sp - 176#64) calleeStk ∗ cells (s0.sp - 176#64) 22
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private def cliIdKeyPairPollExpandedPlacedSpec [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (calleeStk : Nat) :
    Spec IdOwnPollGhostPlaced where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      x.own.path.length < 2 ^ 32 ∧
      pathOk (pathOf x.own.path (utf8 "identity-key-pair")) ∧
      ∀ bs, x.own.get rd s.fs.files (utf8 "identity-key-pair") = .ok bs →
        bs.length < 2 ^ 32⌝ ∗
      (lsρ PollCommon.idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 0#8) ∗
      dirAt A x.self x.own ∗
      memRegion x.out 72 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
      stackAt (s.sp - 176#64) calleeStk ∗
      ((∃∗ v0 : BitVec 64, (s.sp - 176#64) ↦₆₄ v0) ∗
        memRegion (s.sp - 168#64) 72 ∗
        memRegion (s.sp - 96#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s.sp - 48#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s.sp - 40#64) ↦₆₄ s30) ∗
        (∃∗ s22 : BitVec 64, (s.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s.sp - 8#64) ↦₆₄ s19))
  post := fun x s0 sf =>
    kpPostAnsPlaced A x.out ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files) s0 sf ∗
      (lsρ PollCommon.idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗
      dirAt A x.self x.own ∗
      FromRecordCallees.lsLogOff ∗ A.pool ∗
      stackAt (s0.sp - 176#64) calleeStk ∗
      ((∃∗ v0 : BitVec 64, (s0.sp - 176#64) ↦₆₄ v0) ∗
        memRegion (s0.sp - 168#64) 72 ∗
        memRegion (s0.sp - 96#64) 48 ∗
        (∃∗ s29 : BitVec 64, (s0.sp - 48#64) ↦₆₄ s29) ∗
        (∃∗ s30 : BitVec 64, (s0.sp - 40#64) ↦₆₄ s30) ∗
        (∃∗ s22 : BitVec 64, (s0.sp - 32#64) ↦₆₄ s22) ∗
        (∃∗ s21 : BitVec 64, (s0.sp - 24#64) ↦₆₄ s21) ∗
        (∃∗ s20 : BitVec 64, (s0.sp - 16#64) ↦₆₄ s20) ∗
        (∃∗ s19 : BitVec 64, (s0.sp - 8#64) ↦₆₄ s19))
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem cliIdKeyPairPollExpandedPlacedSpec_eq [LibsignalPlacement] (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustAlloc) (calleeStk : Nat) :
    cliIdKeyPairPollExpandedPlacedSpec rd pathOk A calleeStk =
      cliIdKeyPairPollInnerPlacedSpec rd pathOk A calleeStk := by
  unfold cliIdKeyPairPollExpandedPlacedSpec cliIdKeyPairPollInnerPlacedSpec
  congr 1
  · funext x s; rw [cells_22_kp_placed s.sp]
  · funext x s0 sf; rw [cells_22_kp_placed s0.sp]

set_option maxHeartbeats 1200000 in
private theorem idKeyPairPollInner_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hGet : subroutine_ok (lsProg_567 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok (lsProg_567 H) (lsmpl.base 84)
      (RecordCodecsBinary.identityKeyPairTryFromPlacedSpec A))
    (hhi : kpCalleeStk getStk ≤ 2 ^ 64) :
    subroutine_ok (lsProg_567 H) (blkPl_567).base
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (cliIdKeyPairPollInnerPlacedSpec rd pathOk A (kpCalleeStk getStk))) := by
  let calleeStk := kpCalleeStk getStk
  rw [← cliIdKeyPairPollExpandedPlacedSpec_eq]
  have hGetCells : subroutine_ok (lsProg_567 H) ((blkPl_567).ρ dirGetName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (PollCommon.dirGetRoCellsSpec rd pathOk A calleeStk)) :=
    kp567_dirGet_target.symm ▸ PollCommon.dirGetRo_cells_placed_ok (calleeStk := calleeStk)
      (subroutine_ok_rocl_of_withLsCodeRoLoaded hGet)
      (by dsimp [calleeStk, kpCalleeStk]; omega) hhi
  have hTryCells : subroutine_ok (lsProg_567 H) ((blkPl_567).ρ identityKeyPairTryFromName)
      (LibsignalPublicApi.StoreKit.withLsRoCl lsmpl
        (PollCommon.ikpTryFromCellsPlacedSpec A calleeStk)) :=
    kp567_tryFrom_target.symm ▸ PollCommon.ikpTryFrom_cells_placed_ok (calleeStk := calleeStk)
      (subroutine_ok_rocl_of_withLsCodeRoLoaded hDec)
      (by dsimp [calleeStk, kpCalleeStk]; omega) hhi
  have hDeallocCells := PollCommon.deallocAt_cells_placed_ok (prog := lsProg_567 H)
    (calleeStk := calleeStk) hC (by decide)
    (by dsimp [calleeStk, kpCalleeStk]; omega) hhi
  clear hGet hDec hC
  dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded]
  simp (config := { maxSteps := 2000000 }) only [cliIdKeyPairPollExpandedPlacedSpec,
    sepExists_sepConj_left, sepExists_sepConj_right]
  wpp_init x s0
  have hcrl0 : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hname_len : (utf8 "identity-key-pair").length = 17 := PollCommon.utf8_idKp_length
  have hname_lt : (utf8 "identity-key-pair").length < 2 ^ 32 := by
    rw [PollCommon.utf8_idKp_length]; decide
  apply sepWPp_of_sepWP_lscro hcrl0 (mid := (blkPl_567).ρ dirGetName)
  wp_steps
  apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
  intro hcrl1
  wp_call_lscro hGetCells hcrl1
    (s0.sp - 96#64, x.self, x.own,
      lsρ PollCommon.idKpFileNameSym, utf8 "identity-key-pair", s0.sp - 176#64)
  case panic =>
    intro sf_p _ hm
    dsimp only at hm
    exact close_panic_subgoal_placed s0 hm (by simp only [wp_norm, arm64_norm, *])
  have h_reg0 : sf.sp = s0.sp - 176#64 ∧
      sf.readReg64 (.gpr 19#5) = x.fut ∧
      sf.readReg64 (.gpr 20#5) = x.out ∧
      sf.readReg64 (.gpr 29#5) = s0.sp - 48#64 :=
    ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
     by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
  rcases h_reg0 with ⟨_, _, _, _⟩
  cases w with
  | error u =>
    cases u
    have hget_err : .error () = x.own.get rd s0.fs.files (utf8 "identity-key-pair") ∧
        sf.trace = s0.trace := ⟨by assumption, by assumption⟩
    have hans_err : (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files = .error () := by
      unfold IdGhost.keyPair
      rw [← hget_err.1]
      rfl
    apply SepWPp.of_sepWP_ret
    apply SepWP.focus_rw (getResultAt_err_sp_96_placed A s0.sp)
    wp_pull_exists
    apply SepWP.focus_rw (sp_168_err_split_placed s0.sp)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_weaken (sp_96_cells6_fold_48_placed s0.sp _ _ _ _ _ _)
    apply SepWP.focus_weaken (sp_168_err_fold_placed A s0.sp _ _ _ _)
    rcases PollCommon.reloc_idKeyPairOutAt A (.error ()) with ⟨B, hB⟩
    apply SepWP.focus_rw (hB (s0.sp - 168#64))
    wp_pull_exists
    apply SepWP.pure_elim; intro hbs72
    rcases kp72_words_sp168_placed s0.sp x.out hbs72 with
      ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hsp72, hout72⟩
    apply SepWP.focus_rw hsp72
    apply SepWP.focus_rw (memRegion_72_eq_cells9_placed x.out)
    wp_pull_exists
    wp_steps
    apply SepWP.focus_rw hout72.symm
    apply SepWP.focus_weaken (kp72_words_fold_memRegion_placed s0.sp w0 w1 w2 w3 w4 w5 w6 w7 w8)
    refine focus_kpPostAnsPlaced A x.out
      ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files)
      (.error ()) B _ s0 (hB x.out) hbs72 (by sep_focus) ?_ ?_
    · exact ⟨hans_err.symm, by simp only [wp_norm, arm64_norm, *]⟩
    wp_done
  | ok bs =>
    have hget_ok : .ok bs = x.own.get rd s0.fs.files (utf8 "identity-key-pair") ∧
        sf.trace = s0.trace := ⟨by assumption, by assumption⟩
    have hbs_lt32 : bs.length < 2 ^ 32 := by
      have hall : ∀ bs, x.own.get rd s0.fs.files (utf8 "identity-key-pair") = .ok bs →
          bs.length < 2 ^ 32 := by assumption
      exact hall bs hget_ok.1.symm
    have hx1_len : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      simp only [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    let ansOk : Except Unit IdentityKeyPair :=
      match IdentityKeyPair.tryFrom bs with
      | .ok kp => .ok kp
      | .error _ => .error ()
    have hans_ok : (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files = ansOk := by
      unfold IdGhost.keyPair
      rw [← hget_ok.1]
      rfl
    rw [getResultAt_ok_sp_96_placed A s0.sp bs]
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWPp.exists_elim; intro bCap
    apply SepWPp.exists_elim; intro bPtr
    apply SepWPp.pure_elim; rintro ⟨hbCap_le, hbCap_lt, hbPtr_ne⟩
    apply sepWPp_of_sepWP_lscro hcrl_sf (mid := (blkPl_567).ρ identityKeyPairTryFromName)
    wp_steps
    apply SepWP.focus_weaken (sp_96_cells4_fold_48_placed s0.sp _ _ _ _)
    apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
    intro hcrl_try
    wp_call_lscro hTryCells hcrl_try (bPtr, bs, s0.sp - 168#64, s0.sp - 176#64)
    case panic =>
      intro sf_p _ hm
      dsimp only at hm
      simpa only [sepConj_assoc] using
        close_panic_subgoal_placed s0 hm (by simp only [wp_norm, arm64_norm, *])
    have h_reg1 : sf_1.sp = s0.sp - 176#64 ∧
        sf_1.readReg64 (.gpr 19#5) = x.fut ∧
        sf_1.readReg64 (.gpr 20#5) = x.out ∧
        sf_1.readReg64 (.gpr 21#5) = bCap ∧
        sf_1.readReg64 (.gpr 22#5) = bPtr ∧
        sf_1.readReg64 (.gpr 29#5) = s0.sp - 48#64 :=
      ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
       by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    rcases h_reg1 with ⟨_, _, _, _, _, _⟩
    by_cases hc0 : bCap = 0#64
    · subst hc0
      have hbs_nil : bs = [] := by
        cases bs with
        | nil => rfl
        | cons _ _ => simp at hbCap_le
      subst hbs_nil
      apply SepWPp.of_sepWP_ret
      have hemp : ((bPtr ↦ₛ ([] : List (BitVec 8))) ∗
          Store.IdTrustPoll.Helpers.vecU8BufRest A 0#64 bPtr 0) = emp := by
        simp [Store.IdTrustPoll.Helpers.vecU8BufRest]
      apply SepWP.focus_rw hemp
      apply SepWP.focus_weaken (tryFrom_to_idKeyPairOutAt_placed A (s0.sp - 168#64)
        (IdentityKeyPair.tryFrom []))
      rcases PollCommon.reloc_idKeyPairOutAt A ansOk with ⟨B, hB⟩
      apply SepWP.focus_rw (hB (s0.sp - 168#64))
      wp_pull_exists
      apply SepWP.pure_elim; intro hbs72
      rcases kp72_words_sp168_placed s0.sp x.out hbs72 with
        ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hsp72, hout72⟩
      apply SepWP.focus_rw hsp72
      apply SepWP.focus_rw (memRegion_72_eq_cells9_placed x.out)
      wp_pull_exists
      wp_steps
      apply SepWP.focus_rw hout72.symm
      apply SepWP.focus_weaken (kp72_words_fold_memRegion_placed s0.sp w0 w1 w2 w3 w4 w5 w6 w7 w8)
      refine focus_kpPostAnsPlaced A x.out
        ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files)
        ansOk B _ s0 (hB x.out) hbs72 (by sep_focus) ?_ ?_
      · exact ⟨hans_ok.symm, by simp only [wp_norm, arm64_norm, *]⟩
      wp_done
    · have hc0_beq : (bCap == 0#64) = false := beq_false_of_ne hc0
      apply sepWPp_of_sepWP_lscro hcrl_sf_1 (mid := lsρ lsRustDeallocSymCli)
      wp_steps
      apply SepWP.done (by wp_norm_goal; try bv_omega) (by wp_norm_lhs)
      intro hcrl_d0
      wp_call_lscro hDeallocCells hcrl_d0 (bPtr, bCap, bs, s0.sp - 176#64)
      case panic =>
        intro sf_p _ hm
        dsimp only at hm
        simpa only [sepConj_assoc] using
          close_panic_subgoal_placed s0 hm (by simp only [wp_norm, arm64_norm, *])
      have h_reg2 : sf_2.sp = s0.sp - 176#64 ∧
          sf_2.readReg64 (.gpr 19#5) = x.fut ∧
          sf_2.readReg64 (.gpr 20#5) = x.out ∧
          sf_2.readReg64 (.gpr 29#5) = s0.sp - 48#64 :=
        ⟨by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *],
         by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
      rcases h_reg2 with ⟨_, _, _, _⟩
      apply SepWPp.of_sepWP_ret
      apply SepWP.focus_weaken (tryFrom_to_idKeyPairOutAt_placed A (s0.sp - 168#64)
        (IdentityKeyPair.tryFrom bs))
      rcases PollCommon.reloc_idKeyPairOutAt A ansOk with ⟨B, hB⟩
      apply SepWP.focus_rw (hB (s0.sp - 168#64))
      wp_pull_exists
      apply SepWP.pure_elim; intro hbs72
      rcases kp72_words_sp168_placed s0.sp x.out hbs72 with
        ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hsp72, hout72⟩
      apply SepWP.focus_rw hsp72
      apply SepWP.focus_rw (memRegion_72_eq_cells9_placed x.out)
      wp_pull_exists
      wp_steps
      apply SepWP.focus_rw hout72.symm
      apply SepWP.focus_weaken (kp72_words_fold_memRegion_placed s0.sp w0 w1 w2 w3 w4 w5 w6 w7 w8)
      refine focus_kpPostAnsPlaced A x.out
        ((IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files)
        ansOk B _ s0 (hB x.out) hbs72 (by sep_focus) ?_ ?_
      · exact ⟨hans_ok.symm, by simp only [wp_norm, arm64_norm, *]⟩
      wp_done

/-! ## Outer Wrapper and CLI Instantiation -/

set_option maxRecDepth 2000000 in
theorem idKeyPairPoll_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hGet : subroutine_ok (lsProg_567 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok (lsProg_567 H) (lsmpl.base 84)
      (RecordCodecsBinary.identityKeyPairTryFromPlacedSpec A))
    (hstk : 0xb0 + kpCalleeStk getStk ≤ stk) :
    subroutine_ok (lsProg_567 H) (lsmpl.base 567)
      (idKeyPairPollSpecPlaced rd pathOk A stk) := by
  intro x R s0 hpc hrun hpre hsp hcl
  obtain ⟨hcrl0, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [idKeyPairPollSpecPlaced] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hpath, hpok, hlen⟩, hmem⟩
  dsimp only [idOwnFutBoxAtPlaced] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine Store.IdTrustPoll.Helpers.memRegion_bound_of_pointsTo64
      (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₈ 0#8) ∗ memRegion (x.fut + 9#64) 7 ∗
        dirAt A x.self x.own ∗ memRegion x.out 72 ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; ac_rfl
  let calleeStk := kpCalleeStk getStk
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 176 ≤ 2 ^ 64 := by omega
  rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp (subStk := calleeStk + 176)
        (by omega) hstk_hi,
      ProofLib.stackAt_split_cells s0.sp calleeStk 22 hframe_hi] at hmem
  have hro := PollCommon.rodata_idKpFileName_placed hcrl0.2 hmem
  let F_extra :=
    memRegion (x.fut + 9#64) 7 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 176))
  have hpre_in : s0.mem ⊨
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (cliIdKeyPairPollInnerPlacedSpec rd pathOk A calleeStk)).pre x s0 ∗ (F_extra ∗ R) := by
    refine satisfies_withLsCodeRoLoaded_pre hcrl0 ?_
    dsimp only [cliIdKeyPairPollInnerPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hpath, hpok, hlen⟩, ?_⟩
    dsimp only [F_extra]
    exact Satisfies.mono (by sep_focus) hro
  rcases idKeyPairPollInner_placed_ok hC hGet hDec hcal_hi x (F_extra ∗ R)
      s0 hpc hrun hpre_in hsp hcl with
    ⟨sf, hsteps, ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom, hq⟩⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, cliIdKeyPairPollInnerPlacedSpec,
      idKeyPairPollSpecPlaced, idOwnFutBoxAtPlaced, kpPostAnsPlaced] at hq ⊢
    simp_rw [PollCommon.idKeyPairOutAtPlaced_eq]
    have hq_ro : sf.mem ⊨ (lsρ PollCommon.idKpFileNameSym ↦ᵣ utf8 "identity-key-pair") ∗
        (((∃∗ ans : Except Unit IdentityKeyPair,
            ⌜ans = (IdGhost.mk x.own (.new [])).keyPair rd s0.fs.files ∧ sf.trace = s0.trace⌝ ∗
            idKeyPairOutAt A x.out ans) ∗
          ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₈ 1#8) ∗ memRegion (x.fut + 9#64) 7) ∗
          dirAt A x.self x.own ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 176)) ∗
            (stackAt (s0.sp - 176#64) calleeStk ∗ cells (s0.sp - 176#64) 22))) ∗ R) := by
      dsimp only [F_extra] at hq
      exact Satisfies.mono (by sep_focus) hq
    have hq_drop := Satisfies.of_sep_right hq_ro
    rw [Store.IdTrustPoll.Helpers.stackAt_sub_split s0.sp (subStk := calleeStk + 176)
          (by omega) hstk_hi,
        ProofLib.stackAt_split_cells s0.sp calleeStk 22 hframe_hi]
    exact hq_drop
  · refine ⟨sf, hsteps, Or.inr (Or.inl ⟨hpan, ?_⟩)⟩
    dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, cliIdKeyPairPollInnerPlacedSpec,
      idKeyPairPollSpecPlaced] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      cliIdKeyPairPollInnerPlacedSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
      cliIdKeyPairPollInnerPlacedSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-- CLI instantiation of `IdentityFiles::get_identity_key_pair::{closure#0}` (Block `567`)
transferred onto any caller block program `prog` (e.g. `initProgPlaced W`). -/
theorem idKeyPairPoll_cli_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {A : RustAlloc} {W : CliHooks} {H : LibsignalHooks} [IsLsBlockProg prog i H] (B : RunBudgets)
    (hh : RunHooksPlaced W A H)
    (hGet : subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A B.dirGetNeed))
    (hi : i < 619 := by decide)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok prog (lsmpl.base 567)
      (idKeyPairPollSpecPlaced cliIo.rd cliWrOk A (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hs : smallRootStack ≤ 65536 := by decide
  have he : extHookStack ≤ 65536 := by decide
  have hGet567 : subroutine_ok (lsProg_567 H) (lsmpl.base 589)
      (dirGetSpecPlaced cliIo.rd cliWrOk A B.dirGetNeed) := by
    have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := lsProg_567 H) hGet
    exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
          LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  have hDec84 := RecordCodecsBinary.Assembly.identityKeyPair_tryFrom_placed_ok_of_hooks hh.codec
  have hDec567 : subroutine_ok (lsProg_567 H) (lsmpl.base 84)
      (RecordCodecsBinary.identityKeyPairTryFromPlacedSpec A) := by
    have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := lsProg_567 H) hDec84
    exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
          LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  have h567 := idKeyPairPoll_placed_ok_of_deps (stk := stk - cliInitiateFrame)
    hh.alloc hGet567 hDec567 (by dsimp only [kpCalleeStk]; omega)
  have hrocl := ls_subroutine_ok_rocl_of_block (callerProg := prog) h567 hi
  exact subroutine_ok_mono hrocl (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl,
        LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.IdKeyPairPoll
