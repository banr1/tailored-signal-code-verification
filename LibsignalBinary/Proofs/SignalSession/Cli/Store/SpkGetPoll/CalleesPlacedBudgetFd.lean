/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Callee Wrappers and Epilogue for `get_signed_pre_key::{closure#0}`

`FdsGe3Closed`-threaded sret unpack/pack helpers, placed callee cell wrappers, outer bridge, and
shared epilogue (`+344 .. ret`) on Block `571` (`lsProg_571 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlacedBudgetFd

open Arm64 ProofLib
open AsmConstants (boxSliceLenOff decResultVecOff resultErrSpeOff spePayloadOff speSize vecSize)
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchetRepr
  (errResultAt errTag okTagVec speAt speWord strRefAt utf8 vecResultAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalTripleRatchet.Getters (dropSpeStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded NoFsEv TraceFsSound extract_withLsCodeRoLoaded
   withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (SignedPreKeyRecord)
open CryptoVerification.RecordCodecsBinary (DecodeGhost signedPreKeyResultAt)
open CryptoVerification.SpqrV1.Alloc
  (vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DecimalGhost DirGetGhost DirGhost DropSpeWordGhost PkAns PkNameOk PkPollGhost PkSizeOk
   ReadRule decimalText dirAt files_eq_at_callback getResultAt keyName pkAnsAt pkAnsOf pkBoxAt
   spkAnsAt subroutine_ok_withFsInv withFsInv withFsInv_entry withFsInv_post_elim
   withFsInv_pre_intro)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_571 blkPC_571 blkPl_571 lsProg_571)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers
  (DeallocBufGhost DecodeCellsGhost DecimalCellsGhost DirGetCellsGhost DropSpeCellsGhost
   cells_48_split cells_sub_5_152_eq cells_sub_5_248_eq cells_sub_5_296_eq
   cells_sub_5_336_eq cells_sub_5_376_eq cells_sub_6_200_eq cells_sub_6_48_eq cells_sub_6_96_eq
   decodeSpkDetached dirGetDetached memRegion_16_cells memRegion_24_cells memRegion_32_cells
   memRegion_40_cells memRegion_48_cells memRegion_88_cells memRegion_bound_of_pointsTo64
   sp200_16 sp200_24 sp200_32 sp200_40 sp200_48 sp200_56 sp200_64 sp200_72 sp200_8 sp200_80
   sp248_16 sp248_8 speAt_unpack speDetached spkPollSlack spkSavedAt spkScratch15
   spkStructDetached spkStruct_unpack stackAt_spkPoll_frame stackAt_sub_split trace_ans_congr
   vecU8BufRest vecU8Buf_eq_bytes_sep_rest words11At words6At)
open CryptoVerification.SignalSession.Cli.Store.SpkGetPoll.Helpers.CliSpkPollNorm
  (bv_sub_sub_lit extractLsb_append_hi extractLsb_append_lo readReg32_setMem_setPC_pre
   readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre
   readReg_setPC_pre readVReg128_setMem_pre readVReg128_setMem_setPC_pre readVReg128_setPC_pre
   readVReg128_setPState_pre readVReg128_writeReg64_pre sp_setMem_setPC_pre sp_setPC_pre)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk
   rustDeallocEvents)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkLoopEnv decodeSignedPreKeyPlacedSpec decodeSignedPreKeyRawSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (dealloc_keepsFs_lscro_of_fs subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced decimalSpecPlaced dirGetSpecPlaced dropSpeWordSpecPlaced
   pkGetPollSpecOfPlaced spkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (CliSpkGetPollEnv deallocBufCellsSpec decimalCellsSpec decodeSpkCellsSpec dirGetCellsSpec
   dropSpeWordCellsSpec spkGetPollInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudgetFd
  (deallocBufCellsSpec_fd decimalCellsSpec_fd decodeSpkCellsSpec_fd dirGetCellsSpec_fd
   dropSpeWordCellsSpec_fd spkGetPollInnerSpec_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudget
  (spkEpiPre)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.SymPostBudgetFd
  (spkPostQ_fd)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi bv_sub_sub_lit
attribute [local arm64_norm, local wp_norm] words6At words11At

/-! ## 1. Private Sret Unpack & Epilogue Pack Helpers -/

private theorem getResultAt_unpack_p (A : RustAlloc) (ret : BitVec 64)
    (gr : Except Unit (List (BitVec 8))) :
    getResultAt A ret gr ⊢
      ∃∗ g0 : BitVec 64, ∃∗ g1 : BitVec 64, ∃∗ g2 : BitVec 64,
      ∃∗ g3 : BitVec 64, ∃∗ g4 : BitVec 64, ∃∗ g5 : BitVec 64,
        words6At ret g0 g1 g2 g3 g4 g5 ∗ dirGetDetached A gr g0 g1 g2 g3 g4 g5 := by
  cases gr with
  | error u =>
    cases u
    dsimp only [getResultAt, dirGetDetached]
    refine Entails.trans (speAt_unpack A (utf8 "read") ret .invalidState) ?_
    refine Entails.sepExists_elim fun g0 => Entails.sepExists_elim fun g1 =>
      Entails.sepExists_elim fun g2 => Entails.sepExists_elim fun g3 =>
      Entails.sepExists_elim fun g4 => Entails.sepExists_elim fun g5 => ?_
    refine Entails.sepExists_right g0 (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right g3
      (Entails.sepExists_right g4 (Entails.sepExists_right g5 ?_)))))
    dsimp only [speDetached]
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    have hpull :
        (words6At ret g0 g1 g2 g3 g4 g5 ∗
          ⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read")) =
        (⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          words6At ret g0 g1 g2 g3 g4 g5 ∗
          vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read")) := by sep_ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hg0, hg3, hg5⟩ => ?_
    have hgoal :
        words6At ret g0 g1 g2 g3 g4 g5 ∗
          vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read") ⊢
        ⌜g0 = speWord 1⌝ ∗
          ⌜g0 = speWord 1 ∧ g3 = BitVec.ofNat 64 bs.length ∧
            g5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗
          words6At ret g0 g1 g2 g3 g4 g5 ∗
          vecU8Buf A g1 g2 bs ∗ (g4 ↦ᵣ utf8 "read") :=
      Entails.pure_right hg0 (Entails.pure_right ⟨hg0, hg3, hg5⟩ (Entails.refl _))
    exact Entails.trans hgoal (Entails.of_eq (by sep_ac_rfl))
  | ok bs =>
    dsimp only [getResultAt, vecResultAt, dirGetDetached, words6At]
    have h8 : asm64% decResultVecOff = 8#64 := rfl
    have h32 : asm64% (decResultVecOff + vecSize) = 32#64 := rfl
    have hs : asm% (speSize - (decResultVecOff + vecSize)) = 16 := rfl
    rw [h8, h32, hs, memRegion_16_cells (ret + 32#64)]
    dsimp only [vecU8]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun g5 => Entails.sepExists_elim fun g4 =>
      Entails.sepExists_elim fun g1 => Entails.sepExists_elim fun g2 => ?_
    rw [vecU8At_eq_header_sep_buf]
    dsimp only [vecHeader]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.sepExists_right okTagVec (Entails.sepExists_right g1
      (Entails.sepExists_right g2 (Entails.sepExists_right (BitVec.ofNat 64 bs.length)
      (Entails.sepExists_right g4 (Entails.sepExists_right g5 ?_)))))
    rw [show (okTagVec = okTagVec ∧ BitVec.ofNat 64 bs.length = BitVec.ofNat 64 bs.length) = True from
      eq_true ⟨rfl, rfl⟩, pure_true, emp_sepConj]
    exact Entails.of_eq (by sep_ac_rfl)

private theorem signedPreKeyResultAt_unpack_p (A : RustAlloc) (ret : BitVec 64)
    (res : Except SignalProtocolError SignedPreKeyRecord) :
    signedPreKeyResultAt A ret res ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
      ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64,
        words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
        decodeSpkDetached A res w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 := by
  cases res with
  | error e =>
    dsimp only [signedPreKeyResultAt, errResultAt, decodeSpkDetached]
    have htag : errTag = 0xFFFFFFFFFFFFFFFF#64 := rfl
    have hoff8 : asm64% resultErrSpeOff = 8#64 := rfl
    have hoff56 : asm64% (resultErrSpeOff + speSize) = 56#64 := rfl
    have hsz : 88 - asm% (resultErrSpeOff + speSize) = 32 := rfl
    rw [htag, hoff8, hoff56, hsz, memRegion_32_cells (ret + 56#64)]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_left (speAt_unpack A [] (ret + 8#64) e))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w10 => Entails.sepExists_elim fun w9 =>
      Entails.sepExists_elim fun w8 => Entails.sepExists_elim fun w7 =>
      Entails.sepExists_elim fun u0 => Entails.sepExists_elim fun u1 =>
      Entails.sepExists_elim fun u2 => Entails.sepExists_elim fun u3 =>
      Entails.sepExists_elim fun u4 => Entails.sepExists_elim fun u5 => ?_
    refine Entails.sepExists_right 0xFFFFFFFFFFFFFFFF#64 (Entails.sepExists_right u0
      (Entails.sepExists_right u1 (Entails.sepExists_right u2
      (Entails.sepExists_right u3 (Entails.sepExists_right u4
      (Entails.sepExists_right u5 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.sepExists_right w9
      (Entails.sepExists_right w10 ?_))))))))))
    dsimp only [words6At, words11At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [pure_true, emp_sepConj]
    exact Entails.of_eq (by sep_ac_rfl)
  | ok r =>
    dsimp only [signedPreKeyResultAt, decodeSpkDetached]
    refine Entails.trans (spkStruct_unpack A ret r.signedPreKey) ?_
    refine Entails.sepExists_elim fun w0 => Entails.sepExists_elim fun w1 =>
      Entails.sepExists_elim fun w2 => Entails.sepExists_elim fun w3 =>
      Entails.sepExists_elim fun w4 => Entails.sepExists_elim fun w5 =>
      Entails.sepExists_elim fun w6 => Entails.sepExists_elim fun w7 =>
      Entails.sepExists_elim fun w8 => Entails.sepExists_elim fun w9 =>
      Entails.sepExists_elim fun w10 => ?_
    refine Entails.sepExists_right w0 (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right w5
      (Entails.sepExists_right w6 (Entails.sepExists_right w7
      (Entails.sepExists_right w8 (Entails.sepExists_right w9
      (Entails.sepExists_right w10 ?_))))))))))
    dsimp only [spkStructDetached]
    have hpull :
        (words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          ⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          vecU8Buf A w6 w7 r.signedPreKey.signature) =
        (⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          vecU8Buf A w6 w7 r.signedPreKey.signature) := by sep_ac_rfl
    rw [hpull]
    refine Entails.pure_left fun hprops => ?_
    have hgoal :
        words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          vecU8Buf A w6 w7 r.signedPreKey.signature ⊢
        ⌜w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          ⌜w2 = BitVec.ofNat 64 r.signedPreKey.publicKey.length ∧
            w5 = BitVec.ofNat 64 r.signedPreKey.privateKey.length ∧
            w8 = BitVec.ofNat 64 r.signedPreKey.signature.length ∧
            w9 = r.signedPreKey.timestamp ∧
            w10.extractLsb' 0 32 = r.signedPreKey.id ∧
            w0 ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗
          vecU8Buf A w0 w1 r.signedPreKey.publicKey ∗
          vecU8Buf A w3 w4 r.signedPreKey.privateKey ∗
          vecU8Buf A w6 w7 r.signedPreKey.signature :=
      Entails.pure_right hprops.2.2.2.2.2 (Entails.pure_right hprops (Entails.refl _))
    exact Entails.trans hgoal (Entails.of_eq (by sep_ac_rfl))

private theorem cells_pack_5_376_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 376#64) ↦₆₄ a0) ∗ ((sp - 368#64) ↦₆₄ a1) ∗ ((sp - 360#64) ↦₆₄ a2) ∗
      ((sp - 352#64) ↦₆₄ a3) ∗ ((sp - 344#64) ↦₆₄ a4) ⊢ cells (sp - 376#64) 5 := by
  rw [cells_sub_5_376_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_336_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 336#64) ↦₆₄ a0) ∗ ((sp - 328#64) ↦₆₄ a1) ∗ ((sp - 320#64) ↦₆₄ a2) ∗
      ((sp - 312#64) ↦₆₄ a3) ∗ ((sp - 304#64) ↦₆₄ a4) ⊢ cells (sp - 336#64) 5 := by
  rw [cells_sub_5_336_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_296_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 296#64) ↦₆₄ a0) ∗ ((sp - 288#64) ↦₆₄ a1) ∗ ((sp - 280#64) ↦₆₄ a2) ∗
      ((sp - 272#64) ↦₆₄ a3) ∗ ((sp - 264#64) ↦₆₄ a4) ⊢ cells (sp - 296#64) 5 := by
  rw [cells_sub_5_296_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_5_248_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 248#64) ↦₆₄ a0) ∗ ((sp - 240#64) ↦₆₄ a1) ∗ ((sp - 232#64) ↦₆₄ a2) ∗
      ((sp - 224#64) ↦₆₄ a3) ∗ ((sp - 216#64) ↦₆₄ a4) ⊢ cells (sp - 248#64) 5 := by
  rw [cells_sub_5_248_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_6_200_p (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 200#64) ↦₆₄ a0) ∗ ((sp - 192#64) ↦₆₄ a1) ∗ ((sp - 184#64) ↦₆₄ a2) ∗
      ((sp - 176#64) ↦₆₄ a3) ∗ ((sp - 168#64) ↦₆₄ a4) ∗ ((sp - 160#64) ↦₆₄ a5) ⊢
      cells (sp - 200#64) 6 := by
  rw [cells_sub_6_200_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem cells_pack_5_152_p (sp a0 a1 a2 a3 a4 : BitVec 64) :
    ((sp - 152#64) ↦₆₄ a0) ∗ ((sp - 144#64) ↦₆₄ a1) ∗ ((sp - 136#64) ↦₆₄ a2) ∗
      ((sp - 128#64) ↦₆₄ a3) ∗ ((sp - 120#64) ↦₆₄ a4) ⊢ cells (sp - 152#64) 5 := by
  rw [cells_sub_5_152_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4 (Entails.refl _)))))

private theorem cells_pack_6_96_p (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 96#64) ↦₆₄ a0) ∗ ((sp - 88#64) ↦₆₄ a1) ∗ ((sp - 80#64) ↦₆₄ a2) ∗
      ((sp - 72#64) ↦₆₄ a3) ∗ ((sp - 64#64) ↦₆₄ a4) ∗ ((sp - 56#64) ↦₆₄ a5) ⊢
      cells (sp - 96#64) 6 := by
  rw [cells_sub_6_96_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem cells_pack_6_48_p (sp a0 a1 a2 a3 a4 a5 : BitVec 64) :
    ((sp - 48#64) ↦₆₄ a0) ∗ ((sp - 40#64) ↦₆₄ a1) ∗ ((sp - 32#64) ↦₆₄ a2) ∗
      ((sp - 24#64) ↦₆₄ a3) ∗ ((sp - 16#64) ↦₆₄ a4) ∗ ((sp - 8#64) ↦₆₄ a5) ⊢
      cells (sp - 48#64) 6 := by
  rw [cells_sub_6_48_eq]
  exact Entails.sepExists_right a0 (Entails.sepExists_right a1 (Entails.sepExists_right a2
    (Entails.sepExists_right a3 (Entails.sepExists_right a4
      (Entails.sepExists_right a5 (Entails.refl _))))))

private theorem frame48_pack_groups_p (sp : BitVec 64) :
    spkPollSlack sp ∗
      (cells (sp - 376#64) 5 ∗ cells (sp - 336#64) 5 ∗ cells (sp - 296#64) 5) ∗
      cells (sp - 248#64) 5 ∗
      cells (sp - 200#64) 6 ∗ cells (sp - 152#64) 5 ∗
      cells (sp - 96#64) 6 ∗ cells (sp - 48#64) 6 ⊢
      cells (sp - 384#64) 48 := by
  rw [cells_48_split sp]
  dsimp only [spkScratch15]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem spkEpiPost_pack_fd_p {M : AllocCostModel} (rd : ReadRule)
    (pathOk : List (BitVec 8) → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) (x : PkPollGhost) (st : M.σ) (s0 sf : State)
    (evs : List AllocEvent) (ans : PkAns SignedPreKeyRecord) (D : SepProp)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : BitVec 64)
    (a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 : BitVec 64)
    (hfds_sf : FdsGe3Closed sf.fs)
    (hpack : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢ spkAnsAt A.repAlloc x.out ans)
    (hans : ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace)
    (hevs : CliSpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x evs) :
    ((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
      ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
      ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
      ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
      dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st) sf ∗
      stackAt (s0.sp - 384#64) calleeStk ∗
      (spkPollSlack s0.sp ∗
        ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
          ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
         (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
          ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
         (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
          ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
        (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
          ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
        (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
          ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
        (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
          ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ⊢
      (spkGetPollInnerSpec_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk).post
        (x, st) s0 sf := by
  dsimp only [spkGetPollInnerSpec_fd, withFdsGe3Closed]
  refine Entails.pure_right hfds_sf ?_
  have hans' : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢
      ∃∗ a : PkAns SignedPreKeyRecord,
        ⌜a = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
            sf.trace = s0.trace ∧
            CliSpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x evs⌝ ∗
        spkAnsAt A.repAlloc x.out a :=
    Entails.trans hpack
      (Entails.sepExists_right ans (Entails.pure_right ⟨hans.1, hans.2, hevs⟩ (Entails.refl _)))
  dsimp only [words11At] at hans'
  have hsaved :
      (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
        ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ⊢
      cells (s0.sp - 96#64) 6 ∗ cells (s0.sp - 48#64) 6 := by
    have hsplit :
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
        ((((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25)) ∗
         (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by
      sep_ac_rfl
    rw [hsplit]
    exact sepConj_mono
      (cells_pack_6_96_p s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x28)
        (s0.readReg64 .x27) (s0.readReg64 .x26) (s0.readReg64 .x25))
      (cells_pack_6_48_p s0.sp (s0.readReg64 .x24) (s0.readReg64 .x23)
        (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
  have hcells := Entails.trans
    (sepConj_mono_right
      (sepConj_mono
        (sepConj_mono (cells_pack_5_376_p s0.sp a0 o7 o8 o9 o10)
          (sepConj_mono (cells_pack_5_336_p s0.sp o5 o6 b2 b3 b4)
            (cells_pack_5_296_p s0.sp c0 c1 c2 c3 c4)))
        (sepConj_mono (cells_pack_5_248_p s0.sp d0 d1 d2 d3 d4)
          (sepConj_mono (cells_pack_6_200_p s0.sp e0 e1 e2 e3 e4 e5)
            (sepConj_mono (cells_pack_5_152_p s0.sp f0 f1 f2 f3 f4) hsaved)))))
    (frame48_pack_groups_p s0.sp)
  dsimp only [spkGetPollInnerSpec]
  refine Entails.sepExists_right evs ?_
  have hassoc :
      (((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
        ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
        ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 384#64) calleeStk ∗
        (spkPollSlack s0.sp ∗
          ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
            ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
           (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
            ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
           (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
            ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
          (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
            ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
          (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
            ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
          (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
            ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) =
      ((((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗ ((x.out + 16#64) ↦₆₄ o2) ∗
        ((x.out + 24#64) ↦₆₄ o3) ∗ ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6) ∗ ((x.out + 56#64) ↦₆₄ o7) ∗ ((x.out + 64#64) ↦₆₄ o8) ∗
        ((x.out + 72#64) ↦₆₄ o9) ∗ ((x.out + 80#64) ↦₆₄ o10)) ∗ D) ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st) sf ∗
        stackAt (s0.sp - 384#64) calleeStk ∗
        (spkPollSlack s0.sp ∗
          ((((s0.sp - 376#64) ↦₆₄ a0) ∗ ((s0.sp - 368#64) ↦₆₄ o7) ∗ ((s0.sp - 360#64) ↦₆₄ o8) ∗
            ((s0.sp - 352#64) ↦₆₄ o9) ∗ ((s0.sp - 344#64) ↦₆₄ o10)) ∗
           (((s0.sp - 336#64) ↦₆₄ o5) ∗ ((s0.sp - 328#64) ↦₆₄ o6) ∗ ((s0.sp - 320#64) ↦₆₄ b2) ∗
            ((s0.sp - 312#64) ↦₆₄ b3) ∗ ((s0.sp - 304#64) ↦₆₄ b4)) ∗
           (((s0.sp - 296#64) ↦₆₄ c0) ∗ ((s0.sp - 288#64) ↦₆₄ c1) ∗ ((s0.sp - 280#64) ↦₆₄ c2) ∗
            ((s0.sp - 272#64) ↦₆₄ c3) ∗ ((s0.sp - 264#64) ↦₆₄ c4))) ∗
          (((s0.sp - 248#64) ↦₆₄ d0) ∗ ((s0.sp - 240#64) ↦₆₄ d1) ∗ ((s0.sp - 232#64) ↦₆₄ d2) ∗
            ((s0.sp - 224#64) ↦₆₄ d3) ∗ ((s0.sp - 216#64) ↦₆₄ d4)) ∗
          (((s0.sp - 200#64) ↦₆₄ e0) ∗ ((s0.sp - 192#64) ↦₆₄ e1) ∗ ((s0.sp - 184#64) ↦₆₄ e2) ∗
            ((s0.sp - 176#64) ↦₆₄ e3) ∗ ((s0.sp - 168#64) ↦₆₄ e4) ∗ ((s0.sp - 160#64) ↦₆₄ e5)) ∗
          (((s0.sp - 152#64) ↦₆₄ f0) ∗ ((s0.sp - 144#64) ↦₆₄ f1) ∗ ((s0.sp - 136#64) ↦₆₄ f2) ∗
            ((s0.sp - 128#64) ↦₆₄ f3) ∗ ((s0.sp - 120#64) ↦₆₄ f4)) ∗
          (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
            ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
            ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) := by
    sep_ac_rfl
  rw [hassoc]
  exact sepConj_mono hans'
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hcells))))))

/-! ## 2. Placed Callee Cell Wrappers & Outer Bridge (`*_fd`) -/

theorem decimal_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop} {decStk calleeStk : Nat}
    (hDecimal : subroutine_ok prog (lsmpl.base 597)
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)))
    (hFs : TraceFsSound prog)
    (hle : decStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 597)
      (withLsCodeRoLoaded lsmpl (decimalCellsSpec_fd A lim DecEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨id, ret, o0, o1, o2, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [decimalCellsSpec_fd, withFdsGe3Closed] at hpre
  simp only [decimalCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfds0, ⟨hx0, hx1, hfsp, hfit⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - decStk)
  let callG : DecimalGhost × M.σ := (⟨id, ret⟩, st)
  have hpre_base : s0.mem ⊨ (decimalSpecPlaced A lim DecEnv decStk).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold decimalSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_24_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hfit⟩, ?_⟩
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  have hpre_fd : s0.mem ⊨
      (withFdsGe3Closed (decimalSpecPlaced A lim DecEnv decStk)).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfds0, hpre_base⟩
  have hpre_fs := withFsInv_pre_intro (withFsInv_entry s0) hpre_fd
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  refine hDecFs.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre_fs hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    obtain ⟨hfs_sf, hq⟩ := withFsInv_post_elim hq
    dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, decimalSpecPlaced,
      decimalCellsSpec_fd, decimalCellsSpec, callG, keyName] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfds_sf, hq⟩
    refine ⟨hfds_sf, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨htr, hevs⟩, hq⟩
    have hfiles : sf.fs.files = s0.fs.files :=
      files_eq_at_callback hfs_sf (evs := []) (by rw [htr, List.append_nil]) (by simp [NoFsEv])
    dsimp only [vecU8] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq
    rcases hq with ⟨nCap, nPtr, hq⟩
    refine ⟨evs, nCap, nPtr, ?_⟩
    rw [vecU8At_eq_header_sep_buf] at hq
    dsimp only [vecHeader] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hfiles, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim
  · dsimp only [withFsInv, withFdsGe3Closed, withLsCodeRoLoaded, decimalSpecPlaced] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact (not_satisfies_false_sepConj hq.2).elim

theorem dirGet_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk calleeStk : Nat} {F0 : FsFiles}
    (hGet : subroutine_ok prog (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hle : getStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 589)
      (withLsCodeRoLoaded lsmpl
        (dirGetCellsSpec_fd rd pathOk A lim (fun dir id => GetEnv F0 dir (keyName id)) F0 calleeStk)) := by
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨ret, self, dir, nCap, nPtr, id, o0, o1, o2, o3, o4, o5, fsp⟩, st⟩ R s0
      hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [dirGetCellsSpec_fd, withFdsGe3Closed] at hpre
  simp only [dirGetCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfds0, ⟨hx0, hx1, hx2, hx3, hfsp, hfiles, hnameOk, hfit⟩, hmem⟩
  subst hfsp
  rcases hnameOk with ⟨hnlen, hdlen, hpOk⟩
  have hx3_nat : (s0.readReg64 .x3).toNat = (keyName id).length := by
    rw [hx3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfit0 : FitsEnv M lim st (GetEnv s0.fs.files dir (keyName id)) := by
    rwa [hfiles]
  rw [stackAt_sub_split s0.sp hle hhi,
    vecU8Buf_eq_bytes_sep_rest A.repAlloc nCap nPtr (keyName id)] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - getStk)
  let nameRem := vecU8BufRest A.repAlloc nCap nPtr (keyName id)
  let callG : DirGetGhost × M.σ := (⟨ret, self, dir, nPtr, keyName id, false⟩, st)
  have hpre_base : s0.mem ⊨ (dirGetSpecPlaced rd pathOk A lim GetEnv getStk).pre callG s0 ∗
      (nameRem ∗ stkRem ∗ R) := by
    unfold dirGetSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG, bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte, memRegion_48_cells, sepExists_sepConj_left,
      sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨o5, o4, o3, o2, o1, o0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3_nat, hnlen, hdlen, hpOk, hfit0⟩, ?_⟩
    dsimp only [stkRem, nameRem]
    dsimp only [bytesAt] at hmem
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem
    convert hmem using 1; sep_ac_rfl
  have hpre0 : s0.mem ⊨
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)).pre callG s0 ∗
      (nameRem ∗ stkRem ∗ R) := by
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfds0, hpre_base⟩
  refine hGet.mono_outcome callG (nameRem ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, dirGetSpecPlaced,
      dirGetCellsSpec_fd, dirGetCellsSpec, callG, bytesAt] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfds_sf, hq⟩
    refine ⟨hfds_sf, ?_⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    rw [hfiles] at hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, gr, hq⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hdisj, hq⟩
    have hq' := Satisfies.mono (sepConj_mono_left (getResultAt_unpack_p A.repAlloc ret gr)) hq
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq'
    rcases hq' with ⟨g0, g1, g2, g3, g4, g5, hq'⟩
    refine ⟨evs, gr, g0, g1, g2, g3, g4, g5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hdisj, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi,
      vecU8Buf_eq_bytes_sep_rest A.repAlloc nCap nPtr (keyName id)]
    dsimp only [bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [stkRem, nameRem] at hq'
    convert hq' using 1; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, dirGetSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, dirGetSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, dirGetSpecPlaced] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem decodeSpk_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop} {calleeStk : Nat}
    (hDec : subroutine_ok prog (lsmpl.base 595)
      (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)))
    (hle : smallRootStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs) :
    subroutine_ok prog (lsmpl.base 595)
      (withLsCodeRoLoaded lsmpl (decodeSpkCellsSpec_fd A lim DecodeEnv calleeStk)) := by
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨ret, bCap, bPtr, bytes, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, fsp⟩, st⟩
      R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [decodeSpkCellsSpec_fd, withFdsGe3Closed] at hpre
  simp only [decodeSpkCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfds0, ⟨hx0, hx1, hx2, hfsp, hlen_pos, hlen_lt, hfit⟩, hmem⟩
  subst hfsp
  have hx2_nat : (s0.readReg64 .x2).toNat = bytes.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hfit_loop : FitsEnv M lim st (SpkLoopEnv (2 * bytes.length + 3) bytes.length) :=
    hfit.mono (hSub bytes)
  rw [stackAt_sub_split s0.sp hle hhi,
    vecU8Buf_eq_bytes_sep_rest A.repAlloc bCap bPtr bytes] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - smallRootStack)
  let bytesRem := vecU8BufRest A.repAlloc bCap bPtr bytes
  let callG : DecodeGhost × M.σ := (⟨bPtr, bytes, ret⟩, st)
  have hpre_base : s0.mem ⊨ (decodeSignedPreKeyPlacedSpec A lim).pre callG s0 ∗
      (bytesRem ∗ stkRem ∗ R) := by
    unfold decodeSignedPreKeyPlacedSpec decodeSignedPreKeyRawSpec
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_88_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_nat, hlen_pos, hlen_lt, hfit_loop⟩, ?_⟩
    dsimp only [stkRem, bytesRem]
    dsimp only [bytesAt] at hmem
    simp only [Bool.false_eq_true, ↓reduceIte] at hmem
    convert hmem using 1; sep_ac_rfl
  have hpre0 : s0.mem ⊨
      (withFdsGe3Closed (decodeSignedPreKeyPlacedSpec A lim)).pre callG s0 ∗
      (bytesRem ∗ stkRem ∗ R) := by
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfds0, hpre_base⟩
  refine hDec.mono_outcome callG (bytesRem ∗ stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed, withLsCodeRoLoaded,
      CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyPlacedSpec, decodeSignedPreKeyRawSpec,
      decodeSpkCellsSpec_fd, decodeSpkCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfds_sf, hq⟩
    refine ⟨hfds_sf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    simp only [sepConj_assoc] at hq
    rw [satisfies_pure_sepConj] at hq
    rcases hq with ⟨hevs_k, hq⟩
    have hevs : DecodeEnv bytes evs := hSup bytes evs hevs_k
    have hq_sr : sf.mem ⊨
        signedPreKeyResultAt A.repAlloc ret (SignedPreKeyRecord.deserialize bytes) ∗
          (A.pool lim (M.stepEvents evs st) sf ∗ (bPtr ↦ₛ bytes) ∗
            stackAt s0.sp smallRootStack ∗ (bytesRem ∗ stkRem ∗ R)) := by
      convert hq using 1; sep_ac_rfl
    have hq' := Satisfies.mono
      (sepConj_mono_left
        (signedPreKeyResultAt_unpack_p A.repAlloc ret (SignedPreKeyRecord.deserialize bytes)))
      hq_sr
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq'
    rcases hq' with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, hq'⟩
    refine ⟨evs, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨htr, hevs⟩, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi,
      vecU8Buf_eq_bytes_sep_rest A.repAlloc bCap bPtr bytes]
    dsimp only [bytesAt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    dsimp only [stkRem, bytesRem] at hq'
    convert hq' using 1; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyPlacedSpec, decodeSignedPreKeyRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyPlacedSpec, decodeSignedPreKeyRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      decodeSignedPreKeyPlacedSpec, decodeSignedPreKeyRawSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem deallocBuf_cells_keepsFs_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (Spec.keepsFs (deallocBufCellsSpec A lim calleeStk))) := by
  have hDealloc := dealloc_keepsFs_lscro_of_fs (callerProg := prog) hC hi
  refine subroutine_ok.of_codeLoaded fun ⟨⟨cap, ptr, bytes, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [Spec.keepsFs] at hpre
  simp only [deallocBufCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hfsp, hcap, hlr_ls⟩, hmem⟩
  subst hfsp
  unfold vecU8Buf at hmem
  have hcap0 : ¬(cap = 0) := hcap
  simp only [hcap0, ite_false] at hmem
  rw [sepConj_assoc, satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨⟨hbs_le, hcap_lt, _⟩, hmem⟩
  have hcap_pos : 0 < cap.toNat := by
    by_cases hz : cap.toNat = 0
    · exact (hcap (BitVec.eq_of_toNat_eq hz)).elim
    · omega
  have hlay : RustLayoutOk cap.toNat 1 := ⟨⟨hcap_pos, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hreg : (ptr ↦ₛ bytes) ∗
      memRegion (ptr + BitVec.ofNat 64 bytes.length) (cap.toNat - bytes.length) ⊢
      memRegion ptr cap.toNat := by
    have heq : cap.toNat = bytes.length + (cap.toNat - bytes.length) := by omega
    conv_rhs => rw [heq]
    rw [memRegion_split ptr bytes.length (cap.toNat - bytes.length) (by omega)]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bytes)
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - extHookStack)
  have hmem_reg : s0.mem ⊨ memRegion ptr cap.toNat ∗
      (A.pool lim st s0 ∗ A.live ptr cap.toNat 1 ∗ stackAt s0.sp extHookStack ∗ stkRem ∗ R) := by
    refine Satisfies.mono (sepConj_mono_left hreg) ?_
    dsimp only [stkRem]
    convert hmem using 1; sep_ac_rfl
  have hx1_nat : (s0.readReg64 .x1).toNat = cap.toNat := congrArg BitVec.toNat hx1
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; rfl
  let callG : BitVec 64 × Nat × Nat × M.σ := (ptr, cap.toNat, 1, st)
  have hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (Spec.keepsFs (rustDeallocExternSpecWithStack M A lim extHookStack))).pre
        callG s0 ∗ (stkRem ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack, callG]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1_nat, hx2_nat, hlay, hlr_ls⟩, ?_⟩
    convert hmem_reg using 1; sep_ac_rfl
  refine hDealloc.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack,
      deallocBufCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfs_eq, hq⟩
    refine ⟨hfs_eq, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨htr, hq⟩
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, Spec.keepsFs, rustDeallocExternSpecWithStack,
      LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliDeallocBudgetExternSpecWithStack,
      LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem deallocBuf_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} [IsLsBlockProg prog i H] {calleeStk : Nat}
    (hC : AllocContractsFsPlaced A lim H)
    (hle : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (hi : i < 619 := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec_fd A lim calleeStk)) :=
  subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs
    (deallocBuf_cells_keepsFs_placed_ok hC hle hhi hi)

theorem dropSpeWord_cells_placed_ok_fd [LibsignalPlacement] {prog : Program} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {calleeStk : Nat}
    (hDrop : subroutine_ok prog (lsmpl.base 553)
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)))
    (hle : dropSpeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 553)
      (withLsCodeRoLoaded lsmpl (dropSpeWordCellsSpec_fd A lim calleeStk)) := by
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨a, d1, d2, d3, d4, d5, fsp⟩, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [dropSpeWordCellsSpec_fd, withFdsGe3Closed] at hpre
  simp only [dropSpeWordCellsSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfds0, ⟨hx0, hfsp⟩, hmem⟩
  subst hfsp
  rw [stackAt_sub_split s0.sp hle hhi] at hmem
  let stkRem := memRegion (s0.sp - BitVec.ofNat 64 calleeStk) (calleeStk - dropSpeStackX)
  let callG : DropSpeWordGhost × M.σ := (⟨a, 14⟩, st)
  have hpre_base : s0.mem ⊨ (dropSpeWordSpecPlaced A lim).pre callG s0 ∗ (stkRem ∗ R) := by
    unfold dropSpeWordSpecPlaced
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [callG]
    simp only [memRegion_40_cells, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists]
    refine ⟨d5, d4, d3, d2, d1, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, Or.inr trivial⟩, ?_⟩
    dsimp only [words6At, stkRem] at hmem ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    convert hmem using 1; sep_ac_rfl
  have hpre0 : s0.mem ⊨
      (withFdsGe3Closed (dropSpeWordSpecPlaced A lim)).pre callG s0 ∗ (stkRem ∗ R) := by
    dsimp only [withFdsGe3Closed]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hfds0, hpre_base⟩
  refine hDrop.mono_outcome callG (stkRem ∗ R) s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, dropSpeWordSpecPlaced,
      dropSpeWordCellsSpec_fd, dropSpeWordCellsSpec, callG] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfds_sf, hq⟩
    refine ⟨hfds_sf, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨htr, hq⟩
    simp only [memRegion_48_cells, sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨c5, c4, c3, c2, c1, c0, hq⟩
    refine ⟨c0, c1, c2, c3, c4, c5, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    rw [stackAt_sub_split s0.sp hle hhi]
    dsimp only [stkRem] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withFdsGe3Closed, dropSpeWordSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, dropSpeWordSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withFdsGe3Closed, dropSpeWordSpecPlaced, withLsCodeRoLoaded] at hq
    exact (not_satisfies_false_sepConj hq).elim

theorem spkGetPoll_placed_of_inner_fd [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (withLsCodeRoLoaded lsmpl
          (spkGetPollInnerSpec_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk)))
    (hstk : 0x180 + calleeStk ≤ stk) :
    subroutine_ok prog entry
      (withFdsGe3Closed
        (spkGetPollSpecPlaced rd pathOk A lim
          (CliSpkGetPollEnv DecEnv GetEnv DecodeEnv rd) stk)) := by
  refine subroutine_ok.of_codeLoaded fun ⟨x, st⟩ R s0 hpc hrun hpre hsp _ => ?_
  dsimp only [withFdsGe3Closed] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hfds0, hpre⟩
  unfold spkGetPollSpecPlaced pkGetPollSpecOfPlaced at hpre
  rcases extract_withLsCodeRoLoaded hpre with ⟨hcrl, hpre⟩
  dsimp only [] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hname, hsize, hfit⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 0xd#64) 3 ∗
        dirAt A.repAlloc x.self x.dir ∗ memRegion x.out 88 ∗ A.pool lim st s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 384 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 384) (by omega) hstk_hi,
    stackAt_spkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 0xd#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 384))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (spkGetPollInnerSpec_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk)).pre (x, st) s0 ∗
      (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [spkGetPollInnerSpec_fd, withFdsGe3Closed, spkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hfds0, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hname, hsize, hfit⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; sep_ac_rfl
  refine (hInner hcal_hi).mono_outcome (x, st) (F_extra ∗ R) s0 hpc hrun hpre_in hsp
    fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hq⟩ | ⟨_code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withFdsGe3Closed, withLsCodeRoLoaded, spkGetPollInnerSpec_fd, spkGetPollInnerSpec,
      spkGetPollSpecPlaced, pkGetPollSpecOfPlaced, spkAnsAt, pkBoxAt] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfds_sf, hq⟩
    refine ⟨hfds_sf, ?_⟩
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, ans, hq⟩
    refine ⟨evs, ans, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 384) (by omega) hstk_hi,
      stackAt_spkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; sep_ac_rfl
  · dsimp only [withLsCodeRoLoaded, spkGetPollInnerSpec_fd, withFdsGe3Closed, spkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, spkGetPollInnerSpec_fd, withFdsGe3Closed, spkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · dsimp only [withLsCodeRoLoaded, spkGetPollInnerSpec_fd, withFdsGe3Closed, spkGetPollInnerSpec] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 3. Shared Epilogue (`+344` .. `ret`) on `lsProg_571 H` (`*_fd`) -/

theorem epilogue_placed_ok_fd [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {st : M.σ} {R : SepProp}
    {s0 s : State} {evs : List AllocEvent} {ans : PkAns SignedPreKeyRecord} {D P : SepProp}
    {o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 : BitVec 64}
    {u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64}
    {a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 : BitVec 64}
    (hfds : FdsGe3Closed s.fs)
    (hpc : s.pc = (blkPl_571).base + bv% 344)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 384#64)
    (hvr : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = o0)
    (hx25 : s.readReg64 .x25 = o1)
    (hx23 : s.readReg64 .x23 = o2)
    (hx24 : s.readReg64 .x24 = o3)
    (hx21 : s.readReg64 .x21 = o4)
    (hpack : words11At x.out o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗ D ⊢ spkAnsAt A.repAlloc x.out ans)
    (hans : ans = pkAnsOf SignedPreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          s.trace = s0.trace)
    (hevs : CliSpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x evs)
    (hP : P ⊢ spkEpiPre A lim calleeStk x (M.stepEvents evs st) s0 s D
      u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10
      a0 o7 o8 o9 o10 o5 o6 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4
      e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4 := by
        try simp only [spkEpiPre, words11At, words6At, spkSavedAt,
          sp248_8, sp248_16, sp200_8, sp200_16, sp200_24, sp200_32, sp200_40,
          sp200_48, sp200_56, sp200_64, sp200_72, sp200_80]
        sep_frame) :
    SepWP (lsProg_571 H) (s0.readReg64 .x30) s P
      (spkPostQ_fd rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x st R s0) := by
  refine SepWP.weaken_pre hP ?_
  dsimp only [spkEpiPre, spkSavedAt, words11At, spkPostQ_fd]
  clear hP
  wp_steps_sync_pool (s0.readReg64 .x30)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, ?_, ?_⟩
  · refine Entails.trans (Entails.of_eq (by sep_ac_rfl))
      (spkEpiPost_pack_fd_p rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x st s0 _ evs ans D
        o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10
        a0 b2 b3 b4 c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 e0 e1 e2 e3 e4 e5 f0 f1 f2 f3 f4
        (by simpa only [wp_norm, arm64_norm] using hfds)
        hpack (trace_ans_congr (s := s) (by simp only [wp_norm, arm64_norm]) hans) hevs)
  · simp only [wp_norm, arm64_norm]
  · rw [CalleeSavedPreserved.iff_regs]
    simp only [wp_norm, arm64_norm, hvr]

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesPlacedBudgetFd
