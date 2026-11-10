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
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LastResortPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Relocatable Proofs for `get_kyber_pre_key::{closure#0}`

Proves `kpkGetPollInner_placed_ok`, `kpkGetPoll_placed_ok`, and `kpkGetPoll_placed_fs_ok` on
Block `576` (`lsProg_576 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack smallRootStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles FsInv LibsignalCodeRoLoaded TraceFsSound extract_withLsCodeRoLoaded sepWPp_seq_lscro
   withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkPollGhost PkAns PkNameOk PkSizeOk ReadRule dirAt keyName kpkAnsAt kpkAnsOf pkAnsOf
   pkBoxAt withFsInv_entry)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_576 blkPC_576 blkPl_576 lsProg_576)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
  (KpkScratch add1_lt63_beq_zero add1_lt63_bne_zero bind_sepWP_state bind_sepWPp_state
   cmn_lt63_eq_false cmn_lt63_ne_true dec_off16 dec_off8 decodePostProp fsInv_of_eq
   kpkSavedRegs kpkScratchAt kpkSlack3 memRegion_bound_of_pointsTo64 ofNat_len_ne_zero
   satisfies_open_frame satisfies_open_words11 slot7At slotDecAt slotFp90At slotRetHeadAt
   slotRetTailAt slotSp40At slotSp70At sp_sub_432_spAligned stackAt_kpkPoll_frame
   stackAt_sub_split vecU8Buf_zero_entails_emp words11At words11At_retSlot words6At_retSlot)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers.CliKpkGetPollNorm
  (extractLsb_append_hi extractLsb_append_lo readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   readVReg128_setMem_pre readVReg128_setMem_setPC_pre readVReg128_setPC_pre
   readVReg128_setPState_pre readVReg128_writeReg64_pre sp_setMem_setPC_pre sp_setPC_pre
   zext32_trunc32)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustDeallocEvents)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkLoopEnv decodeKyberPreKeyPlacedSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced decimalSpecPlaced dirGetSpecPlaced kpkGetPollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
  (CliKpkGetPollEnv KpkPassEnv OptKpkDecodeEnv cliKpkGetPollInnerSpec deallocVecBufCellsSpec
   decimalFsCellsSpec decodeFsCellsSpec dirGetFsCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlacedBudget
  (deallocVecBuf_cells_placed_ok decimal_cells_placed_ok decode_cells_placed_ok
   dirGet_cells_placed_ok kpkGetPoll_placed_of_inner)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.EpiloguePlacedBudget
  (KpkExitPost kpk_call_total_lscro step_dec_err_ret_placed step_dec_ok_ret_placed
   step_dir_err_ret_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlacedBudgetAux
  (KpkCalleeDepsPlaced step_ot_empty_next_placed)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi zext32_trunc32
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_sub_496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.sp_add_neg496_eq_esp
  CryptoVerification.LibsignalTripleRatchet.Expand.esp_add_496_sub_496


/-! ## Full `kpkGetPollInner_placed_ok`, `kpkGetPoll_placed_ok`, and `kpkGetPoll_placed_fs_ok` (`+0`) -/

private theorem kpkGetPollInner_sepWPp_of_pre [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_576 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_576 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok (lsProg_576 H) (lsmpl.base 595)
      (decodeKyberPreKeyPlacedSpec A lim))
    (hle_dec : decStk ≤ calleeStk)
    (hle_get : getStk ≤ calleeStk)
    (hle_root : smallRootStack ≤ calleeStk)
    (hle_hook : extHookStack ≤ calleeStk)
    (hFs : TraceFsSound (lsProg_576 H))
    (hhi : calleeStk ≤ 2 ^ 64)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs)
    (x : KpkPollGhost) (st0 : M.σ) (Fr : SepProp) (s0 : State)
    (hpc0 : s0.pc = (blkPl_576).base)
    (hrun0 : s0.status = .Running)
    (hpre0 : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliKpkGetPollInnerSpec rd pathOk A lim DecEnv
          (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv calleeStk)).pre
        (x, st0) s0 ∗ Fr)
    (hal0 : s0.spAligned = true) :
    ∃ P : SepProp, (s0.mem ⊨ P ∗ Fr) ∧
      SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s0 P
        (KpkExitPost rd pathOk A lim DecEnv
          (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv calleeStk x st0 s0)
        (fun _ _ => False) := by
  obtain ⟨hcrl0, hpre0⟩ := extract_withLsCodeRoLoaded hpre0
  dsimp only [cliKpkGetPollInnerSpec] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hfs0, hx0, hx8, hn1, hn2, hs1, hs2, hfit0⟩, hmem0⟩
  have hmem_54 : s0.mem ⊨ cells (s0.sp - 432#64) 54 ∗
      (memRegion x.out 88 ∗
       (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
       dirAt A.repAlloc x.self x.kg.oneTime ∗
       dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
       A.pool lim st0 s0 ∗ stackAt (s0.sp - 432#64) calleeStk ∗ Fr) := by
    convert hmem0 using 1; sep_ac_rfl
  clear hmem0
  obtain ⟨sc, g96, g88, g80, g72, g64, g56, g48, g40, g32, g24, g16, g8, hmem1⟩ :=
    satisfies_open_frame hmem_54
  clear hmem_54
  let savedInit : SepProp :=
    ((s0.sp - 96#64) ↦₆₄ g96) ∗ ((s0.sp - 88#64) ↦₆₄ g88) ∗
    ((s0.sp - 80#64) ↦₆₄ g80) ∗ ((s0.sp - 72#64) ↦₆₄ g72) ∗
    ((s0.sp - 64#64) ↦₆₄ g64) ∗ ((s0.sp - 56#64) ↦₆₄ g56) ∗
    ((s0.sp - 48#64) ↦₆₄ g48) ∗ ((s0.sp - 40#64) ↦₆₄ g40) ∗
    ((s0.sp - 32#64) ↦₆₄ g32) ∗ ((s0.sp - 24#64) ↦₆₄ g24) ∗
    ((s0.sp - 16#64) ↦₆₄ g16) ∗ ((s0.sp - 8#64) ↦₆₄ g8)
  change s0.mem ⊨ (kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ savedInit) ∗ _ at hmem1
  have hmem_out : s0.mem ⊨ memRegion x.out 88 ∗
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
       dirAt A.repAlloc x.self x.kg.oneTime ∗
       dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
       A.pool lim st0 s0 ∗ stackAt (s0.sp - 432#64) calleeStk ∗
       kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ savedInit ∗ Fr) := by
    convert hmem1 using 1; sep_ac_rfl
  clear hmem1
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, hmem_ready⟩ :=
    satisfies_open_words11 hmem_out
  clear hmem_out
  have hwp : SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s0
      (words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim st0 s0 ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ savedInit)
      (KpkExitPost rd pathOk A lim DecEnv
        (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv calleeStk x st0 s0)
      (fun _ _ => False) := by
    have hDeps : KpkCalleeDepsPlaced A lim DecEnv GetEnv H rd pathOk decStk getStk :=
      ⟨hDecimal, hGet, hDec⟩
    have hDecCells := decimal_cells_placed_ok (F0 := s0.fs.files) (T0 := s0.trace)
      hDecimal hFs hle_dec hhi
    have hGetCells := dirGet_cells_placed_ok (F0 := s0.fs.files) (T0 := s0.trace)
      hGet hFs hle_get hhi
    have hDecodeCells := decode_cells_placed_ok (F0 := s0.fs.files) (T0 := s0.trace)
      (DecodeEnv := DecodeEnv) hDec hFs hle_root hhi hSub hSup
    clear hDecimal hGet hDec
    have hfit_pass1 : FitsEnv M lim st0
        (KpkPassEnv DecEnv (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
          rd s0.fs.files x.kg.oneTime x.id) := by
      unfold CliKpkGetPollEnv at hfit0
      split at hfit0
      · exact hfit0.seq_left
      · exact hfit0
    have hfit_dec : FitsEnv M lim st0 (DecEnv x.id) := by
      unfold KpkPassEnv at hfit_pass1
      exact hfit_pass1.seq_left
    let _ := hal0
    -- Prologue `+0 .. +64`: save regs, check state byte `0`, load fields, `bl decimal`
    apply sepWPp_seq_lscro (mid := lsmpl.base 597) hcrl0
    dsimp only [savedInit]
    wp_steps_sync_pool (lsmpl.base 597)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_dec
    have hsp_dec : s_dec.sp = s0.sp - 432#64 := by simp only [s_dec, arm64_norm]
    have hal_dec : s_dec.spAligned = true := sp_sub_432_spAligned hal0 hsp_dec
    have htr_dec : s_dec.trace = s0.trace := by simp only [s_dec, arm64_norm]
    have hfs_dec : FsInv s0.fs.files s0.trace s_dec :=
      fsInv_of_eq hfs0 (by simp only [s_dec, arm64_norm]) (by simp only [s_dec, arm64_norm])
    have hvregs_dec : calleeSavedVRegs s_dec = calleeSavedVRegs s0 := by
      simp only [s_dec, calleeSavedVRegs, arm64_norm]
    refine kpk_call_total_lscro
      ((x.id, s0.sp - 264#64, sc.dec0, sc.dec1, sc.dec2, s0.sp - 432#64), st0)
      hDecCells hcrl1
      (by simp only [s_dec, arm64_norm])
      (by simp only [s_dec, arm64_norm, *])
      hal_dec
      (ret_pc := (blkPl_576).base + 68#64)
      (by simp only [s_dec, arm64_norm])
      (F := words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        kpkSlack3 s0.sp ∗
        (slot7At s0.sp sc ∗ slotSp40At s0.sp sc ∗ slotSp70At s0.sp sc ∗
         slotFp90At s0.sp sc ∗ slotRetHeadAt s0.sp sc ∗ slotRetTailAt s0.sp sc) ∗
        kpkSavedRegs s0)
      ?_ (hnext := ?_)
    · dsimp only [decimalFsCellsSpec, kpkScratchAt, slotDecAt, kpkSavedRegs]
      rw [dec_off8, dec_off16]
      have hpure :
          (FsInv s0.fs.files s0.trace s_dec ∧
            s_dec.readReg64 .x0 = s0.sp - 264#64 ∧
            s_dec.readReg32 .x1 = x.id ∧
            s_dec.sp = s0.sp - 432#64 ∧
            FitsEnv M lim st0 (DecEnv x.id)) = True :=
        eq_true ⟨hfs_dec,
          by simp only [s_dec, arm64_norm],
          by simp only [s_dec, arm64_norm],
          hsp_dec, hfit_dec⟩
      rw [hpure, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_ad hcrl2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [decimalFsCellsSpec]
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun evsDec =>
        SepWPp.exists_elim fun nCap => SepWPp.exists_elim fun nPtr => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hfs2, htr2, hevsDec⟩ => ?_
      have hfit_after_dec := (by unfold KpkPassEnv at hfit_pass1; exact hfit_pass1 :
        FitsEnv M lim st0
          (SeqEnv (DecEnv x.id)
            (SeqEnv (GetEnv s0.fs.files x.kg.oneTime (keyName x.id))
              (SeqEnv (OptKpkDecodeEnv DecodeEnv
                (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                FreeOnlyEvs)))).seq_right hevsDec
      have hfit_get : FitsEnv M lim (M.stepEvents evsDec st0)
          (GetEnv s0.fs.files x.kg.oneTime (keyName x.id)) :=
        hfit_after_dec.seq_left
      have hsp_ad : s_ad.sp = s0.sp - 432#64 := hsp2.trans hsp_dec
      have hal_ad : s_ad.spAligned = true := sp_sub_432_spAligned hal0 hsp_ad
      let _ := hal_ad
      have htr_ad : s_ad.trace = s0.trace := htr2.trans htr_dec
      have hx19_ad : s_ad.readReg64 .x19 = x.fut :=
        hcsp2.1.trans (by simp only [s_dec, arm64_norm, *])
      have hx20_ad : s_ad.readReg64 .x20 = x.out :=
        hcsp2.2.1.trans (by simp only [s_dec, arm64_norm, *])
      have hx24_ad : s_ad.readReg64 .x24 = x.self :=
        hcsp2.2.2.2.2.2.1.trans (by simp only [s_dec, arm64_norm])
      have hx25_ad : s_ad.readReg64 .x25 = x.id.zeroExtend 64 :=
        hcsp2.2.2.2.2.2.2.1.trans (by simp only [s_dec, arm64_norm])
      have hx29_ad : s_ad.readReg64 .x29 = s0.sp - 96#64 :=
        hcsp2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dec, arm64_norm])
      have hvregs_ad : calleeSavedVRegs s_ad = calleeSavedVRegs s0 :=
        hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_dec
      let _ := And.intro hx24_ad hx29_ad
      -- `+68 .. +84`: `Dir::get(x29 - 0x60, self, nPtr, nLen)`
      rw [dec_off8, dec_off16]
      apply sepWPp_seq_lscro (mid := lsmpl.base 589) hcrl2
      wp_steps_sync_pool (lsmpl.base 589)
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcrl3
      apply bind_sepWPp_state; intro s_get
      have hsp_get : s_get.sp = s0.sp - 432#64 := by simp only [s_get, arm64_norm, hsp_ad]
      have hal_get : s_get.spAligned = true := sp_sub_432_spAligned hal0 hsp_get
      have htr_get : s_get.trace = s0.trace := by simp only [s_get, arm64_norm, htr_ad]
      have hfs_get : FsInv s0.fs.files s0.trace s_get :=
        fsInv_of_eq hfs2 (by simp only [s_get, arm64_norm]) (by simp only [s_get, arm64_norm])
      refine kpk_call_total_lscro
        ((s0.sp - 192#64, x.self, x.kg.oneTime, x.id, nCap, nPtr,
          sc.ret0, sc.ret1, sc.ret2, sc.ret3, sc.ret4, sc.ret5, s0.sp - 432#64),
          M.stepEvents evsDec st0)
        hGetCells hcrl3
        (by simp only [s_get, arm64_norm])
        (by simp only [s_get, arm64_norm, *])
        hal_get
        (ret_pc := (blkPl_576).base + 88#64)
        (by simp only [s_get, arm64_norm])
        (F := words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
          (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          kpkSlack3 s0.sp ∗
          (slot7At s0.sp sc ∗ slotSp40At s0.sp sc ∗ slotSp70At s0.sp sc ∗
           ((s0.sp - 264#64) ↦₆₄ nCap) ∗ ((s0.sp - 256#64) ↦₆₄ nPtr) ∗
           ((s0.sp - 248#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
           slotFp90At s0.sp sc ∗ slotRetTailAt s0.sp sc) ∗
          kpkSavedRegs s0)
        ?_ (hnext := ?_)
      · dsimp only [dirGetFsCellsSpec, slotRetHeadAt]
        rw [words6At_retSlot]
        have hpure :
            (FsInv s0.fs.files s0.trace s_get ∧ s_get.trace = s0.trace ∧
              PkNameOk pathOk x.kg.oneTime x.id ∧
              s_get.readReg64 .x0 = s0.sp - 192#64 ∧
              s_get.readReg64 .x1 = x.self ∧
              s_get.readReg64 .x2 = nPtr ∧
              s_get.readReg64 .x3 = BitVec.ofNat 64 (keyName x.id).length ∧
              s_get.sp = s0.sp - 432#64 ∧
              FitsEnv M lim (M.stepEvents evsDec st0)
                (GetEnv s0.fs.files x.kg.oneTime (keyName x.id))) = True :=
          eq_true ⟨hfs_get, htr_get, hn1,
            by simp only [s_get, arm64_norm],
            by simp only [s_get, arm64_norm, *],
            by simp only [s_get, arm64_norm],
            by simp only [s_get, arm64_norm],
            hsp_get, hfit_get⟩
        rw [hpure, ProofLib.pure_true, emp_sepConj]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s_ag hcrl4 hpc4 hrun4 hsp4 hcsp4
        dsimp only [dirGetFsCellsSpec]
        simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun evsGet =>
          SepWPp.exists_elim fun r =>
          SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
          SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
          SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 =>
          SepWPp.exists_elim fun H_post => ?_
        rw [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hprop, hevsGet⟩ => ?_
        have hfit_after_get := hfit_after_dec.seq_right hevsGet
        rw [← M.stepEvents_append] at hfit_after_get ⊢
        rw [words6At_retSlot]
        have hsp_ag : s_ag.sp = s0.sp - 432#64 := hsp4.trans hsp_get
        have hal_ag : s_ag.spAligned = true := sp_sub_432_spAligned hal0 hsp_ag
        let _ := hal_ag
        have hx19_ag : s_ag.readReg64 .x19 = x.fut :=
          hcsp4.1.trans (by simp only [s_get, arm64_norm, hx19_ad])
        have hx20_ag : s_ag.readReg64 .x20 = x.out :=
          hcsp4.2.1.trans (by simp only [s_get, arm64_norm, hx20_ad])
        have hx21_ag : s_ag.readReg64 .x21 = nPtr :=
          hcsp4.2.2.1.trans (by simp only [s_get, arm64_norm])
        have hx24_ag : s_ag.readReg64 .x24 = x.self :=
          hcsp4.2.2.2.2.2.1.trans (by simp only [s_get, arm64_norm, hx24_ad])
        have hx25_ag : s_ag.readReg64 .x25 = x.id.zeroExtend 64 :=
          hcsp4.2.2.2.2.2.2.1.trans (by simp only [s_get, arm64_norm, hx25_ad])
        have hx29_ag : s_ag.readReg64 .x29 = s0.sp - 96#64 :=
          hcsp4.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_get, arm64_norm, hx29_ad])
        have hvregs_ag : calleeSavedVRegs s_ag = calleeSavedVRegs s0 :=
          hcsp4.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [s_get, calleeSavedVRegs, arm64_norm]; exact hvregs_ad)
        let _ := hx29_ag
        let sc_ag : KpkScratch :=
          { sc with
            dec0 := nCap, dec1 := nPtr, dec2 := BitVec.ofNat 64 (keyName x.id).length,
            ret0 := w0, ret1 := w1, ret2 := w2, ret3 := w3, ret4 := w4, ret5 := w5 }
        have sameAg :
            slot7At s0.sp sc_ag = slot7At s0.sp sc ∧
            slotSp40At s0.sp sc_ag = slotSp40At s0.sp sc ∧
            slotSp70At s0.sp sc_ag = slotSp70At s0.sp sc ∧
            slotFp90At s0.sp sc_ag = slotFp90At s0.sp sc ∧
            slotRetTailAt s0.sp sc_ag = slotRetTailAt s0.sp sc :=
          ⟨rfl, rfl, rfl, rfl, rfl⟩
        rcases r with ⟨⟩ | ⟨⟩ | ⟨b0, bs⟩
        · -- `Dir::get` returned `.error ()` -> `+412`
          rcases hprop with ⟨hw0, hr_disj, hread_ent⟩
          subst hw0
          apply sepWPp_seq_lscro (mid := (blkPl_576).base + 412#64) hcrl4
          wp_steps_sync_pool ((blkPl_576).base + 412#64)
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hcrl5
          apply bind_sepWPp_state; intro s_err
          have hans_err :
              .readErr = kpkAnsOf
                    (pkAnsOf KyberPreKeyRecord.deserialize
                      (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                    (pkAnsOf KyberPreKeyRecord.deserialize
                      (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
                  s_err.trace = s0.trace := by
            have htr_e : s_err.trace = s_ag.trace := by simp only [s_err, arm64_norm]
            rcases hr_disj with ⟨hget_e, htr_eq⟩
            refine ⟨?_, htr_e.trans htr_eq⟩
            rw [hget_e]; rfl
          have hopt_nil :
              OptKpkDecodeEnv DecodeEnv
                (x.kg.oneTime.get rd s0.fs.files (keyName x.id)) [] := by
            rw [hr_disj.1]; rfl
          refine SepWPp.weaken_pre ?_
            (step_dir_err_ret_placed hC hFs hle_hook hhi x st0 (evsDec ++ evsGet) sc_ag nPtr
              u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 H_post hal0 hcrl5
              (by simp only [s_err, arm64_norm])
              (by simp only [s_err, arm64_norm, *])
              (by simp only [s_err, arm64_norm, hsp_ag])
              (by simp only [s_err, calleeSavedVRegs, arm64_norm] at hvregs_ag ⊢; exact hvregs_ag)
              (by simp only [s_err, arm64_norm, hx29_ag])
              (by simp only [s_err, arm64_norm, hx19_ag])
              (by simp only [s_err, arm64_norm, hx20_ag])
              (by simp only [s_err, arm64_norm, hx21_ag])
              (by simp only [s_err, arm64_norm])
              hans_err
              (fun evsF hF => by
                unfold CliKpkGetPollEnv
                rw [hr_disj.1]
                dsimp only [pkAnsOf]
                have hp1 : KpkPassEnv DecEnv
                    (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
                    rd s0.fs.files x.kg.oneTime x.id
                    (evsDec ++ (evsGet ++ ([] ++ evsF))) :=
                  SeqEnv.append hevsDec (SeqEnv.append hevsGet (SeqEnv.append hopt_nil hF))
                simpa only [List.append_assoc, List.nil_append] using hp1)
              hread_ent)
          dsimp only [kpkScratchAt]
          rw [sameAg.1, sameAg.2.1, sameAg.2.2.1, sameAg.2.2.2.1, sameAg.2.2.2.2]
          dsimp only [slotDecAt, slotRetHeadAt, sc_ag]
          exact Entails.of_eq (by sep_ac_rfl)
        · -- `Dir::get` returned `.ok []` -> `+180` (`step_ot_empty_next_placed`)
          rcases hprop with ⟨hget_empty, hfs_ag, htr_ag, hw0, hw3, hH⟩
          subst hw0 hw3 hH
          apply sepWPp_seq_lscro (mid := (blkPl_576).base + 180#64) hcrl4
          wp_steps_sync_pool ((blkPl_576).base + 180#64)
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hcrl5
          apply bind_sepWPp_state; intro s_m
          have hfs_m : FsInv s0.fs.files s0.trace s_m :=
            fsInv_of_eq hfs_ag (by simp only [s_m, arm64_norm]) (by simp only [s_m, arm64_norm])
          have hmiss1 : pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.oneTime.get rd s0.fs.files (keyName x.id)) = .missing := by
            rw [hget_empty]; rfl
          have hopt_nil :
              OptKpkDecodeEnv DecodeEnv
                (x.kg.oneTime.get rd s0.fs.files (keyName x.id)) [] := by
            rw [hget_empty]; rfl
          refine SepWPp.weaken_pre ?_
            (step_ot_empty_next_placed hC hDeps hFs
              hle_dec hle_get hle_root hle_hook hhi hSub hSup
              x st0 (evsDec ++ evsGet) sc_ag nPtr w1 w2
              u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 hn2 hs2 hmiss1
              (fun evsF hF => by
                have hp1 : KpkPassEnv DecEnv
                    (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
                    rd s0.fs.files x.kg.oneTime x.id
                    (evsDec ++ (evsGet ++ ([] ++ evsF))) :=
                  SeqEnv.append hevsDec (SeqEnv.append hevsGet (SeqEnv.append hopt_nil hF))
                simpa only [List.append_assoc, List.nil_append] using hp1)
              hfit0 hal0 hcrl5 hfs_m
              (by simp only [s_m, arm64_norm])
              (by simp only [s_m, arm64_norm, *])
              (by simp only [s_m, arm64_norm, hsp_ag])
              (by simp only [s_m, arm64_norm, htr_ag])
              (by simp only [s_m, calleeSavedVRegs, arm64_norm] at hvregs_ag ⊢; exact hvregs_ag)
              (by simp only [s_m, arm64_norm, hx29_ag])
              (by simp only [s_m, arm64_norm])
              (by simp only [s_m, arm64_norm, hx19_ag])
              (by simp only [s_m, arm64_norm, hx20_ag])
              (by simp only [s_m, arm64_norm, hx21_ag])
              (by simp only [s_m, arm64_norm])
              (by simp only [s_m, arm64_norm, hx24_ag])
              (by simp only [s_m, arm64_norm, hx25_ag]))
          dsimp only [kpkScratchAt]
          rw [sameAg.1, sameAg.2.1, sameAg.2.2.1, sameAg.2.2.2.1, sameAg.2.2.2.2]
          dsimp only [slotDecAt, slotRetHeadAt, sc_ag]
          exact Entails.of_eq (by sep_ac_rfl)
        · -- `Dir::get` returned `.ok (b0 :: bs)` -> `decode_kyber_pre_key` (`+128`)
          rcases hprop with ⟨hget_ne, hfs_ag, htr_ag, hw0, hw3, hH⟩
          subst hw0 hw3 hH
          have hfit_dk : FitsEnv M lim (M.stepEvents (evsDec ++ evsGet) st0)
              (DecodeEnv (b0 :: bs)) := by
            have hseq := hfit_after_get.seq_left
            rwa [hget_ne] at hseq
          have hlen_pos : 0 < (b0 :: bs).length := List.length_pos_of_ne_nil (by simp)
          have hlen_lt : (b0 :: bs).length < 2 ^ 32 := hs1 (b0 :: bs) hget_ne
          have hlen_ne : BitVec.ofNat 64 (b0 :: bs).length ≠ 0#64 :=
            ofNat_len_ne_zero hlen_pos hlen_lt
          have hlen_beq : (BitVec.ofNat 64 (b0 :: bs).length == 0#64) = false :=
            beq_eq_false_iff_ne.mpr hlen_ne
          have hlen_bne : (BitVec.ofNat 64 (b0 :: bs).length != 0#64) = true :=
            bne_iff_ne.mpr hlen_ne
          have _ := And.intro hlen_beq hlen_bne
          apply sepWPp_seq_lscro (mid := lsmpl.base 595) hcrl4
          dsimp only [slot7At]
          wp_steps_sync_pool (lsmpl.base 595)
          apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          intro hcrl5
          apply bind_sepWPp_state; intro s_dk
          have hsp_dk : s_dk.sp = s0.sp - 432#64 := by simp only [s_dk, arm64_norm, hsp_ag]
          have hal_dk : s_dk.spAligned = true := sp_sub_432_spAligned hal0 hsp_dk
          have htr_dk : s_dk.trace = s0.trace := by simp only [s_dk, arm64_norm, htr_ag]
          have hfs_dk : FsInv s0.fs.files s0.trace s_dk :=
            fsInv_of_eq hfs_ag (by simp only [s_dk, arm64_norm]) (by simp only [s_dk, arm64_norm])
          refine kpk_call_total_lscro
            ((s0.sp - 192#64, w1, w2, b0 :: bs,
              0xFFFFFFFFFFFFFFFE#64, w1, w2, BitVec.ofNat 64 (b0 :: bs).length, w4, w5,
              sc.ret6, sc.ret7, sc.ret8, sc.ret9, sc.ret10, s0.sp - 432#64),
              M.stepEvents (evsDec ++ evsGet) st0)
            hDecodeCells hcrl5
            (by simp only [s_dk, arm64_norm])
            (by simp only [s_dk, arm64_norm, *])
            hal_dk
            (ret_pc := (blkPl_576).base + 132#64)
            (by simp only [s_dk, arm64_norm])
            (F := vecU8Buf A.repAlloc nCap nPtr (keyName x.id) ∗
              words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
              (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
              dirAt A.repAlloc x.self x.kg.oneTime ∗
              dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
              kpkSlack3 s0.sp ∗
              (((s0.sp - 424#64) ↦₆₄ w1) ∗
               ((s0.sp - 416#64) ↦₆₄ sc.sp10_0) ∗ ((s0.sp - 408#64) ↦₆₄ sc.sp10_1) ∗
               ((s0.sp - 400#64) ↦₆₄ sc.sp10_2) ∗ ((s0.sp - 392#64) ↦₆₄ sc.sp10_3) ∗
               ((s0.sp - 384#64) ↦₆₄ sc.sp10_4) ∗ ((s0.sp - 376#64) ↦₆₄ sc.sp10_5) ∗
               slotSp40At s0.sp sc ∗ slotSp70At s0.sp sc ∗
               ((s0.sp - 264#64) ↦₆₄ nCap) ∗ ((s0.sp - 256#64) ↦₆₄ nPtr) ∗
               ((s0.sp - 248#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
               slotFp90At s0.sp sc) ∗
              kpkSavedRegs s0)
            ?_ (hnext := ?_)
          · dsimp only [decodeFsCellsSpec, slotRetTailAt]
            rw [words11At_retSlot]
            have hpure :
                (FsInv s0.fs.files s0.trace s_dk ∧ s_dk.trace = s0.trace ∧
                  0 < (b0 :: bs).length ∧ (b0 :: bs).length < 2 ^ 32 ∧
                  s_dk.readReg64 .x0 = s0.sp - 192#64 ∧
                  s_dk.readReg64 .x1 = w2 ∧
                  s_dk.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs).length ∧
                  s_dk.sp = s0.sp - 432#64 ∧
                  FitsEnv M lim (M.stepEvents (evsDec ++ evsGet) st0)
                    (DecodeEnv (b0 :: bs))) = True :=
              eq_true ⟨hfs_dk, htr_dk, hlen_pos, hlen_lt,
                by simp only [s_dk, arm64_norm],
                by simp only [s_dk, arm64_norm],
                by simp only [s_dk, arm64_norm],
                hsp_dk, hfit_dk⟩
            rw [hpure, ProofLib.pure_true, emp_sepConj]
            exact Entails.of_eq (by sep_ac_rfl)
          · intro s_adk hcrl6 hpc6 hrun6 hsp6 hcsp6
            dsimp only [decodeFsCellsSpec]
            simp only [sepExists_sepConj_left]
            refine SepWPp.exists_elim fun evsDk =>
              SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
              SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
              SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 =>
              SepWPp.exists_elim fun d6 => SepWPp.exists_elim fun d7 =>
              SepWPp.exists_elim fun d8 => SepWPp.exists_elim fun d9 =>
              SepWPp.exists_elim fun d10 => SepWPp.exists_elim fun Hdec => ?_
            rw [sepConj_assoc]
            refine SepWPp.pure_elim fun ⟨hdprop, hevsDk⟩ => ?_
            rw [← M.stepEvents_append]
            rw [words11At_retSlot]
            have hopt_dk :
                OptKpkDecodeEnv DecodeEnv
                  (x.kg.oneTime.get rd s0.fs.files (keyName x.id)) evsDk := by
              rw [hget_ne]; exact hevsDk
            have hevs_pass1_dk : ∀ evsF, FreeOnlyEvs evsF →
                KpkPassEnv DecEnv
                  (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
                  rd s0.fs.files x.kg.oneTime x.id
                  (((evsDec ++ evsGet) ++ evsDk) ++ evsF) := by
              intro evsF hF
              have hp1 : KpkPassEnv DecEnv
                  (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv
                  rd s0.fs.files x.kg.oneTime x.id
                  (evsDec ++ (evsGet ++ (evsDk ++ evsF))) :=
                SeqEnv.append hevsDec (SeqEnv.append hevsGet (SeqEnv.append hopt_dk hF))
              simpa only [List.append_assoc] using hp1
            have hsp_adk : s_adk.sp = s0.sp - 432#64 := hsp6.trans hsp_dk
            have hal_adk : s_adk.spAligned = true := sp_sub_432_spAligned hal0 hsp_adk
            let _ := hal_adk
            have hx19_adk : s_adk.readReg64 .x19 = x.fut :=
              hcsp6.1.trans (by simp only [s_dk, arm64_norm, hx19_ag])
            have hx20_adk : s_adk.readReg64 .x20 = x.out :=
              hcsp6.2.1.trans (by simp only [s_dk, arm64_norm, hx20_ag])
            have hx21_adk : s_adk.readReg64 .x21 = nPtr :=
              hcsp6.2.2.1.trans (by simp only [s_dk, arm64_norm, hx21_ag])
            have hx22_adk : s_adk.readReg64 .x22 = w2 :=
              hcsp6.2.2.2.1.trans (by simp only [s_dk, arm64_norm])
            have hx27_adk : s_adk.readReg64 .x27 = s0.sp - 192#64 :=
              hcsp6.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dk, arm64_norm])
            have hx29_adk : s_adk.readReg64 .x29 = s0.sp - 96#64 :=
              hcsp6.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dk, arm64_norm, hx29_ag])
            have hvregs_adk : calleeSavedVRegs s_adk = calleeSavedVRegs s0 :=
              hcsp6.2.2.2.2.2.2.2.2.2.2.2.trans
                (by simp only [s_dk, calleeSavedVRegs, arm64_norm]; exact hvregs_ag)
            let _ := And.intro hx22_adk (And.intro hx27_adk hx29_adk)
            unfold decodePostProp at hdprop
            rcases hdprop with ⟨_hfs_adk, htr_adk, hdcase⟩
            cases hdes : KyberPreKeyRecord.deserialize (b0 :: bs) with
            | error e =>
              rw [hdes] at hdcase
              rcases hdcase with ⟨hd0, hdec_ent⟩
              subst hd0
              let sc_de : KpkScratch :=
                { sc with
                  sp08 := w1,
                  dec0 := nCap, dec1 := nPtr, dec2 := BitVec.ofNat 64 (keyName x.id).length,
                  ret0 := 0xFFFFFFFFFFFFFFFF#64, ret1 := d1, ret2 := d2, ret3 := d3,
                  ret4 := d4, ret5 := d5, ret6 := d6, ret7 := d7, ret8 := d8,
                  ret9 := d9, ret10 := d10 }
              have sameDe :
                  slotSp40At s0.sp sc_de = slotSp40At s0.sp sc ∧
                  slotSp70At s0.sp sc_de = slotSp70At s0.sp sc ∧
                  slotFp90At s0.sp sc_de = slotFp90At s0.sp sc :=
                ⟨rfl, rfl, rfl⟩
              apply sepWPp_seq_lscro (mid := (blkPl_576).base + 440#64) hcrl6
              wp_steps_sync_pool ((blkPl_576).base + 440#64)
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hcrl7
              apply bind_sepWPp_state; intro s_de
              have hans_de : .decodeErr e = kpkAnsOf
                  (pkAnsOf KyberPreKeyRecord.deserialize
                    (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                  (pkAnsOf KyberPreKeyRecord.deserialize
                    (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) := by
                rw [hget_ne]; simp [pkAnsOf, hdes, kpkAnsOf]
              refine SepWPp.weaken_pre ?_
                (step_dec_err_ret_placed hC hFs hle_hook hhi x st0
                  ((evsDec ++ evsGet) ++ evsDk) sc_de nPtr w2 (b0 :: bs)
                  u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 e Hdec hal0 hcrl7
                  (by simp only [s_de, arm64_norm])
                  (by simp only [s_de, arm64_norm, *])
                  (by simp only [s_de, arm64_norm, hsp_adk])
                  (by simp only [s_de, arm64_norm, htr_adk])
                  (by simp only [s_de, calleeSavedVRegs, arm64_norm] at hvregs_adk ⊢; exact hvregs_adk)
                  (by simp only [s_de, arm64_norm, hx29_adk])
                  (by simp only [s_de, arm64_norm, hx27_adk])
                  (by simp only [s_de, arm64_norm])
                  (by simp only [s_de, arm64_norm, hx19_adk])
                  (by simp only [s_de, arm64_norm, hx20_adk])
                  (by simp only [s_de, arm64_norm, hx21_adk])
                  hans_de
                  (fun evsF hF => by
                    unfold CliKpkGetPollEnv
                    rw [hget_ne]
                    dsimp only [pkAnsOf]
                    rw [hdes]
                    exact hevs_pass1_dk evsF hF)
                  hdec_ent)
              dsimp only [kpkScratchAt]
              rw [sameDe.1, sameDe.2.1, sameDe.2.2]
              dsimp only [slot7At, slotDecAt, slotRetHeadAt, slotRetTailAt, sc_de]
              exact Entails.of_eq (by sep_ac_rfl)
            | ok rec =>
              rw [hdes] at hdcase
              rcases hdcase with ⟨hd0_lt, hfound_ent⟩
              have h1 := cmn_lt63_eq_false hd0_lt
              have h2 := cmn_lt63_ne_true hd0_lt
              have h3 := add1_lt63_beq_zero hd0_lt
              have h4 := add1_lt63_bne_zero hd0_lt
              have _ := And.intro h1 (And.intro h2 (And.intro h3 h4))
              let sc_ok : KpkScratch :=
                { sc with
                  sp08 := w1,
                  sp40_0 := d7, sp40_1 := d8, sp40_2 := d9, sp40_3 := d10, sp40_4 := d5, sp40_5 := d6,
                  sp70_0 := d7, sp70_1 := d8, sp70_2 := d9, sp70_3 := d10, sp70_4 := d5, sp70_5 := d6,
                  dec0 := nCap, dec1 := nPtr, dec2 := BitVec.ofNat 64 (keyName x.id).length,
                  fp90_0 := d7, fp90_1 := d8, fp90_2 := d9, fp90_3 := d10, fp90_4 := d5, fp90_5 := d6,
                  ret0 := d0, ret1 := d1, ret2 := d2, ret3 := d3,
                  ret4 := d4, ret5 := d5, ret6 := d6, ret7 := d7, ret8 := d8,
                  ret9 := d9, ret10 := d10 }
              apply sepWPp_seq_lscro (mid := (blkPl_576).base + 216#64) hcrl6
              dsimp only [slotSp40At, slotSp70At, slotFp90At]
              wp_steps_sync_pool ((blkPl_576).base + 216#64)
              apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
              intro hcrl7
              apply bind_sepWPp_state; intro s_ok
              have hans_ok : .found rec = kpkAnsOf
                  (pkAnsOf KyberPreKeyRecord.deserialize
                    (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                  (pkAnsOf KyberPreKeyRecord.deserialize
                    (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) := by
                rw [hget_ne]; simp [pkAnsOf, hdes, kpkAnsOf]
              refine SepWPp.weaken_pre ?_
                (step_dec_ok_ret_placed hC hFs hle_hook hhi x st0
                  ((evsDec ++ evsGet) ++ evsDk) sc_ok nPtr w1 w2 (b0 :: bs)
                  d0 d1 d2 d3 d4
                  u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 rec Hdec hal0 hcrl7
                  (by simp only [s_ok, arm64_norm])
                  (by simp only [s_ok, arm64_norm, *])
                  (by simp only [s_ok, arm64_norm, hsp_adk])
                  (by simp only [s_ok, arm64_norm, htr_adk])
                  (by simp only [s_ok, calleeSavedVRegs, arm64_norm] at hvregs_adk ⊢; exact hvregs_adk)
                  (by simp only [s_ok, arm64_norm, hx29_adk])
                  (by simp only [s_ok, arm64_norm])
                  (by simp only [s_ok, arm64_norm])
                  (by simp only [s_ok, arm64_norm, hx19_adk])
                  (by simp only [s_ok, arm64_norm, hx20_adk])
                  (by simp only [s_ok, arm64_norm, hx21_adk])
                  (by simp only [s_ok, arm64_norm, hx22_adk])
                  (by simp only [s_ok, arm64_norm])
                  (by simp only [s_ok, arm64_norm])
                  (by simp only [s_ok, arm64_norm])
                  (by simp only [s_ok, arm64_norm])
                  hans_ok
                  (fun evsF hF => by
                    unfold CliKpkGetPollEnv
                    rw [hget_ne]
                    dsimp only [pkAnsOf]
                    rw [hdes]
                    exact hevs_pass1_dk evsF hF)
                  (hfound_ent x.out))
              dsimp only [kpkScratchAt, slot7At, slotSp40At, slotSp70At, slotDecAt,
                slotFp90At, slotRetHeadAt, slotRetTailAt, sc_ok]
              exact Entails.of_eq (by sep_ac_rfl)
  refine ⟨_, ?_, hwp⟩
  convert hmem_ready using 1; sep_ac_rfl

/-- Full symbolic proof of `cliKpkGetPollInnerSpec` on `lsProg_576 H` under `[LibsignalPlacement]`. -/
theorem kpkGetPollInner_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_576 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_576 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk))
    (hDec : subroutine_ok (lsProg_576 H) (lsmpl.base 595)
      (decodeKyberPreKeyPlacedSpec A lim))
    (hle_dec : decStk ≤ calleeStk)
    (hle_get : getStk ≤ calleeStk)
    (hle_root : smallRootStack ≤ calleeStk)
    (hle_hook : extHookStack ≤ calleeStk)
    (hFs : TraceFsSound (lsProg_576 H))
    (hhi : calleeStk ≤ 2 ^ 64)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs) :
    subroutine_ok (lsProg_576 H) ((blkPl_576).base)
      (withLsCodeRoLoaded lsmpl
        (cliKpkGetPollInnerSpec rd pathOk A lim DecEnv (fun dir id => GetEnv dir (keyName id))
          DecodeEnv calleeStk)) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre0 hal0
  obtain ⟨P, hmP, hwp⟩ := kpkGetPollInner_sepWPp_of_pre (GetEnv := fun _ => GetEnv)
    hC hDecimal hGet hDec hle_dec hle_get hle_root hle_hook hFs hhi hSub hSup
    x st0 R s0 hpc0 hrun0 hpre0 hal0
  refine ⟨P, R, hmP, fun R' hm' hL => ?_⟩
  rcases hwp R' hm' hL with
    ⟨sf, hsteps,
      ⟨hpc_f, hrun_f, P_f, hm_f, hsp_f, hcs_f, hent_f⟩ |
      ⟨_, _, _, hfalse⟩ |
      hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, P_f, hm_f,
      ⟨fun hmfR => ?_, hsp_f, hcs_f⟩⟩⟩
    dsimp only [withLsCodeRoLoaded]
    exact Satisfies.mono (sepConj_mono_left hent_f) hmfR
  · exact hfalse.elim
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Outer `kpkGetPollSpecPlaced` proof on `lsProg_576 H` for state-independent `GetEnv`. -/
theorem kpkGetPoll_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_576 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_576 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim (fun _ => GetEnv) getStk))
    (hDec : subroutine_ok (lsProg_576 H) (lsmpl.base 595)
      (decodeKyberPreKeyPlacedSpec A lim))
    (hFs : TraceFsSound (lsProg_576 H))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs) :
    subroutine_ok (lsProg_576 H) ((blkPl_576).base)
      (kpkGetPollSpecPlaced rd pathOk A lim
        (CliKpkGetPollEnv DecEnv (fun dir id => GetEnv dir (keyName id)) DecodeEnv rd) stk) :=
  kpkGetPoll_placed_of_inner
    (calleeStk := max (max decStk getStk) (max smallRootStack extHookStack))
    (fun hhi => kpkGetPollInner_placed_ok hC hDecimal hGet hDec
      (by omega) (by omega) (by omega) (by omega) hFs hhi hSub hSup)
    hstk

/-- Direct `kpkGetPollSpecPlaced` proof on `lsProg_576 H` accepting an arbitrary `FsFiles`-indexed
`GetEnv` in `dirGetSpecPlaced`. -/
theorem kpkGetPoll_placed_fs_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hDecimal : subroutine_ok (lsProg_576 H) (lsmpl.base 597)
      (decimalSpecPlaced A lim DecEnv decStk))
    (hGet : subroutine_ok (lsProg_576 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hDec : subroutine_ok (lsProg_576 H) (lsmpl.base 595)
      (decodeKyberPreKeyPlacedSpec A lim))
    (hFs : TraceFsSound (lsProg_576 H))
    (hstk : 0x1b0 + max (max decStk getStk) (max smallRootStack extHookStack) ≤ stk)
    (hSub : ∀ bs evs, SpkLoopEnv (2 * bs.length + 3) bs.length evs → DecodeEnv bs evs)
    (hSup : ∀ bs evs, KyberDecodeEnv bs.length evs → DecodeEnv bs evs) :
    subroutine_ok (lsProg_576 H) ((blkPl_576).base)
      (kpkGetPollSpecPlaced rd pathOk A lim
        (fun F0 x =>
          CliKpkGetPollEnv DecEnv (fun dir id => GetEnv F0 dir (keyName id)) DecodeEnv rd F0 x)
        stk) := by
  set calleeStk := max (max decStk getStk) (max smallRootStack extHookStack)
  apply subroutine_ok_of_sepWPp
  intro ⟨x, st0⟩ R s0 hpc0 hrun0 hpre0 hal0
  unfold kpkGetPollSpecPlaced at hpre0
  obtain ⟨hcrl, hpre0⟩ := extract_withLsCodeRoLoaded hpre0
  dsimp only at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx8, hn1, hn2, hs1, hs2, hfit⟩, hmem⟩
  dsimp only [pkBoxAt] at hmem
  have hstk_hi : stk ≤ 2 ^ 64 := by
    refine memRegion_bound_of_pointsTo64 (m := s0.mem) (b := s0.sp - BitVec.ofNat 64 stk)
      (a := x.fut) (v := x.self)
      (R := ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        memRegion (x.fut + 0xd#64) 3 ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        memRegion x.out 88 ∗ A.pool lim st0 s0 ∗ R) ?_
    dsimp only [stackAt] at hmem
    convert hmem using 1; sep_ac_rfl
  have hcal_hi : calleeStk ≤ 2 ^ 64 := by omega
  have hframe_hi : calleeStk + 432 ≤ 2 ^ 64 := by omega
  rw [stackAt_sub_split s0.sp (subStk := calleeStk + 432) (by omega) hstk_hi,
    stackAt_kpkPoll_frame s0.sp hframe_hi] at hmem
  let F_extra := memRegion (x.fut + 0xd#64) 3 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (calleeStk + 432))
  have hpre_in : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (cliKpkGetPollInnerSpec rd pathOk A lim DecEnv
          (fun dir id => GetEnv s0.fs.files dir (keyName id)) DecodeEnv calleeStk)).pre
        (x, st0) s0 ∗ (F_extra ∗ R) := by
    refine satisfies_lscro_pre hcrl ?_
    dsimp only [cliKpkGetPollInnerSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨withFsInv_entry s0, hx0, hx8, hn1, hn2, hs1, hs2, hfit⟩, ?_⟩
    dsimp only [F_extra]
    convert hmem using 1; sep_ac_rfl
  obtain ⟨P, hmP, hwp⟩ := kpkGetPollInner_sepWPp_of_pre (GetEnv := GetEnv)
    hC hDecimal hGet hDec (by omega) (by omega) (by omega) (by omega) hFs hcal_hi hSub hSup
    x st0 (F_extra ∗ R) s0 hpc0 hrun0 hpre_in hal0
  refine ⟨P, F_extra ∗ R, hmP, fun R' hm' hL => ?_⟩
  rcases hwp R' hm' hL with
    ⟨sf, hsteps,
      ⟨hpc_f, hrun_f, P_f, hm_f, hsp_f, hcs_f, hent_f⟩ |
      ⟨_, _, _, hfalse⟩ |
      hoom⟩
  · refine ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, P_f, hm_f,
      ⟨fun hmf_Fr => ?_, hsp_f, hcs_f⟩⟩⟩
    have hq := Satisfies.mono (sepConj_mono_left hent_f) hmf_Fr
    dsimp only [withLsCodeRoLoaded, cliKpkGetPollInnerSpec,
      kpkGetPollSpecPlaced, pkBoxAt] at hq ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hq ⊢
    rcases hq with ⟨evs, hq⟩
    refine ⟨evs, ?_⟩
    rw [stackAt_sub_split s0.sp (subStk := calleeStk + 432) (by omega) hstk_hi,
      stackAt_kpkPoll_frame s0.sp hframe_hi]
    dsimp only [F_extra] at hq
    convert hq using 1; sep_ac_rfl
  · exact hfalse.elim
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.SymPlacedBudget
