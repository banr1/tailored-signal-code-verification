/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.EpiloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LastResort
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Relocatable `last_resort` Arm for `get_kyber_pre_key::{closure#0}`

Verifies the `last_resort` directory lookup and missing-file cleanup (`+288`) on Block `576` under
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CliKpkGetPollNorm

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

/-! ## `last_resort` missing-file cleanup (`+628`, `+572`) and full `last_resort` arm (`+288`) -/

theorem step_missing_free_name_ret_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_hook : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (x : KpkPollGhost) {s0 s : State}
    (sc : KpkScratch) (nPtr : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (hal0 : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_576).base + 628#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = nPtr)
    (hans_eq : .missing = kpkAnsOf
      (pkAnsOf KyberPreKeyRecord.deserialize (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
      (pkAnsOf KyberPreKeyRecord.deserialize (x.kg.lastResort.get rd s0.fs.files (keyName x.id)))) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (SpqrV1.Alloc.vecU8Buf A sc.dec0 nPtr (keyName x.id) ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost rd pathOk A calleeStk x s0)
      (KpkPanicAllow s0) := by
  by_cases hnCap : sc.dec0 = 0#64
  · have hdrop : SpqrV1.Alloc.vecU8Buf A sc.dec0 nPtr (keyName x.id) ⊢ emp := by
      rw [hnCap]; exact vecU8Buf_zero_entails_emp A nPtr (keyName x.id)
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left hdrop) (Entails.of_eq (emp_sepConj _))) ?_
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply SepWPp.of_sepWP (mid := (blkPl_576).base + 500#64)
    dsimp only [lsProg_576, kpkScratchAt, slotDecAt]
    rw [hnCap]
    wp_steps
    apply bind_sepWP_state; intro s1
    apply SepWP.done (by simp only [s1, arm64_norm, *]) (by simp only [s1, arm64_norm, *])
    refine SepWPp.weaken_pre ?_
      (step_epilogue_write_ret_placed x sc
        0xFFFFFFFFFFFFFFFF#64 0x800000000000000F#64
        (s1.readReg64 .x26) (s1.readReg64 .x27) (s1.readReg64 .x28)
        u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 .missing emp hal0
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs)
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm])
        rfl rfl rfl
        ⟨hans_eq, by simp only [s1, arm64_norm, htr]⟩
        (by rw [sepConj_emp]; exact words11At_missing_entails A x.out _ _ _ _ _ _ _ _ _))
    rw [emp_sepConj]
    dsimp only [kpkScratchAt, slotDecAt]
    rw [hnCap]
    exact Entails.of_eq (by ac_rfl)
  · have hn_beq : (sc.dec0 == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hn_bne : (sc.dec0 != 0#64) = true := bne_iff_ne.mpr hnCap
    have _ := And.intro hn_beq hn_bne
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply StoreKit.sepWPp_seq_lscro (mid := (lsρ lsRustDeallocSymCli)) hcrl
    dsimp only [lsProg_576, kpkScratchAt, slotDecAt]
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_dl
    have hsp_dl : s_dl.sp = s0.sp - 432#64 := by simp only [s_dl, arm64_norm, hsp]
    have hal_dl : s_dl.spAligned = true := sp_sub_432_spAligned hal0 hsp_dl
    have hdealloc := deallocVecBuf_cells_placed_ok (F0 := s_dl.fs.files) (T0 := s_dl.trace)
      hC hFs hle_hook hhi
    refine kpk_call_lscro (sc.dec0, nPtr, keyName x.id, s0.sp - 432#64) hdealloc hcrl1
      (by simp only [s_dl, wp_norm, arm64_norm])
      (by simp only [s_dl, arm64_norm, *])
      hal_dl
      (ret_pc := (blkPl_576).base + 648#64)
      (by simp only [s_dl, arm64_norm])
      (F := words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      ?_ (hnext := ?_)
    · dsimp only [deallocVecBufCellsSpec, kpkScratchAt, slotDecAt]
      have hpure_dl :
          (FsInv s_dl.fs.files s_dl.trace s_dl ∧ sc.dec0 ≠ 0#64 ∧
            s_dl.readReg64 .x0 = nPtr ∧ s_dl.readReg64 .x1 = sc.dec0 ∧
            s_dl.readReg64 .x2 = 1#64 ∧ s_dl.sp = s0.sp - 432#64) = True :=
        eq_true ⟨withFsInv_entry s_dl, hnCap,
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm],
          hsp_dl⟩
      rw [hpure_dl, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    · intro s_after hcrl2 hpc2 hrun2 hsp2 hcsp2
      let _ := hcrl2
      dsimp only [deallocVecBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
      have hsp_af : s_after.sp = s0.sp - 432#64 := hsp2.trans hsp_dl
      have hal_af : s_after.spAligned = true := sp_sub_432_spAligned hal0 hsp_af
      let _ := hal_af
      have htr_af : s_after.trace = s0.trace := by
        rw [htr2]; simp only [s_dl, arm64_norm, htr]
      have hx19_af : s_after.readReg64 .x19 = x.fut :=
        hcsp2.1.trans (by simp only [s_dl, arm64_norm, hx19])
      have hx20_af : s_after.readReg64 .x20 = x.out :=
        hcsp2.2.1.trans (by simp only [s_dl, arm64_norm, hx20])
      have hvregs_af : calleeSavedVRegs s_after = calleeSavedVRegs s0 :=
        hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans
          (by simp only [s_dl, calleeSavedVRegs, arm64_norm]; exact hvregs)
      apply SepWPp.of_sepWP (mid := (blkPl_576).base + 500#64)
      wp_steps
      apply bind_sepWP_state; intro s_end
      apply SepWP.done (by simp only [s_end, arm64_norm, *]) (by simp only [s_end, arm64_norm, *])
      refine SepWPp.weaken_pre ?_
        (step_epilogue_write_ret_placed x sc
          0xFFFFFFFFFFFFFFFF#64 0x800000000000000F#64
          (s_end.readReg64 .x26) (s_end.readReg64 .x27) (s_end.readReg64 .x28)
          u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 .missing emp hal0
          (by simp only [s_end, arm64_norm])
          (by simp only [s_end, arm64_norm, *])
          (by simp only [s_end, arm64_norm, hsp_af])
          (by simp only [s_end, calleeSavedVRegs, arm64_norm] at hvregs_af ⊢; exact hvregs_af)
          (by simp only [s_end, arm64_norm, hx19_af])
          (by simp only [s_end, arm64_norm, hx20_af])
          (by simp only [s_end, arm64_norm])
          (by simp only [s_end, arm64_norm])
          rfl rfl rfl
          ⟨hans_eq, by simp only [s_end, arm64_norm, htr_af]⟩
          (by rw [sepConj_emp]; exact words11At_missing_entails A x.out _ _ _ _ _ _ _ _ _))
      rw [emp_sepConj]
      exact Entails.of_eq (by ac_rfl)

theorem step_missing_path_ret_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_hook : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (x : KpkPollGhost) {s0 s : State}
    (sc : KpkScratch) (nPtr bCap bPtr : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (hal0 : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_576).base + 572#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx1 : s.readReg64 .x1 = bCap)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = nPtr)
    (hx22 : s.readReg64 .x22 = bPtr)
    (hans_eq : .missing = kpkAnsOf
      (pkAnsOf KyberPreKeyRecord.deserialize (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
      (pkAnsOf KyberPreKeyRecord.deserialize (x.kg.lastResort.get rd s0.fs.files (keyName x.id)))) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (SpqrV1.Alloc.vecU8Buf A bCap bPtr [] ∗
        SpqrV1.Alloc.vecU8Buf A sc.dec0 nPtr (keyName x.id) ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost rd pathOk A calleeStk x s0)
      (KpkPanicAllow s0) := by
  let sc1 : KpkScratch :=
    { sc with
      sp40_0 := sc.sp70_0, sp40_1 := sc.sp70_1,
      sp40_2 := sc.sp70_2, sp40_3 := sc.sp70_3,
      sp40_4 := sc.sp70_4, sp40_5 := sc.sp70_5,
      fp90_0 := sc.sp70_0, fp90_1 := sc.sp70_1,
      fp90_2 := sc.sp70_2, fp90_3 := sc.sp70_3,
      fp90_4 := sc.sp70_4, fp90_5 := sc.sp70_5 }
  have sameSlots :
      slot7At s0.sp sc1 = slot7At s0.sp sc ∧
      slotSp70At s0.sp sc1 = slotSp70At s0.sp sc ∧
      slotDecAt s0.sp sc1 = slotDecAt s0.sp sc ∧
      slotRetHeadAt s0.sp sc1 = slotRetHeadAt s0.sp sc ∧
      slotRetTailAt s0.sp sc1 = slotRetTailAt s0.sp sc :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  by_cases hbCap : bCap = 0#64
  · subst hbCap
    have hdrop : SpqrV1.Alloc.vecU8Buf A 0#64 bPtr [] ⊢ emp :=
      vecU8Buf_zero_entails_emp A bPtr []
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left hdrop) (Entails.of_eq (emp_sepConj _))) ?_
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_576).base + 628#64) hcrl
    dsimp only [lsProg_576, kpkScratchAt, slot7At, slotSp40At, slotSp70At, slotFp90At]
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s1
    refine SepWPp.weaken_pre ?_
      (step_missing_free_name_ret_placed hC hFs hle_hook hhi x sc1 nPtr
        u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 hal0 hcrl1
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, htr])
        (by simp only [s1, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs)
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        hans_eq)
    dsimp only [kpkScratchAt]
    rw [sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2.1, sameSlots.2.2.2.2]
    dsimp only [slot7At, slotSp40At, slotSp70At, slotFp90At, sc1]
    exact Entails.of_eq (by ac_rfl)
  · have hb_beq : (bCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbCap
    have hb_bne : (bCap != 0#64) = true := bne_iff_ne.mpr hbCap
    have _ := And.intro hb_beq hb_bne
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply StoreKit.sepWPp_seq_lscro (mid := (lsρ lsRustDeallocSymCli)) hcrl
    dsimp only [lsProg_576, kpkScratchAt, slot7At, slotSp40At, slotSp70At, slotFp90At]
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_dl
    have hsp_dl : s_dl.sp = s0.sp - 432#64 := by simp only [s_dl, arm64_norm, hsp]
    have hal_dl : s_dl.spAligned = true := sp_sub_432_spAligned hal0 hsp_dl
    have hdealloc := deallocVecBuf_cells_placed_ok (F0 := s_dl.fs.files) (T0 := s_dl.trace)
      hC hFs hle_hook hhi
    refine kpk_call_lscro (bCap, bPtr, [], s0.sp - 432#64) hdealloc hcrl1
      (by simp only [s_dl, wp_norm, arm64_norm])
      (by simp only [s_dl, arm64_norm, *])
      hal_dl
      (ret_pc := (blkPl_576).base + 628#64)
      (by simp only [s_dl, arm64_norm])
      (F := SpqrV1.Alloc.vecU8Buf A sc.dec0 nPtr (keyName x.id) ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc1 ∗ kpkSavedRegs s0)
      ?_ (hnext := ?_)
    · dsimp only [deallocVecBufCellsSpec, kpkScratchAt]
      rw [sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2.1, sameSlots.2.2.2.2]
      dsimp only [slot7At, slotSp40At, slotSp70At, slotFp90At, sc1]
      have hpure_dl :
          (FsInv s_dl.fs.files s_dl.trace s_dl ∧ bCap ≠ 0#64 ∧
            s_dl.readReg64 .x0 = bPtr ∧ s_dl.readReg64 .x1 = bCap ∧
            s_dl.readReg64 .x2 = 1#64 ∧ s_dl.sp = s0.sp - 432#64) = True :=
        eq_true ⟨withFsInv_entry s_dl, hbCap,
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm],
          hsp_dl⟩
      rw [hpure_dl, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    · intro s_after hcrl2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [deallocVecBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
      have htr_tot : s_after.trace = s0.trace := by
        rw [htr2]; simp only [s_dl, arm64_norm, htr]
      refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
        (step_missing_free_name_ret_placed hC hFs hle_hook hhi x sc1 nPtr
          u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 hal0 hcrl2 hpc2 hrun2
          (hsp2.trans hsp_dl) htr_tot
          (hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [s_dl, calleeSavedVRegs, arm64_norm]; exact hvregs))
          (hcsp2.1.trans (by simp only [s_dl, arm64_norm, hx19]))
          (hcsp2.2.1.trans (by simp only [s_dl, arm64_norm, hx20]))
          (hcsp2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx21]))
          hans_eq)

theorem step_last_resort_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {decStk getStk calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hDecimal : subroutine_ok (lsProg_576 H) (lsmpl.base 597)
      (decimalSpecPlaced A decStk))
    (hGet : subroutine_ok (lsProg_576 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A getStk))
    (hDec : subroutine_ok (lsProg_576 H) (lsmpl.base 595)
      (decodeKyberPreKeyPlacedSpec A))
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_dec : decStk ≤ calleeStk)
    (hle_get : getStk ≤ calleeStk)
    (hle_root : smallRootStack ≤ calleeStk)
    (hle_hook : extHookStack ≤ calleeStk)
    (hhi : calleeStk ≤ 2 ^ 64)
    (x : KpkPollGhost) {s0 s : State}
    (sc : KpkScratch)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (hn2 : PkNameOk pathOk x.kg.lastResort x.id)
    (hs2 : PkSizeOk rd s0.fs.files x.kg.lastResort x.id)
    (hmiss1 : pkAnsOf KyberPreKeyRecord.deserialize
      (x.kg.oneTime.get rd s0.fs.files (keyName x.id)) = .missing)
    (hal0 : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsInv s0.fs.files s0.trace s)
    (hpc : s.pc = (blkPl_576).base + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx25 : s.readReg64 .x25 = x.id.zeroExtend 64) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost rd pathOk A calleeStk x s0)
      (KpkPanicAllow s0) := by
  have hDecCells := decimal_cells_placed_ok (F0 := s0.fs.files) (T0 := s0.trace)
    hDecimal hFs hle_dec hhi
  have hGetCells := dirGet_cells_placed_ok (F0 := s0.fs.files) (T0 := s0.trace)
    hGet hFs hle_get hhi
  have hDecodeCells := decode_cells_placed_ok (F0 := s0.fs.files) (T0 := s0.trace)
    hDec hFs hle_root hhi
  clear hDecimal hGet hDec
  have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
  let _ := hal
  -- `+288 .. +296`: `decimal(sp + 0xa8, id)`
  apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 597) hcrl
  dsimp only [lsProg_576]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcrl1
  apply bind_sepWPp_state; intro s_dec
  have hsp_dec : s_dec.sp = s0.sp - 432#64 := by simp only [s_dec, arm64_norm, hsp]
  have hal_dec : s_dec.spAligned = true := sp_sub_432_spAligned hal0 hsp_dec
  have htr_dec : s_dec.trace = s0.trace := by simp only [s_dec, arm64_norm, htr]
  have hfs_dec : FsInv s0.fs.files s0.trace s_dec :=
    fsInv_of_eq hfs (by simp only [s_dec, arm64_norm]) (by simp only [s_dec, arm64_norm])
  refine kpk_call_lscro
    (x.id, s0.sp - 264#64, sc.dec0, sc.dec1, sc.dec2, s0.sp - 432#64)
    hDecCells hcrl1
    (by simp only [s_dec, arm64_norm])
    (by simp only [s_dec, arm64_norm, *])
    hal_dec
    (ret_pc := (blkPl_576).base + 300#64)
    (by simp only [s_dec, arm64_norm])
    (F := words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
      dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      kpkSlack3 s0.sp ∗
      (slot7At s0.sp sc ∗ slotSp40At s0.sp sc ∗ slotSp70At s0.sp sc ∗
       slotFp90At s0.sp sc ∗ slotRetHeadAt s0.sp sc ∗ slotRetTailAt s0.sp sc) ∗
      kpkSavedRegs s0)
    ?_
    (hpanic := fun _ _ _ hp => kpk_panic_of_trace htr_dec hp)
    (hnext := ?_)
  · dsimp only [decimalFsCellsSpec, kpkScratchAt, slotDecAt]
    rw [dec_off8, dec_off16]
    have hpure :
        (FsInv s0.fs.files s0.trace s_dec ∧
          s_dec.readReg64 .x0 = s0.sp - 264#64 ∧
          s_dec.readReg32 .x1 = x.id ∧
          s_dec.sp = s0.sp - 432#64) = True :=
      eq_true ⟨hfs_dec,
        by simp only [s_dec, arm64_norm],
        by simp only [s_dec, arm64_norm],
        hsp_dec⟩
    rw [hpure, ProofLib.pure_true, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)
  · intro s_ad hcrl2 hpc2 hrun2 hsp2 hcsp2
    dsimp only [decimalFsCellsSpec]
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nCap => SepWPp.exists_elim fun nPtr => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hfs2, htr2⟩ => ?_
    have hsp_ad : s_ad.sp = s0.sp - 432#64 := hsp2.trans hsp_dec
    have hal_ad : s_ad.spAligned = true := sp_sub_432_spAligned hal0 hsp_ad
    let _ := hal_ad
    have htr_ad : s_ad.trace = s0.trace := htr2.trans htr_dec
    have hx19_ad : s_ad.readReg64 .x19 = x.fut :=
      hcsp2.1.trans (by simp only [s_dec, arm64_norm, hx19])
    have hx20_ad : s_ad.readReg64 .x20 = x.out :=
      hcsp2.2.1.trans (by simp only [s_dec, arm64_norm, hx20])
    have hx24_ad : s_ad.readReg64 .x24 = x.self :=
      hcsp2.2.2.2.2.2.1.trans (by simp only [s_dec, arm64_norm, hx24])
    have hx29_ad : s_ad.readReg64 .x29 = s0.sp - 96#64 :=
      hcsp2.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dec, arm64_norm, hx29])
    have hvregs_ad : calleeSavedVRegs s_ad = calleeSavedVRegs s0 :=
      hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans
        (by simp only [s_dec, calleeSavedVRegs, arm64_norm]; exact hvregs)
    let _ := And.intro hx24_ad hx29_ad
    -- `+300 .. +316`: `Dir::get(x29 - 0x60, self + 0x28, nPtr, nLen)`
    rw [dec_off8, dec_off16]
    apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 589) hcrl2
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl3
    apply bind_sepWPp_state; intro s_get
    have hsp_get : s_get.sp = s0.sp - 432#64 := by simp only [s_get, arm64_norm, hsp_ad]
    have hal_get : s_get.spAligned = true := sp_sub_432_spAligned hal0 hsp_get
    have htr_get : s_get.trace = s0.trace := by simp only [s_get, arm64_norm, htr_ad]
    have hfs_get : FsInv s0.fs.files s0.trace s_get :=
      fsInv_of_eq hfs2 (by simp only [s_get, arm64_norm]) (by simp only [s_get, arm64_norm])
    refine kpk_call_lscro
      (s0.sp - 192#64, x.self + 0x28#64, x.kg.lastResort, x.id, nCap, nPtr,
        sc.ret0, sc.ret1, sc.ret2, sc.ret3, sc.ret4, sc.ret5, s0.sp - 432#64)
      hGetCells hcrl3
      (by simp only [s_get, arm64_norm])
      (by simp only [s_get, arm64_norm, *])
      hal_get
      (ret_pc := (blkPl_576).base + 320#64)
      (by simp only [s_get, arm64_norm])
      (F := words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A x.self x.kg.oneTime ∗
        kpkSlack3 s0.sp ∗
        (slot7At s0.sp sc ∗ slotSp40At s0.sp sc ∗ slotSp70At s0.sp sc ∗
         ((s0.sp - 264#64) ↦₆₄ nCap) ∗ ((s0.sp - 256#64) ↦₆₄ nPtr) ∗
         ((s0.sp - 248#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
         slotFp90At s0.sp sc ∗ slotRetTailAt s0.sp sc) ∗
        kpkSavedRegs s0)
      ?_
      (hpanic := fun _ _ _ hp => kpk_panic_of_trace htr_get hp)
      (hnext := ?_)
    · dsimp only [dirGetFsCellsSpec, slotRetHeadAt]
      rw [words6At_retSlot]
      have hpure :
          (FsInv s0.fs.files s0.trace s_get ∧ s_get.trace = s0.trace ∧
            PkNameOk pathOk x.kg.lastResort x.id ∧
            s_get.readReg64 .x0 = s0.sp - 192#64 ∧
            s_get.readReg64 .x1 = x.self + 0x28#64 ∧
            s_get.readReg64 .x2 = nPtr ∧
            s_get.readReg64 .x3 = BitVec.ofNat 64 (keyName x.id).length ∧
            s_get.sp = s0.sp - 432#64) = True :=
        eq_true ⟨hfs_get, htr_get, hn2,
          by simp only [s_get, arm64_norm],
          by simp only [s_get, arm64_norm, *],
          by simp only [s_get, arm64_norm],
          by simp only [s_get, arm64_norm],
          hsp_get⟩
      rw [hpure, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    · intro s_ag hcrl4 hpc4 hrun4 hsp4 hcsp4
      dsimp only [dirGetFsCellsSpec]
      simp only [sepExists_sepConj_left]
      refine SepWPp.exists_elim fun r =>
        SepWPp.exists_elim fun w0 => SepWPp.exists_elim fun w1 =>
        SepWPp.exists_elim fun w2 => SepWPp.exists_elim fun w3 =>
        SepWPp.exists_elim fun w4 => SepWPp.exists_elim fun w5 =>
        SepWPp.exists_elim fun H_post => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hprop => ?_
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
      · -- `Dir::get` returned `.error ()`
        rcases hprop with ⟨hw0, hr_disj, hread_ent⟩
        subst hw0
        apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_576).base + 412#64) hcrl4
        wp_steps
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
          rw [hmiss1, hget_e]; rfl
        refine SepWPp.weaken_pre ?_
          (step_dir_err_ret_placed hC hFs hle_hook hhi x sc_ag nPtr
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
            hans_err hread_ent)
        dsimp only [kpkScratchAt]
        rw [sameAg.1, sameAg.2.1, sameAg.2.2.1, sameAg.2.2.2.1, sameAg.2.2.2.2]
        dsimp only [slotDecAt, slotRetHeadAt, sc_ag]
        exact Entails.of_eq (by ac_rfl)
      · -- `Dir::get` returned `.ok []` -> `missing` path (`+572`)
        rcases hprop with ⟨hget_empty, _hfs_ag, htr_ag, hw0, hw3, hH⟩
        subst hw0 hw3 hH
        apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_576).base + 572#64) hcrl4
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcrl5
        apply bind_sepWPp_state; intro s_m
        have hans_miss : .missing = kpkAnsOf
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) := by
          rw [hmiss1, hget_empty]; rfl
        refine SepWPp.weaken_pre ?_
          (step_missing_path_ret_placed hC hFs hle_hook hhi x sc_ag nPtr w1 w2
            u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 hal0 hcrl5
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
            hans_miss)
        dsimp only [kpkScratchAt]
        rw [sameAg.1, sameAg.2.1, sameAg.2.2.1, sameAg.2.2.2.1, sameAg.2.2.2.2]
        dsimp only [slotDecAt, slotRetHeadAt, sc_ag]
        exact Entails.of_eq (by ac_rfl)
      · -- `Dir::get` returned `.ok (b0 :: bs)` -> `decode_kyber_pre_key` (`+356`)
        rcases hprop with ⟨hget_ne, hfs_ag, htr_ag, hw0, hw3, hH⟩
        subst hw0 hw3 hH
        have hlen_pos : 0 < (b0 :: bs).length := List.length_pos_of_ne_nil (by simp)
        have hlen_lt : (b0 :: bs).length < 2 ^ 32 := hs2 (b0 :: bs) hget_ne
        have hlen_ne : BitVec.ofNat 64 (b0 :: bs).length ≠ 0#64 :=
          ofNat_len_ne_zero hlen_pos hlen_lt
        have hlen_beq : (BitVec.ofNat 64 (b0 :: bs).length == 0#64) = false :=
          beq_eq_false_iff_ne.mpr hlen_ne
        have hlen_bne : (BitVec.ofNat 64 (b0 :: bs).length != 0#64) = true :=
          bne_iff_ne.mpr hlen_ne
        have _ := And.intro hlen_beq hlen_bne
        apply StoreKit.sepWPp_seq_lscro (mid := lsmpl.base 595) hcrl4
        dsimp only [lsProg_576, slot7At]
        wp_steps
        apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        intro hcrl5
        apply bind_sepWPp_state; intro s_dk
        have hsp_dk : s_dk.sp = s0.sp - 432#64 := by simp only [s_dk, arm64_norm, hsp_ag]
        have hal_dk : s_dk.spAligned = true := sp_sub_432_spAligned hal0 hsp_dk
        have htr_dk : s_dk.trace = s0.trace := by simp only [s_dk, arm64_norm, htr_ag]
        have hfs_dk : FsInv s0.fs.files s0.trace s_dk :=
          fsInv_of_eq hfs_ag (by simp only [s_dk, arm64_norm]) (by simp only [s_dk, arm64_norm])
        refine kpk_call_lscro
          (s0.sp - 192#64, w1, w2, b0 :: bs,
            0xFFFFFFFFFFFFFFFE#64, w1, w2, BitVec.ofNat 64 (b0 :: bs).length, w4, w5,
            sc.ret6, sc.ret7, sc.ret8, sc.ret9, sc.ret10, s0.sp - 432#64)
          hDecodeCells hcrl5
          (by simp only [s_dk, arm64_norm])
          (by simp only [s_dk, arm64_norm, *])
          hal_dk
          (ret_pc := (blkPl_576).base + 360#64)
          (by simp only [s_dk, arm64_norm])
          (F := SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName x.id) ∗
            words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
            (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
            dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
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
          ?_
          (hpanic := fun _ _ _ hp => kpk_panic_of_trace htr_dk hp)
          (hnext := ?_)
        · dsimp only [decodeFsCellsSpec, slotRetTailAt]
          rw [words11At_retSlot]
          have hpure :
              (FsInv s0.fs.files s0.trace s_dk ∧ s_dk.trace = s0.trace ∧
                0 < (b0 :: bs).length ∧ (b0 :: bs).length < 2 ^ 32 ∧
                s_dk.readReg64 .x0 = s0.sp - 192#64 ∧
                s_dk.readReg64 .x1 = w2 ∧
                s_dk.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs).length ∧
                s_dk.sp = s0.sp - 432#64) = True :=
            eq_true ⟨hfs_dk, htr_dk, hlen_pos, hlen_lt,
              by simp only [s_dk, arm64_norm],
              by simp only [s_dk, arm64_norm],
              by simp only [s_dk, arm64_norm],
              hsp_dk⟩
          rw [hpure, ProofLib.pure_true, emp_sepConj]
          exact Entails.of_eq (by ac_rfl)
        · intro s_adk hcrl6 hpc6 hrun6 hsp6 hcsp6
          dsimp only [decodeFsCellsSpec]
          simp only [sepExists_sepConj_left]
          refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
            SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
            SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 =>
            SepWPp.exists_elim fun d6 => SepWPp.exists_elim fun d7 =>
            SepWPp.exists_elim fun d8 => SepWPp.exists_elim fun d9 =>
            SepWPp.exists_elim fun d10 => SepWPp.exists_elim fun Hdec => ?_
          rw [sepConj_assoc]
          refine SepWPp.pure_elim fun hdprop => ?_
          rw [words11At_retSlot]
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
          have hx29_adk : s_adk.readReg64 .x29 = s0.sp - 96#64 :=
            hcsp6.2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dk, arm64_norm, hx29_ag])
          have hvregs_adk : calleeSavedVRegs s_adk = calleeSavedVRegs s0 :=
            hcsp6.2.2.2.2.2.2.2.2.2.2.2.trans
              (by simp only [s_dk, calleeSavedVRegs, arm64_norm]; exact hvregs_ag)
          let _ := And.intro hx22_adk hx29_adk
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
            apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_576).base + 440#64) hcrl6
            wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            intro hcrl7
            apply bind_sepWPp_state; intro s_de
            have hans_de : .decodeErr e = kpkAnsOf
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) := by
              rw [hmiss1, hget_ne]; simp [pkAnsOf, hdes, kpkAnsOf]
            refine SepWPp.weaken_pre ?_
              (step_dec_err_ret_placed hC hFs hle_hook hhi x sc_de nPtr w2 (b0 :: bs)
                u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 e Hdec hal0 hcrl7
                (by simp only [s_de, arm64_norm])
                (by simp only [s_de, arm64_norm, *])
                (by simp only [s_de, arm64_norm, hsp_adk])
                (by simp only [s_de, arm64_norm, htr_adk])
                (by simp only [s_de, calleeSavedVRegs, arm64_norm] at hvregs_adk ⊢; exact hvregs_adk)
                (by simp only [s_de, arm64_norm, hx29_adk])
                (by simp only [s_de, arm64_norm])
                (by simp only [s_de, arm64_norm])
                (by simp only [s_de, arm64_norm, hx19_adk])
                (by simp only [s_de, arm64_norm, hx20_adk])
                (by simp only [s_de, arm64_norm, hx21_adk])
                hans_de hdec_ent)
            dsimp only [kpkScratchAt]
            rw [sameDe.1, sameDe.2.1, sameDe.2.2]
            dsimp only [slot7At, slotDecAt, slotRetHeadAt, slotRetTailAt, sc_de]
            exact Entails.of_eq (by ac_rfl)
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
            apply StoreKit.sepWPp_seq_lscro (mid := (blkPl_576).base + 216#64) hcrl6
            dsimp only [lsProg_576, slotSp40At, slotSp70At, slotFp90At]
            wp_steps
            apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            intro hcrl7
            apply bind_sepWPp_state; intro s_ok
            have hans_ok : .found rec = kpkAnsOf
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) := by
              rw [hmiss1, hget_ne]; simp [pkAnsOf, hdes, kpkAnsOf]
            refine SepWPp.weaken_pre ?_
              (step_dec_ok_ret_placed hC hFs hle_hook hhi x sc_ok nPtr w1 w2 (b0 :: bs)
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
                hans_ok (hfound_ent x.out))
            dsimp only [kpkScratchAt, slot7At, slotSp40At, slotSp70At, slotDecAt,
              slotFp90At, slotRetHeadAt, slotRetTailAt, sc_ok]
            exact Entails.of_eq (by ac_rfl)

end Placed

end CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
