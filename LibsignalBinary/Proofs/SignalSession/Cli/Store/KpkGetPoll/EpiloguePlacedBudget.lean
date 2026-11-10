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
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.EpiloguePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Epilogue & Exit Blocks for `get_kyber_pre_key::{closure#0}`

Proves budget-threaded shared exit and epilogue continuations on Block `576` (`lsProg_576 H`)
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.EpiloguePlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsInv LibsignalCodeRoLoaded TraceFsSound sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (KyberPreKeyRecord)
open CryptoVerification.SpqrV1.Alloc (vecU8Buf)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost KpkPollGhost PkAns ReadRule dirAt keyName kpkAnsAt kpkAnsOf pkAnsOf withFsInv_entry)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_576 blkPC_576 blkPl_576 lsProg_576)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (satisfies_lscro_pre)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
  (KpkScratch bind_sepWP_state bind_sepWPp_state kpkFrame_entails_cells54 kpkSavedRegs
   kpkScratchAt kpkSlack3 slot7At slotDecAt slotFp90At slotRetHeadAt slotRetTailAt slotSp40At
   slotSp70At sp_sub_432_spAligned vecU8Buf_zero_entails_emp words11At)
open CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers.CliKpkGetPollNorm
  (extractLsb_append_hi extractLsb_append_lo readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   readVReg128_setMem_pre readVReg128_setMem_setPC_pre readVReg128_setPC_pre
   readVReg128_setPState_pre readVReg128_writeReg64_pre sp_setMem_setPC_pre sp_setPC_pre
   zext32_trunc32)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr
  (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (AllocContractsXCliPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
  (CliKpkGetPollEnv cliKpkGetPollInnerSpec deallocVecBufCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutPlacedBudget
  (deallocVecBuf_cells_placed_ok)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
  readVReg128_setPC_pre readVReg128_setMem_setPC_pre readVReg128_setMem_pre
  readVReg128_setPState_pre readVReg128_writeReg64_pre
  extractLsb_append_lo extractLsb_append_hi zext32_trunc32

abbrev KpkExitPost {M : AllocCostModel} (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (DecEnv : BitVec 32 → List AllocEvent → Prop)
    (GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop)
    (DecodeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (calleeStk : Nat) (x : KpkPollGhost) (st0 : M.σ) (s0 : State) :
    State → SepProp → Prop :=
  fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ (cliKpkGetPollInnerSpec rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk).post
      (x, st0) s0 sf)

/-- Call a total (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, `onOom = ⌜False⌝`) spec wrapped in
`withLsCodeRoLoaded lsmpl`, preserving `LibsignalCodeRoLoaded lsmpl` in a `SepWPp` continuation
for any panic predicate `Qp`. -/
theorem kpk_call_total_lscro [LibsignalPlacement] {prog : Program} {ret : BitVec 64}
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    {α : Type} {callee_pc ret_pc : BitVec 64} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog callee_pc (withLsCodeRoLoaded lsmpl spec))
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee_pc)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hP : P ⊢ spec.pre x s ∗ F)
    (hexit : ∀ sf code R', ¬ (sf.mem ⊨ spec.onExit x code s sf ∗ R') := by
      intro _ _ _ he; exact not_satisfies_false_sepConj he)
    (hoom : ∀ sf R', ¬ (sf.mem ⊨ spec.onOom x s sf ∗ R') := by
      intro _ _ ho; exact not_satisfies_false_sepConj ho)
    (hpanic : ∀ sf R', ¬ (sf.mem ⊨ spec.onPanic x s sf ∗ R') := by
      intro _ _ hp; exact not_satisfies_false_sepConj hp)
    (hnext : ∀ sf : State,
      LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine sepWPp_seq_lscro (mid := ret_pc) hcrl ?_
  refine ProofLib.SepWP.call_subroutine_frame (x := x) (F := F) hcall hpc hrun hsp hlr
    (fun R hm => ?_)
    (fun R' sm _ hp => ?_)
    (fun R' code sm _ he => ?_)
    (fun sm hpcm hrunm hspm hcsm =>
      ProofLib.SepWP.done hpcm hrunm (fun hcrlm => ?_))
    (fun R' sm _ ho => ?_)
  · have hm_pre : s.mem ⊨ (spec.pre x s ∗ F) ∗ R :=
      Satisfies.mono (sepConj_mono_left hP) hm
    exact satisfies_lscro_pre hcrl (by simpa only [sepConj_assoc] using hm_pre)
  · dsimp only [withLsCodeRoLoaded] at hp
    exact hpanic sm R' hp
  · dsimp only [withLsCodeRoLoaded] at he
    exact hexit sm code R' he
  · dsimp only [withLsCodeRoLoaded]
    exact hnext sm hcrlm hpcm hrunm hspm hcsm
  · dsimp only [withLsCodeRoLoaded] at ho
    exact (hoom sm (F ∗ R') ho).elim

theorem step_epilogue_write_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} (x : KpkPollGhost) (st0 : M.σ) (evs : List AllocEvent)
    {s0 s : State}
    (sc : KpkScratch)
    (out0 out1 out2 out3 out4 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (ans : PkAns KyberPreKeyRecord) (Hp : SepProp)
    (hal0 : s0.spAligned = true)
    (hpc : s.pc = (blkPl_576).base + 500#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx23 : s.readReg64 .x23 = out0)
    (hx22 : s.readReg64 .x22 = out1)
    (hx26 : s.readReg64 .x26 = out2)
    (hx27 : s.readReg64 .x27 = out3)
    (hx28 : s.readReg64 .x28 = out4)
    (hans_prop :
      ans = kpkAnsOf
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
          s.trace = s0.trace)
    (hevs : CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x evs)
    (hans_ent :
      words11At x.out out0 out1 out2 out3 out4
        sc.sp10_4 sc.sp10_5 sc.sp10_0 sc.sp10_1 sc.sp10_2 sc.sp10_3 ∗ Hp ⊢
        kpkAnsAt A.repAlloc x.out ans) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (Hp ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim (M.stepEvents evs st0) s ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x st0 s0)
      Qp := by
  have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
  let _ := hal
  dsimp only [words11At, kpkScratchAt, slot7At, kpkSavedRegs]
  apply SepWPp.of_sepWP_ret
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  apply bind_sepWP_state; intro sf
  apply SepWP.done (by simp only [sf, arm64_norm, *]) (by simp only [sf, arm64_norm, *])
  refine ⟨by simp only [sf, arm64_norm, *], ?_, ?_⟩
  · refine ⟨by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, arm64_norm, *],
      by simp only [sf, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs⟩
  · have htrf : sf.trace = s.trace := by simp only [sf, arm64_norm]
    have hans_sf :
        ans = kpkAnsOf
              (pkAnsOf KyberPreKeyRecord.deserialize
                (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
              (pkAnsOf KyberPreKeyRecord.deserialize
                (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
            sf.trace = s0.trace ∧
            CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x evs :=
      ⟨hans_prop.1, htrf.trans hans_prop.2, hevs⟩
    have hpack54 := kpkFrame_entails_cells54 s0 sc
    dsimp only [cliKpkGetPollInnerSpec]
    refine Entails.trans ?_ (Entails.sepExists_right evs (Entails.refl _))
    refine Entails.trans ?_
      (sepConj_mono
        (Entails.trans hans_ent
          (Entails.trans
            (Entails.of_eq (emp_sepConj _).symm)
            (Entails.sepExists_right ans
              (sepConj_mono_left
                (by rw [eq_true hans_sf, ProofLib.pure_true]; exact Entails.refl _)))))
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right hpack54))))))))
    dsimp only [words11At, kpkScratchAt, slot7At, kpkSavedRegs]
    exact Entails.of_eq (by sep_ac_rfl)

theorem step_free_name_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_hook : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (x : KpkPollGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    {s0 s : State}
    (sc : KpkScratch) (nPtr : BitVec 64)
    (out0 out1 out2 out3 out4 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (ans : PkAns KyberPreKeyRecord) (Hp : SepProp)
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_576).base + 480#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = nPtr)
    (hx23 : s.readReg64 .x23 = out0)
    (hx22 : s.readReg64 .x22 = out1)
    (hx26 : s.readReg64 .x26 = out2)
    (hx27 : s.readReg64 .x27 = out3)
    (hx28 : s.readReg64 .x28 = out4)
    (hans_prop :
      ans = kpkAnsOf
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
          s.trace = s0.trace)
    (hevs_free : ∀ evsF, FreeOnlyEvs evsF →
      CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x (evsPre ++ evsF))
    (hans_ent :
      words11At x.out out0 out1 out2 out3 out4
        sc.sp10_4 sc.sp10_5 sc.sp10_0 sc.sp10_1 sc.sp10_2 sc.sp10_3 ∗ Hp ⊢
        kpkAnsAt A.repAlloc x.out ans) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ∗
        Hp ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim (M.stepEvents evsPre st0) s ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x st0 s0)
      Qp := by
  by_cases hnCap : sc.dec0 = 0#64
  · have hdrop : vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ⊢ emp := by
      rw [hnCap]; exact vecU8Buf_zero_entails_emp A.repAlloc nPtr (keyName x.id)
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left hdrop) (Entails.of_eq (emp_sepConj _))) ?_
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply SepWPp.of_sepWP (mid := (blkPl_576).base + 500#64)
    dsimp only [kpkScratchAt, slotDecAt]
    rw [hnCap]
    wp_steps_sync_pool ((blkPl_576).base + 500#64)
    apply bind_sepWP_state; intro s1
    apply SepWP.done (by simp only [s1, arm64_norm, *]) (by simp only [s1, arm64_norm, *])
    refine SepWPp.weaken_pre ?_
      (step_epilogue_write_ret_placed x st0 evsPre sc out0 out1 out2 out3 out4
        u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ans Hp hal0
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs)
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        ⟨hans_prop.1, by simp only [s1, arm64_norm]; exact hans_prop.2⟩
        (by simpa using hevs_free [] FreeOnlyEvs.nil)
        hans_ent)
    dsimp only [kpkScratchAt, slotDecAt]
    rw [hnCap]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hn_beq : (sc.dec0 == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hn_bne : (sc.dec0 != 0#64) = true := bne_iff_ne.mpr hnCap
    have _ := And.intro hn_beq hn_bne
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    dsimp only [kpkScratchAt, slotDecAt]
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_dl
    have hsp_dl : s_dl.sp = s0.sp - 432#64 := by simp only [s_dl, arm64_norm, hsp]
    have hal_dl : s_dl.spAligned = true := sp_sub_432_spAligned hal0 hsp_dl
    have htr_dl : s_dl.trace = s.trace := by simp only [s_dl, arm64_norm]
    have hdealloc := deallocVecBuf_cells_placed_ok (F0 := s_dl.fs.files) (T0 := s_dl.trace)
      hC hFs hle_hook hhi
    refine kpk_call_total_lscro
      ((sc.dec0, nPtr, keyName x.id, s0.sp - 432#64), M.stepEvents evsPre st0)
      hdealloc hcrl1
      (by simp only [s_dl, wp_norm, arm64_norm]; try bv_omega)
      (by simp only [s_dl, arm64_norm, *])
      hal_dl
      (ret_pc := (blkPl_576).base + 500#64)
      (by simp only [s_dl, wp_norm, arm64_norm])
      (F := Hp ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      ?_ (hnext := ?_)
    · dsimp only [deallocVecBufCellsSpec, kpkScratchAt, slotDecAt]
      have hpure_dl :
          (FsInv s_dl.fs.files s_dl.trace s_dl ∧ sc.dec0 ≠ 0#64 ∧
            s_dl.readReg64 .x0 = nPtr ∧ s_dl.readReg64 .x1 = sc.dec0 ∧
            s_dl.readReg64 .x2 = 1#64 ∧ s_dl.sp = s0.sp - 432#64 ∧
            LsRetAddr624 (s_dl.readReg64 .lr)) = True :=
        eq_true ⟨withFsInv_entry s_dl, hnCap,
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm],
          hsp_dl,
          by rw [show s_dl.readReg64 .lr = (blkPl_576).base + 500#64 by
               simp only [s_dl, wp_norm, arm64_norm]]
             exact lsRetAddr624_blockPlacement_base_add 576 500#64 (by decide) (by decide)⟩
      rw [hpure_dl, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after hcrl2 hpc2 hrun2 hsp2 hcsp2
      let _ := hcrl2
      dsimp only [deallocVecBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
      rw [← M.stepEvents_append]
      have htr_tot : s_after.trace = s.trace := htr2.trans htr_dl
      have hans_after :
          ans = kpkAnsOf
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
                (pkAnsOf KyberPreKeyRecord.deserialize
                  (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
              s_after.trace = s0.trace :=
        ⟨hans_prop.1, htr_tot.trans hans_prop.2⟩
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (step_epilogue_write_ret_placed x st0 (evsPre ++ rustDeallocEvents sc.dec0.toNat 1)
          sc out0 out1 out2 out3 out4
          u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ans Hp hal0 hpc2 hrun2
          (hsp2.trans hsp_dl)
          (hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [s_dl, calleeSavedVRegs, arm64_norm]; exact hvregs))
          (hcsp2.1.trans (by simp only [s_dl, arm64_norm, hx19]))
          (hcsp2.2.1.trans (by simp only [s_dl, arm64_norm, hx20]))
          (hcsp2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx23]))
          (hcsp2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx22]))
          (hcsp2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx26]))
          (hcsp2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx27]))
          (hcsp2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx28]))
          hans_after
          (hevs_free _ (FreeOnlyEvs.singleton 1 sc.dec0.toNat))
          hans_ent)

theorem step_dir_err_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_hook : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (x : KpkPollGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    {s0 s : State}
    (sc : KpkScratch) (nPtr : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (Hp : SepProp)
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_576).base + 412#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = nPtr)
    (hx22 : s.readReg64 .x22 = 0x8000000000000001#64)
    (hans_prop :
      .readErr = kpkAnsOf
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
          s.trace = s0.trace)
    (hevs_free : ∀ evsF, FreeOnlyEvs evsF →
      CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x (evsPre ++ evsF))
    (hread_ent : ∀ out t7 t8 t9 t10,
      words11At out 0xFFFFFFFFFFFFFFFF#64 0x8000000000000001#64
        sc.ret1 sc.ret2 sc.ret3 sc.ret4 sc.ret5 t7 t8 t9 t10 ∗ Hp ⊢
        kpkAnsAt A.repAlloc out .readErr) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ∗
        Hp ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim (M.stepEvents evsPre st0) s ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x st0 s0)
      Qp := by
  have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
  let _ := hal
  apply sepWPp_seq_lscro (mid := (blkPl_576).base + 480#64) hcrl
  dsimp only [kpkScratchAt, slot7At, slotRetHeadAt]
  wp_steps_sync_pool ((blkPl_576).base + 480#64)
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hcrl1
  apply bind_sepWPp_state; intro s1
  let sc1 : KpkScratch := { sc with sp10_4 := sc.ret4, sp10_5 := sc.ret5 }
  have sameSlots :
      slotSp40At s0.sp sc1 = slotSp40At s0.sp sc ∧
      slotSp70At s0.sp sc1 = slotSp70At s0.sp sc ∧
      slotDecAt s0.sp sc1 = slotDecAt s0.sp sc ∧
      slotFp90At s0.sp sc1 = slotFp90At s0.sp sc ∧
      slotRetHeadAt s0.sp sc1 = slotRetHeadAt s0.sp sc ∧
      slotRetTailAt s0.sp sc1 = slotRetTailAt s0.sp sc :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine SepWPp.weaken_pre ?_
    (step_free_name_ret_placed hC hFs hle_hook hhi x st0 evsPre sc1 nPtr
      0xFFFFFFFFFFFFFFFF#64 0x8000000000000001#64 sc.ret1 sc.ret2 sc.ret3
      u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 .readErr Hp hal0 hcrl1
      (by simp only [s1, arm64_norm])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs)
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, arm64_norm])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, arm64_norm, *])
      (by simp only [s1, arm64_norm, *])
      ⟨hans_prop.1, by simp only [s1, arm64_norm]; exact hans_prop.2⟩
      hevs_free
      (hread_ent x.out sc.sp10_0 sc.sp10_1 sc.sp10_2 sc.sp10_3))
  dsimp only [kpkScratchAt]
  rw [sameSlots.1, sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2.1,
    sameSlots.2.2.2.2.1, sameSlots.2.2.2.2.2]
  dsimp only [slot7At, slotRetHeadAt, sc1]
  exact Entails.of_eq (by sep_ac_rfl)

theorem step_dec_err_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_hook : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (x : KpkPollGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    {s0 s : State}
    (sc : KpkScratch) (nPtr bPtr : BitVec 64) (bs : List (BitVec 8))
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (e : SignalProtocolError) (Hp : SepProp)
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_576).base + 440#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx27 : s.readReg64 .x27 = s0.sp - 192#64)
    (hx0 : s.readReg64 .x0 = bPtr)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = nPtr)
    (hans_eq : .decodeErr e = kpkAnsOf
      (pkAnsOf KyberPreKeyRecord.deserialize (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
      (pkAnsOf KyberPreKeyRecord.deserialize (x.kg.lastResort.get rd s0.fs.files (keyName x.id))))
    (hevs_free : ∀ evsF, FreeOnlyEvs evsF →
      CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x (evsPre ++ evsF))
    (hdec_ent : ∀ out t7 t8 t9 t10,
      words11At out 0xFFFFFFFFFFFFFFFF#64
        sc.ret1 sc.ret2 sc.ret3 sc.ret4 sc.ret5 sc.ret6 t7 t8 t9 t10 ∗ Hp ⊢
        kpkAnsAt A.repAlloc out (.decodeErr e)) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (vecU8Buf A.repAlloc sc.sp08 bPtr bs ∗
        vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ∗
        Hp ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim (M.stepEvents evsPre st0) s ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x st0 s0)
      Qp := by
  let sc1 : KpkScratch :=
    { sc with sp40_4 := sc.ret5, sp40_5 := sc.ret6, sp10_4 := sc.ret5, sp10_5 := sc.ret6 }
  have sameSlots :
      slotSp70At s0.sp sc1 = slotSp70At s0.sp sc ∧
      slotDecAt s0.sp sc1 = slotDecAt s0.sp sc ∧
      slotFp90At s0.sp sc1 = slotFp90At s0.sp sc ∧
      slotRetHeadAt s0.sp sc1 = slotRetHeadAt s0.sp sc ∧
      slotRetTailAt s0.sp sc1 = slotRetTailAt s0.sp sc :=
    ⟨rfl, rfl, rfl, rfl, rfl⟩
  by_cases hbCap : sc.sp08 = 0#64
  · have hdrop : vecU8Buf A.repAlloc sc.sp08 bPtr bs ⊢ emp := by
      rw [hbCap]; exact vecU8Buf_zero_entails_emp A.repAlloc bPtr bs
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left hdrop) (Entails.of_eq (emp_sepConj _))) ?_
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply sepWPp_seq_lscro (mid := (blkPl_576).base + 480#64) hcrl
    dsimp only [kpkScratchAt, slot7At, slotSp40At, slotRetHeadAt, slotRetTailAt]
    rw [hbCap]
    wp_steps_sync_pool ((blkPl_576).base + 480#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s1
    refine SepWPp.weaken_pre ?_
      (step_free_name_ret_placed hC hFs hle_hook hhi x st0 evsPre sc1 nPtr
        0xFFFFFFFFFFFFFFFF#64 sc.ret1 sc.ret2 sc.ret3 sc.ret4
        u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 (.decodeErr e) Hp hal0 hcrl1
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs)
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        ⟨hans_eq, by simp only [s1, arm64_norm, htr]⟩
        hevs_free
        (hdec_ent x.out sc.sp10_0 sc.sp10_1 sc.sp10_2 sc.sp10_3))
    dsimp only [kpkScratchAt]
    rw [sameSlots.1, sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2.1, sameSlots.2.2.2.2]
    dsimp only [slot7At, slotSp40At, slotRetHeadAt, slotRetTailAt, sc1]
    rw [hbCap]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hb_beq : (sc.sp08 == 0#64) = false := beq_eq_false_iff_ne.mpr hbCap
    have hb_bne : (sc.sp08 != 0#64) = true := bne_iff_ne.mpr hbCap
    have _ := And.intro hb_beq hb_bne
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    dsimp only [kpkScratchAt, slot7At, slotSp40At, slotRetHeadAt, slotRetTailAt]
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_dl
    have hsp_dl : s_dl.sp = s0.sp - 432#64 := by simp only [s_dl, arm64_norm, hsp]
    have hal_dl : s_dl.spAligned = true := sp_sub_432_spAligned hal0 hsp_dl
    have hdealloc := deallocVecBuf_cells_placed_ok (F0 := s_dl.fs.files) (T0 := s_dl.trace)
      hC hFs hle_hook hhi
    refine kpk_call_total_lscro
      ((sc.sp08, bPtr, bs, s0.sp - 432#64), M.stepEvents evsPre st0)
      hdealloc hcrl1
      (by simp only [s_dl, wp_norm, arm64_norm]; try bv_omega)
      (by simp only [s_dl, arm64_norm, *])
      hal_dl
      (ret_pc := (blkPl_576).base + 480#64)
      (by simp only [s_dl, wp_norm, arm64_norm])
      (F := vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ∗
        Hp ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc1 ∗ kpkSavedRegs s0)
      ?_ (hnext := ?_)
    · dsimp only [deallocVecBufCellsSpec, kpkScratchAt]
      rw [sameSlots.1, sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2.1, sameSlots.2.2.2.2]
      dsimp only [slot7At, slotSp40At, slotRetHeadAt, slotRetTailAt, sc1]
      have hpure_dl :
          (FsInv s_dl.fs.files s_dl.trace s_dl ∧ sc.sp08 ≠ 0#64 ∧
            s_dl.readReg64 .x0 = bPtr ∧ s_dl.readReg64 .x1 = sc.sp08 ∧
            s_dl.readReg64 .x2 = 1#64 ∧ s_dl.sp = s0.sp - 432#64 ∧
            LsRetAddr624 (s_dl.readReg64 .lr)) = True :=
        eq_true ⟨withFsInv_entry s_dl, hbCap,
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm],
          hsp_dl,
          by rw [show s_dl.readReg64 .lr = (blkPl_576).base + 480#64 by
               simp only [s_dl, wp_norm, arm64_norm]]
             exact lsRetAddr624_blockPlacement_base_add 576 480#64 (by decide) (by decide)⟩
      rw [hpure_dl, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after hcrl2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [deallocVecBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
      rw [← M.stepEvents_append]
      have htr_tot : s_after.trace = s0.trace := by
        rw [htr2]; simp only [s_dl, arm64_norm, htr]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (step_free_name_ret_placed hC hFs hle_hook hhi x st0
          (evsPre ++ rustDeallocEvents sc.sp08.toNat 1) sc1 nPtr
          0xFFFFFFFFFFFFFFFF#64 sc.ret1 sc.ret2 sc.ret3 sc.ret4
          u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 (.decodeErr e) Hp hal0 hcrl2 hpc2 hrun2
          (hsp2.trans hsp_dl)
          (hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [s_dl, calleeSavedVRegs, arm64_norm]; exact hvregs))
          (hcsp2.1.trans (by simp only [s_dl, arm64_norm, hx19]))
          (hcsp2.2.1.trans (by simp only [s_dl, arm64_norm, hx20]))
          (hcsp2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx21]))
          (hcsp2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm]))
          (hcsp2.2.2.2.1.trans (by simp only [s_dl, arm64_norm]))
          (hcsp2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm]))
          (hcsp2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm]))
          (hcsp2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm]))
          ⟨hans_eq, htr_tot⟩
          (fun evsF hF => by
            rw [List.append_assoc]
            exact hevs_free _ ((FreeOnlyEvs.singleton 1 sc.sp08.toNat).append hF))
          (hdec_ent x.out sc.sp10_0 sc.sp10_1 sc.sp10_2 sc.sp10_3))

theorem step_dec_ok_ret_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → BitVec 32 → List AllocEvent → Prop}
    {DecodeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {Qp : State → SepProp → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hFs : TraceFsSound (lsProg_576 H))
    (hle_hook : extHookStack ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64)
    (x : KpkPollGhost) (st0 : M.σ) (evsPre : List AllocEvent)
    {s0 s : State}
    (sc : KpkScratch) (nPtr bCap bPtr : BitVec 64) (bs : List (BitVec 8))
    (w0 w1 w2 w3 w4 : BitVec 64)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 : BitVec 64)
    (rec : KyberPreKeyRecord) (Hp : SepProp)
    (hal0 : s0.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_576).base + 216#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 432#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx1 : s.readReg64 .x1 = bCap)
    (hx9 : s.readReg64 .x9 = w1)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = nPtr)
    (hx22 : s.readReg64 .x22 = bPtr)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = w2)
    (hx27 : s.readReg64 .x27 = w3)
    (hx28 : s.readReg64 .x28 = w4)
    (hans_eq : .found rec = kpkAnsOf
      (pkAnsOf KyberPreKeyRecord.deserialize (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
      (pkAnsOf KyberPreKeyRecord.deserialize (x.kg.lastResort.get rd s0.fs.files (keyName x.id))))
    (hevs_free : ∀ evsF, FreeOnlyEvs evsF →
      CliKpkGetPollEnv DecEnv GetEnv DecodeEnv rd s0.fs.files x (evsPre ++ evsF))
    (hfound_ent :
      words11At x.out w0 w1 w2 w3 w4
        sc.fp90_4 sc.fp90_5 sc.fp90_0 sc.fp90_1 sc.fp90_2 sc.fp90_3 ∗ Hp ⊢
        kpkAnsAt A.repAlloc x.out (.found rec)) :
    SepWPp (lsProg_576 H) (s0.readReg64 Reg.lr) s
      (vecU8Buf A.repAlloc bCap bPtr bs ∗
        vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ∗
        Hp ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        A.pool lim (M.stepEvents evsPre st0) s ∗ stackAt (s0.sp - 432#64) calleeStk ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc ∗ kpkSavedRegs s0)
      (KpkExitPost rd pathOk A lim DecEnv GetEnv DecodeEnv calleeStk x st0 s0)
      Qp := by
  let sc1 : KpkScratch :=
    { sc with
      sp10_0 := sc.fp90_0, sp10_1 := sc.fp90_1,
      sp10_2 := sc.fp90_2, sp10_3 := sc.fp90_3,
      sp10_4 := sc.fp90_4, sp10_5 := sc.fp90_5 }
  have sameSlots :
      slotSp40At s0.sp sc1 = slotSp40At s0.sp sc ∧
      slotSp70At s0.sp sc1 = slotSp70At s0.sp sc ∧
      slotDecAt s0.sp sc1 = slotDecAt s0.sp sc ∧
      slotFp90At s0.sp sc1 = slotFp90At s0.sp sc ∧
      slotRetHeadAt s0.sp sc1 = slotRetHeadAt s0.sp sc ∧
      slotRetTailAt s0.sp sc1 = slotRetTailAt s0.sp sc :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hbCap : bCap = 0#64
  · subst hbCap
    have hdrop : vecU8Buf A.repAlloc 0#64 bPtr bs ⊢ emp :=
      vecU8Buf_zero_entails_emp A.repAlloc bPtr bs
    refine SepWPp.weaken_pre
      (Entails.trans (sepConj_mono_left hdrop) (Entails.of_eq (emp_sepConj _))) ?_
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply sepWPp_seq_lscro (mid := (blkPl_576).base + 480#64) hcrl
    dsimp only [kpkScratchAt, slot7At, slotFp90At]
    wp_steps_sync_pool ((blkPl_576).base + 480#64)
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s1
    refine SepWPp.weaken_pre ?_
      (step_free_name_ret_placed hC hFs hle_hook hhi x st0 evsPre sc1 nPtr
        w0 w1 w2 w3 w4
        u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 (.found rec) Hp hal0 hcrl1
        (by simp only [s1, arm64_norm])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, calleeSavedVRegs, arm64_norm] at hvregs ⊢; exact hvregs)
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        (by simp only [s1, arm64_norm, *])
        ⟨hans_eq, by simp only [s1, arm64_norm, htr]⟩
        hevs_free
        hfound_ent)
    dsimp only [kpkScratchAt]
    rw [sameSlots.1, sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2.1,
      sameSlots.2.2.2.2.1, sameSlots.2.2.2.2.2]
    dsimp only [slot7At, slotFp90At, sc1]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hb_beq : (bCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbCap
    have hb_bne : (bCap != 0#64) = true := bne_iff_ne.mpr hbCap
    have _ := And.intro hb_beq hb_bne
    have hal : s.spAligned = true := sp_sub_432_spAligned hal0 hsp
    let _ := hal
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    dsimp only [kpkScratchAt, slot7At, slotFp90At]
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by simp only [wp_norm, arm64_norm]; try bv_omega)
      (by simp only [arm64_norm, *])
    intro hcrl1
    apply bind_sepWPp_state; intro s_dl
    have hsp_dl : s_dl.sp = s0.sp - 432#64 := by simp only [s_dl, arm64_norm, hsp]
    have hal_dl : s_dl.spAligned = true := sp_sub_432_spAligned hal0 hsp_dl
    have hdealloc := deallocVecBuf_cells_placed_ok (F0 := s_dl.fs.files) (T0 := s_dl.trace)
      hC hFs hle_hook hhi
    refine kpk_call_total_lscro
      ((bCap, bPtr, bs, s0.sp - 432#64), M.stepEvents evsPre st0)
      hdealloc hcrl1
      (by simp only [s_dl, wp_norm, arm64_norm]; try bv_omega)
      (by simp only [s_dl, arm64_norm, *])
      hal_dl
      (ret_pc := (blkPl_576).base + 480#64)
      (by simp only [s_dl, wp_norm, arm64_norm])
      (F := vecU8Buf A.repAlloc sc.dec0 nPtr (keyName x.id) ∗
        Hp ∗
        words11At x.out u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 ∗
        (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        kpkSlack3 s0.sp ∗ kpkScratchAt s0.sp sc1 ∗ kpkSavedRegs s0)
      ?_ (hnext := ?_)
    · dsimp only [deallocVecBufCellsSpec, kpkScratchAt]
      rw [sameSlots.1, sameSlots.2.1, sameSlots.2.2.1, sameSlots.2.2.2.1,
        sameSlots.2.2.2.2.1, sameSlots.2.2.2.2.2]
      dsimp only [slot7At, slotFp90At, sc1]
      have hpure_dl :
          (FsInv s_dl.fs.files s_dl.trace s_dl ∧ bCap ≠ 0#64 ∧
            s_dl.readReg64 .x0 = bPtr ∧ s_dl.readReg64 .x1 = bCap ∧
            s_dl.readReg64 .x2 = 1#64 ∧ s_dl.sp = s0.sp - 432#64 ∧
            LsRetAddr624 (s_dl.readReg64 .lr)) = True :=
        eq_true ⟨withFsInv_entry s_dl, hbCap,
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm, *],
          by simp only [s_dl, arm64_norm],
          hsp_dl,
          by rw [show s_dl.readReg64 .lr = (blkPl_576).base + 480#64 by
               simp only [s_dl, wp_norm, arm64_norm]]
             exact lsRetAddr624_blockPlacement_base_add 576 480#64 (by decide) (by decide)⟩
      rw [hpure_dl, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s_after hcrl2 hpc2 hrun2 hsp2 hcsp2
      dsimp only [deallocVecBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
      rw [← M.stepEvents_append]
      have htr_tot : s_after.trace = s0.trace := by
        rw [htr2]; simp only [s_dl, arm64_norm, htr]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (step_free_name_ret_placed hC hFs hle_hook hhi x st0
          (evsPre ++ rustDeallocEvents bCap.toNat 1) sc1 nPtr
          w0 w1 w2 w3 w4
          u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 (.found rec) Hp hal0 hcrl2 hpc2 hrun2
          (hsp2.trans hsp_dl)
          (hcsp2.2.2.2.2.2.2.2.2.2.2.2.trans
            (by simp only [s_dl, calleeSavedVRegs, arm64_norm]; exact hvregs))
          (hcsp2.1.trans (by simp only [s_dl, arm64_norm, hx19]))
          (hcsp2.2.1.trans (by simp only [s_dl, arm64_norm, hx20]))
          (hcsp2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx21]))
          (hcsp2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx23]))
          (hcsp2.2.2.2.1.trans (by simp only [s_dl, arm64_norm]))
          (hcsp2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx26]))
          (hcsp2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx27]))
          (hcsp2.2.2.2.2.2.2.2.2.2.1.trans (by simp only [s_dl, arm64_norm, hx28]))
          ⟨hans_eq, htr_tot⟩
          (fun evsF hF => by
            rw [List.append_assoc]
            exact hevs_free _ ((FreeOnlyEvs.singleton 1 bCap.toNat).append hF))
          hfound_ent)

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.EpiloguePlacedBudget
