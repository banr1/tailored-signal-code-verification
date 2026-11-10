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
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetAux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice

/-!
# Budget-Threaded Relocatable Epilogue and Error Branches for `get_pre_key::{closure#0}`

Budget-threaded shared epilogue (`+348 .. +404`) and error-branch helpers (`+200`, `+152`) for
Block `573` (`lsProg_573 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (SignalProtocolError)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag speWord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (PreKeyRecord)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost PkAns PkPollGhost ReadRule dirAt keyName pkAnsOf pkGetAnsAt)
open CryptoVerification.SignalSession.Cli.Placed (blkLib_eq_573 blkPC_573 blkPl_573 lsProg_573)
open CryptoVerification.SignalSession.Cli.Store.PkGetPoll.Helpers
  (bind_sepWP_state decodeErr_reassemble memRegion_56_cells pkBoxKeep pkDecPayload pkPollSlack
   pkSavedRegs readErrHeap readErr_reassemble sp_sub_256_spAligned vecU8BufRest)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget SeqEnv rustDeallocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
  (CliPkGetPollEnv OptPkDecodeEnv deallocBufCellsSpec pkGetPollInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudgetAux
  (bytes_zero_elim_p pkEpiloguePost pkFrame_pack_p pk_call_total_sepWP_lscro)

section Placed

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

theorem cliPkGetPollEnv_of_steps
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {F0 : CryptoVerification.LibsignalPublicApi.StoreKit.FsFiles}
    {x : PkPollGhost} {e1 e2 e3 evs_free : List AllocEvent}
    (h1 : DecEnv x.id e1)
    (h2 : GetEnv x.dir (keyName x.id) e2)
    (h3 : OptPkDecodeEnv PkDecEnv (x.dir.get rd F0 (keyName x.id)) e3)
    (hf : FreeOnlyEvs evs_free) :
    CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd F0 x ((e1 ++ e2 ++ e3) ++ evs_free) := by
  rw [List.append_assoc, List.append_assoc]
  exact SeqEnv.append h1 (SeqEnv.append h2 (SeqEnv.append h3 hf))

private theorem cliPkGetPollEnv_cont_now
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {F0 : CryptoVerification.LibsignalPublicApi.StoreKit.FsFiles}
    {x : PkPollGhost} {evs : List AllocEvent}
    (h : ∀ evs_free, FreeOnlyEvs evs_free →
      CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd F0 x (evs ++ evs_free)) :
    CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd F0 x evs := by
  simpa only [List.append_nil] using h [] FreeOnlyEvs.nil

private theorem cliPkGetPollEnv_cont_dealloc
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {F0 : CryptoVerification.LibsignalPublicApi.StoreKit.FsFiles}
    {x : PkPollGhost} {evs : List AllocEvent}
    (h : ∀ evs_free, FreeOnlyEvs evs_free →
      CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd F0 x (evs ++ evs_free))
    (sz al : Nat) :
    ∀ evs_free, FreeOnlyEvs evs_free →
      CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd F0 x
        ((evs ++ rustDeallocEvents sz al) ++ evs_free) := by
  intro evs_free hf
  rw [List.append_assoc]
  exact h (rustDeallocEvents sz al ++ evs_free)
    (FreeOnlyEvs.append (FreeOnlyEvs.singleton al sz) hf)

/-! ## 1. Shared Epilogue (`+348` .. `+404` `ret`) on `lsProg_573 H` -/

theorem step_epilogue_348_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {st0 : M.σ} {evs : List AllocEvent}
    {s0 s : State} {P : SepProp}
    (ans : PkAns PreKeyRecord)
    (o0 o1 o2 o3 o4 o5 o6 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6 : BitVec 64)
    (payload : SepProp)
    (hpc : s.pc = (blkPl_573).base + bv% (348))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = o0)
    (hx25 : s.readReg64 .x25 = o1)
    (hx23 : s.readReg64 .x23 = o2)
    (hx24 : s.readReg64 .x24 = o3)
    (hx21 : s.readReg64 .x21 = o4)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns :
      ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        s.trace = s0.trace)
    (hevs : CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x evs)
    (hReasm :
      ((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗
        ((x.out + 16#64) ↦₆₄ o2) ∗ ((x.out + 24#64) ↦₆₄ o3) ∗
        ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
        ((x.out + 48#64) ↦₆₄ o6)) ∗ payload ⊢
      pkGetAnsAt A.repAlloc x.out ans)
    (hP : P ⊢
      pkBoxKeep x s0 ∗ payload ∗ dirAt A.repAlloc x.self x.dir ∗
        A.pool lim (M.stepEvents evs st0) s ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ o5) ∗ ((s0.sp - 248#64) ↦₆₄ o6) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ n0) ∗ ((s0.sp - 192#64) ↦₆₄ n1) ∗ ((s0.sp - 184#64) ↦₆₄ n2) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk x st0 s0) := by
  refine SepWP.weaken_pre hP ?_
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  unfold pkBoxKeep
  rw [memRegion_56_cells x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => ?_
  unfold pkSavedRegs
  wp_steps_sync_pool (s0.readReg64 Reg.lr)
  apply bind_sepWP_state; intro sf
  apply SepWP.done (by simp only [sf, wp_norm, arm64_norm, *])
    (by simp only [sf, wp_norm, arm64_norm, *])
  refine ⟨by simp only [sf, wp_norm, arm64_norm, *], ?_, ?_⟩
  · refine ⟨by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *],
      by simp only [sf, wp_norm, arm64_norm, *]⟩
  · have htr_sf : sf.trace = s.trace := by simp only [sf, wp_norm, arm64_norm]
    have hAns' :
        ans = pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
          sf.trace = s0.trace ∧
          CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x evs :=
      ⟨hAns.1, htr_sf.trans hAns.2, hevs⟩
    dsimp only [pkGetPollInnerSpec]
    have hpack := pkFrame_pack_p s0.sp s0 o5 o6 u2 u3 u4 u5 n0 n1 n2 k0 k1 g0 g1 g2 g3 g4 g5 g6
    refine Entails.trans (Q :=
      (((x.out ↦₆₄ o0) ∗ ((x.out + 8#64) ↦₆₄ o1) ∗
          ((x.out + 16#64) ↦₆₄ o2) ∗ ((x.out + 24#64) ↦₆₄ o3) ∗
          ((x.out + 32#64) ↦₆₄ o4) ∗ ((x.out + 40#64) ↦₆₄ o5) ∗
          ((x.out + 48#64) ↦₆₄ o6)) ∗ payload) ∗
      (pkPollSlack s0.sp ∗ pkSavedRegs s0.sp s0 ∗
        ((s0.sp - 256#64) ↦₆₄ o5) ∗ ((s0.sp - 248#64) ↦₆₄ o6) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ n0) ∗ ((s0.sp - 192#64) ↦₆₄ n1) ∗ ((s0.sp - 184#64) ↦₆₄ n2) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ g0) ∗ ((s0.sp - 144#64) ↦₆₄ g1) ∗
        ((s0.sp - 136#64) ↦₆₄ g2) ∗ ((s0.sp - 128#64) ↦₆₄ g3) ∗
        ((s0.sp - 120#64) ↦₆₄ g4) ∗ ((s0.sp - 112#64) ↦₆₄ g5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) ∗
      ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st0) sf ∗
        stackAt (s0.sp - 256#64) calleeStk)) ?_ ?_
    · unfold pkSavedRegs
      exact Entails.of_eq (by sep_ac_rfl)
    · refine Entails.trans (sepConj_mono hReasm (sepConj_mono_left hpack)) ?_
      refine Entails.trans (Q :=
        pkGetAnsAt A.repAlloc x.out ans ∗
          ((x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 12#64) ↦₈ 1#8) ∗
            dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st0) sf ∗
            stackAt (s0.sp - 256#64) calleeStk ∗ cells (s0.sp - 256#64) 32))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      exact Entails.sepExists_right evs
        (sepConj_mono_left (Entails.sepExists_right ans (Entails.pure_right hAns' (Entails.refl _))))

/-! ## 2. Branch 1 (`Dir::get` returned `Err`, `+200` .. `+232` -> `+348`) -/

theorem step_err_200_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {st0 : M.σ} {evs : List AllocEvent}
    {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (lsProg_573 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A lim calleeStk)))
    (w1 w2 w3 w4 w5 nCap nPtr nLen u0 u1 u2 u3 u4 u5 k0 k1 g6 : BitVec 64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_573).base + bv% (200))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = w3)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = speWord 1)
    (hx27 : s.readReg64 .x27 = s0.sp - 152#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hAns :
      (PkAns.readErr : PkAns PreKeyRecord) =
          pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)) ∧
        s.trace = s0.trace)
    (hevs : ∀ evs_free, FreeOnlyEvs evs_free →
      CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x (evs ++ evs_free))
    (hP : P ⊢
      pkBoxKeep x s0 ∗ readErrHeap A.repAlloc w1 w2 w3 w4 w5 ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st0) s ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 144#64) ↦₆₄ w1) ∗
        ((s0.sp - 136#64) ↦₆₄ w2) ∗ ((s0.sp - 128#64) ↦₆₄ w3) ∗
        ((s0.sp - 120#64) ↦₆₄ w4) ∗ ((s0.sp - 112#64) ↦₆₄ w5) ∗ ((s0.sp - 104#64) ↦₆₄ g6)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk x st0 s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  by_cases hnCap : nCap = 0#64
  · subst hnCap
    refine bytes_zero_elim_p (ptr := nPtr) (bs := keyName x.id)
      (Rest := pkBoxKeep x s0 ∗ readErrHeap A.repAlloc w1 w2 w3 w4 w5 ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st0) s ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 144#64) ↦₆₄ w1) ∗
        ((s0.sp - 136#64) ↦₆₄ w2) ∗ ((s0.sp - 128#64) ↦₆₄ w3) ∗
        ((s0.sp - 120#64) ↦₆₄ w4) ∗ ((s0.sp - 112#64) ↦₆₄ w5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
      (by sep_ac_rfl) ?_
    apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl
    wp_steps_sync_pool ((blkPl_573).base + bv% (348))
    apply bind_sepWP_state; intro s_ep
    apply SepWP.done (by simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
    intro _hcrl_ep
    have htr_ep : s_ep.trace = s.trace := by simp only [s_ep, wp_norm, arm64_norm]
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    exact step_epilogue_348_placed .readErr errTag (speWord 1) w1 w2 w3 w4 w5
      u2 u3 u4 u5 0#64 nPtr nLen k0 k1 (speWord 1) w1 w2 w3 w4 w5 g6
      (readErrHeap A.repAlloc w1 w2 w3 w4 w5)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *]; rfl)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns.1, htr_ep.trans hAns.2⟩
      (cliPkGetPollEnv_cont_now hevs)
      (readErr_reassemble A.repAlloc x.out w1 w2 w3 w4 w5)
      (Entails.of_eq (by sep_ac_rfl))
  · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply bind_sepWP_state; intro s_dl
    apply SepWP.done (by simp only [s_dl, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dl, wp_norm, arm64_norm, *])
    intro hcrl1
    have hsp_dl : s_dl.sp = s0.sp - 256#64 := by simp only [s_dl, wp_norm, arm64_norm, hsp]
    have hal_dl : s_dl.spAligned = true := sp_sub_256_spAligned hal0 hsp_dl
    refine pk_call_total_sepWP_lscro
      ((nPtr, nCap, keyName x.id, s0.sp - 256#64), M.stepEvents evs st0)
      hDeallocCells hcrl1
      (by simp only [s_dl, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dl, wp_norm, arm64_norm, *])
      hal_dl
      (by simp only [s_dl, wp_norm, arm64_norm]; rfl)
      (F := pkBoxKeep x s0 ∗ readErrHeap A.repAlloc w1 w2 w3 w4 w5 ∗
        dirAt A.repAlloc x.self x.dir ∗
        ((s0.sp - 256#64) ↦₆₄ w4) ∗ ((s0.sp - 248#64) ↦₆₄ w5) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ u4) ∗ ((s0.sp - 216#64) ↦₆₄ u5) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 144#64) ↦₆₄ w1) ∗
        ((s0.sp - 136#64) ↦₆₄ w2) ∗ ((s0.sp - 128#64) ↦₆₄ w3) ∗
        ((s0.sp - 120#64) ↦₆₄ w4) ∗ ((s0.sp - 112#64) ↦₆₄ w5) ∗ ((s0.sp - 104#64) ↦₆₄ g6))
      ?_ (hnext := ?_)
    · dsimp only [deallocBufCellsSpec]
      have hpure_dl :
          (s_dl.readReg64 .x0 = nPtr ∧ s_dl.readReg64 .x1 = nCap ∧
            s_dl.readReg64 .x2 = 1#64 ∧ s_dl.sp = s0.sp - 256#64 ∧ nCap ≠ 0#64 ∧
            LsRetAddr624 (s_dl.readReg64 .lr)) = True :=
        eq_true ⟨by simp only [s_dl, wp_norm, arm64_norm, *],
          by simp only [s_dl, wp_norm, arm64_norm, *],
          by simp only [s_dl, wp_norm, arm64_norm],
          hsp_dl, hnCap,
          by simp (config := { decide := true }) [s_dl, blkPl_573, wp_norm, arm64_norm, lsLen, *]⟩
      rw [hpure_dl, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · rintro sf hcrl_sf hpc_sf hrun_sf hsp_sf
        ⟨hx19_sf, hx20_sf, hx21_sf, _, hx23_sf, hx24_sf, hx25_sf, _, _, _, _, hvregs_sf⟩
      dsimp only [deallocBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun htr_dl => ?_
      rw [← M.stepEvents_append]
      have hsp_sf' : sf.sp = s0.sp - 256#64 := hsp_sf.trans hsp_dl
      have hal_sf : sf.spAligned = true := sp_sub_256_spAligned hal0 hsp_sf'
      have hx19_sf' : sf.readReg64 .x19 = x.fut :=
        hx19_sf.trans (by simp only [s_dl, wp_norm, arm64_norm, hx19])
      have hx20_sf' : sf.readReg64 .x20 = x.out :=
        hx20_sf.trans (by simp only [s_dl, wp_norm, arm64_norm, hx20])
      have hx21_sf' : sf.readReg64 .x21 = w3 :=
        hx21_sf.trans (by simp only [s_dl, wp_norm, arm64_norm, hx21])
      have hx23_sf' : sf.readReg64 .x23 = w1 :=
        hx23_sf.trans (by simp only [s_dl, wp_norm, arm64_norm, hx23])
      have hx24_sf' : sf.readReg64 .x24 = w2 :=
        hx24_sf.trans (by simp only [s_dl, wp_norm, arm64_norm, hx24])
      have hx25_sf' : sf.readReg64 .x25 = speWord 1 :=
        hx25_sf.trans (by simp only [s_dl, wp_norm, arm64_norm, hx25])
      have hvregs_sf' : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        hvregs_sf.trans (by simp only [s_dl, wp_norm, arm64_norm, hvregs])
      have htr_sf' : sf.trace = s.trace :=
        htr_dl.trans (by simp only [s_dl, wp_norm, arm64_norm])
      apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl_sf
      wp_steps_sync_pool ((blkPl_573).base + bv% (348))
      apply bind_sepWP_state; intro s_ep
      apply SepWP.done (by simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_ep, wp_norm, arm64_norm, *])
      intro _hcrl_ep
      have htr_ep : s_ep.trace = sf.trace := by simp only [s_ep, wp_norm, arm64_norm]
      have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
        simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
      exact step_epilogue_348_placed .readErr errTag (speWord 1) w1 w2 w3 w4 w5
        u2 u3 u4 u5 nCap nPtr nLen k0 k1 (speWord 1) w1 w2 w3 w4 w5 g6
        (readErrHeap A.repAlloc w1 w2 w3 w4 w5)
        hpc_ep
        (by simp only [s_ep, wp_norm, arm64_norm, *])
        (by simp only [s_ep, wp_norm, arm64_norm, hsp_sf'])
        hal0
        (by simp only [s_ep, wp_norm, arm64_norm, hx19_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hx20_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm]; rfl)
        (by simp only [s_ep, wp_norm, arm64_norm, hx25_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hx23_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hx24_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hx21_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hvregs_sf'])
        ⟨hAns.1, (htr_ep.trans htr_sf').trans hAns.2⟩
        (cliPkGetPollEnv_cont_now (cliPkGetPollEnv_cont_dealloc hevs nCap.toNat 1))
        (readErr_reassemble A.repAlloc x.out w1 w2 w3 w4 w5)
        (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. Branch 2 (`PreKeyRecord::deserialize` returned `Err`, `+152` .. `+232` -> `+348`) -/

theorem step_dec_err_152_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {DecEnv : BitVec 32 → List AllocEvent → Prop}
    {GetEnv : DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PkDecEnv : List (BitVec 8) → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {calleeStk : Nat} {x : PkPollGhost} {st0 : M.σ} {evs : List AllocEvent}
    {s0 s : State} {P : SepProp}
    (hDeallocCells : subroutine_ok (lsProg_573 H) (lsρ lsRustDeallocSymCli)
      (withLsCodeRoLoaded lsmpl (deallocBufCellsSpec A lim calleeStk)))
    (e : SignalProtocolError) (bytes : List (BitVec 8))
    (w1 w2 nCap nPtr nLen d0 d1 d2 d3 d4 d5 d6 u0 u1 u2 u3 k0 k1 : BitVec 64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_573).base + bv% (152))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 256#64)
    (hal0 : s0.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = d4)
    (hx22 : s.readReg64 .x22 = nPtr)
    (hx23 : s.readReg64 .x23 = w1)
    (hx24 : s.readReg64 .x24 = w2)
    (hx25 : s.readReg64 .x25 = d1)
    (hx27 : s.readReg64 .x27 = d3)
    (hx28 : s.readReg64 .x28 = d2)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hd0_tag : d0 = errTag)
    (hAns : PkAns.decodeErr e =
      pkAnsOf PreKeyRecord.deserialize (x.dir.get rd s0.fs.files (keyName x.id)))
    (hevs : ∀ evs_free, FreeOnlyEvs evs_free →
      CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x (evs ++ evs_free))
    (hP : P ⊢
      pkBoxKeep x s0 ∗ pkDecPayload A.repAlloc (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        (w2 ↦ₛ bytes) ∗ vecU8BufRest A.repAlloc w1 w2 bytes ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st0) s ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
        ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6)) :
    SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s P
      (pkEpiloguePost rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk x st0 s0) := by
  refine SepWP.weaken_pre hP ?_; clear hP
  have hal : s.spAligned = true := sp_sub_256_spAligned hal0 hsp
  suffices hjoin180 : ∀ (s1 : State) (P1 : SepProp) (evs1 : List AllocEvent),
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.pc = (blkPl_573).base + bv% (180) →
      s1.status = .Running →
      s1.sp = s0.sp - 256#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x19 = x.fut →
      s1.readReg64 .x20 = x.out →
      s1.readReg64 .x21 = d4 →
      s1.readReg64 .x22 = nPtr →
      s1.readReg64 .x25 = d1 →
      s1.readReg64 .x27 = d3 →
      s1.readReg64 .x28 = d2 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (∀ evs_free, FreeOnlyEvs evs_free →
        CliPkGetPollEnv DecEnv GetEnv PkDecEnv rd s0.fs.files x (evs1 ++ evs_free)) →
      (P1 ⊢ pkBoxKeep x s0 ∗ pkDecPayload A.repAlloc (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs1 st0) s1 ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ d5) ∗ ((s0.sp - 248#64) ↦₆₄ d6) ∗
        ((s0.sp - 240#64) ↦₆₄ d5) ∗ ((s0.sp - 232#64) ↦₆₄ d6) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6)) →
      SepWP (lsProg_573 H) (s0.readReg64 Reg.lr) s1 P1
        (pkEpiloguePost rd pathOk A lim DecEnv GetEnv PkDecEnv calleeStk x st0 s0) by
    by_cases hw1 : w1 = 0#64
    · subst hw1
      refine bytes_zero_elim_p (ptr := w2) (bs := bytes)
        (Rest := pkBoxKeep x s0 ∗ pkDecPayload A.repAlloc (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
          (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
          dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs st0) s ∗
          stackAt (s0.sp - 256#64) calleeStk ∗
          ((s0.sp - 256#64) ↦₆₄ u0) ∗ ((s0.sp - 248#64) ↦₆₄ u1) ∗
          ((s0.sp - 240#64) ↦₆₄ u2) ∗ ((s0.sp - 232#64) ↦₆₄ u3) ∗
          ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
          ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
          ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
          ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6))
        (by sep_ac_rfl) ?_
      apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (180)) hcrl
      wp_steps_sync_pool ((blkPl_573).base + bv% (180))
      apply bind_sepWP_state; intro s1
      apply SepWP.done (by simp only [s1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s1, wp_norm, arm64_norm, *])
      intro hcrl1
      exact hjoin180 s1 _ evs hcrl1
        (by simp only [s1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        (by simp only [s1, wp_norm, arm64_norm, *])
        hevs
        (Entails.of_eq (by sep_ac_rfl))
    · have hw1_eq : (w1 == 0#64) = false := beq_eq_false_iff_ne.mpr hw1
      have hw1_ne : (w1 != 0#64) = true := bne_iff_ne.mpr hw1
      apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl
      wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
      apply bind_sepWP_state; intro s_dl1
      apply SepWP.done (by simp only [s_dl1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_dl1, wp_norm, arm64_norm, *])
      intro hcrl1
      have hsp_dl1 : s_dl1.sp = s0.sp - 256#64 := by simp only [s_dl1, wp_norm, arm64_norm, hsp]
      have hal_dl1 : s_dl1.spAligned = true := sp_sub_256_spAligned hal0 hsp_dl1
      refine pk_call_total_sepWP_lscro
        ((w2, w1, bytes, s0.sp - 256#64), M.stepEvents evs st0)
        hDeallocCells hcrl1
        (by simp only [s_dl1, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_dl1, wp_norm, arm64_norm, *])
        hal_dl1
        (by simp only [s_dl1, wp_norm, arm64_norm]; rfl)
        (F := pkBoxKeep x s0 ∗ pkDecPayload A.repAlloc (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
          (nPtr ↦ₛ keyName x.id) ∗ vecU8BufRest A.repAlloc nCap nPtr (keyName x.id) ∗
          dirAt A.repAlloc x.self x.dir ∗
          ((s0.sp - 256#64) ↦₆₄ d5) ∗ ((s0.sp - 248#64) ↦₆₄ d6) ∗
          ((s0.sp - 240#64) ↦₆₄ d5) ∗ ((s0.sp - 232#64) ↦₆₄ d6) ∗
          ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
          ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
          ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
          ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
          ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
          ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6))
        ?_ (hnext := ?_)
      · dsimp only [deallocBufCellsSpec]
        have hpure_dl1 :
            (s_dl1.readReg64 .x0 = w2 ∧ s_dl1.readReg64 .x1 = w1 ∧
              s_dl1.readReg64 .x2 = 1#64 ∧ s_dl1.sp = s0.sp - 256#64 ∧ w1 ≠ 0#64 ∧
              LsRetAddr624 (s_dl1.readReg64 .lr)) = True :=
          eq_true ⟨by simp only [s_dl1, wp_norm, arm64_norm, *],
            by simp only [s_dl1, wp_norm, arm64_norm, *],
            by simp only [s_dl1, wp_norm, arm64_norm],
            hsp_dl1, hw1,
            by simp (config := { decide := true }) [s_dl1, blkPl_573, wp_norm, arm64_norm, lsLen, *]⟩
        rw [hpure_dl1, ProofLib.pure_true, emp_sepConj]
        exact Entails.of_eq (by sep_ac_rfl)
      · rintro sf hcrl_sf hpc_sf hrun_sf hsp_sf
          ⟨hx19_sf, hx20_sf, hx21_sf, hx22_sf, _, _, hx25_sf, _, hx27_sf, hx28_sf, _, hvregs_sf⟩
        dsimp only [deallocBufCellsSpec]
        rw [sepConj_assoc]
        refine SepWP.pure_elim fun htr_dl1 => ?_
        rw [← M.stepEvents_append]
        exact hjoin180 sf _ (evs ++ rustDeallocEvents w1.toNat 1) hcrl_sf
          hpc_sf
          hrun_sf
          (hsp_sf.trans hsp_dl1)
          (htr_dl1.trans (by simp only [s_dl1, wp_norm, arm64_norm, htr]))
          (hx19_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx19]))
          (hx20_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx20]))
          (hx21_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx21]))
          (hx22_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx22]))
          (hx25_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx25]))
          (hx27_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx27]))
          (hx28_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hx28]))
          (hvregs_sf.trans (by simp only [s_dl1, wp_norm, arm64_norm, hvregs]))
          (cliPkGetPollEnv_cont_dealloc hevs w1.toNat 1)
          (Entails.of_eq (by sep_ac_rfl))
  clear hcrl hpc hrun hsp hal htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx27 hx28 hvregs hevs s evs
  intro s1 P1 evs1 hcrl1 hpc1 hrun1 hsp1 htr1 h19_1 h20_1 h21_1 h22_1 h25_1 h27_1 h28_1 hv1
    hevs1 hP1
  refine SepWP.weaken_pre hP1 ?_; clear hP1
  have hal1 : s1.spAligned = true := sp_sub_256_spAligned hal0 hsp1
  by_cases hnCap : nCap = 0#64
  · subst hnCap
    refine bytes_zero_elim_p (ptr := nPtr) (bs := keyName x.id)
      (Rest := pkBoxKeep x s0 ∗ pkDecPayload A.repAlloc (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        dirAt A.repAlloc x.self x.dir ∗ A.pool lim (M.stepEvents evs1 st0) s1 ∗
        stackAt (s0.sp - 256#64) calleeStk ∗
        ((s0.sp - 256#64) ↦₆₄ d5) ∗ ((s0.sp - 248#64) ↦₆₄ d6) ∗
        ((s0.sp - 240#64) ↦₆₄ d5) ∗ ((s0.sp - 232#64) ↦₆₄ d6) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ 0#64) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6))
      (by sep_ac_rfl) ?_
    apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl1
    wp_steps_sync_pool ((blkPl_573).base + bv% (348))
    apply bind_sepWP_state; intro s_ep
    apply SepWP.done (by simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_ep, wp_norm, arm64_norm, *])
    intro _hcrl_ep
    have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
      simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
    have hx26_ep : s_ep.readReg64 .x26 = d0 := by
      rw [hd0_tag]; simp only [s_ep, wp_norm, arm64_norm, *]; rfl
    exact step_epilogue_348_placed (.decodeErr e) d0 d1 d2 d3 d4 d5 d6
      d5 d6 d5 d6 0#64 nPtr nLen k0 k1 d0 d1 d2 d3 d4 d5 d6
      (pkDecPayload A.repAlloc (.error e) d0 d1 d2 d3 d4 d5 d6)
      hpc_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hal0
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      hx26_ep
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      (by simp only [s_ep, wp_norm, arm64_norm, *])
      ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, *]⟩
      (cliPkGetPollEnv_cont_now hevs1)
      (decodeErr_reassemble A.repAlloc x.out e d0 d1 d2 d3 d4 d5 d6)
      (Entails.of_eq (by sep_ac_rfl))
  · have hnCap_eq : (nCap == 0#64) = false := beq_eq_false_iff_ne.mpr hnCap
    have hnCap_ne : (nCap != 0#64) = true := bne_iff_ne.mpr hnCap
    apply sepWP_seq_lscro (mid := lsρ lsRustDeallocSymCli) hcrl1
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply bind_sepWP_state; intro s_dl2
    apply SepWP.done (by simp only [s_dl2, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dl2, wp_norm, arm64_norm, *])
    intro hcrl2
    have hsp_dl2 : s_dl2.sp = s0.sp - 256#64 := by simp only [s_dl2, wp_norm, arm64_norm, hsp1]
    have hal_dl2 : s_dl2.spAligned = true := sp_sub_256_spAligned hal0 hsp_dl2
    refine pk_call_total_sepWP_lscro
      ((nPtr, nCap, keyName x.id, s0.sp - 256#64), M.stepEvents evs1 st0)
      hDeallocCells hcrl2
      (by simp only [s_dl2, wp_norm, arm64_norm, *]; try bv_omega)
      (by simp only [s_dl2, wp_norm, arm64_norm, *])
      hal_dl2
      (by simp only [s_dl2, wp_norm, arm64_norm]; rfl)
      (F := pkBoxKeep x s0 ∗ pkDecPayload A.repAlloc (.error e) d0 d1 d2 d3 d4 d5 d6 ∗
        dirAt A.repAlloc x.self x.dir ∗
        ((s0.sp - 256#64) ↦₆₄ d5) ∗ ((s0.sp - 248#64) ↦₆₄ d6) ∗
        ((s0.sp - 240#64) ↦₆₄ d5) ∗ ((s0.sp - 232#64) ↦₆₄ d6) ∗
        ((s0.sp - 224#64) ↦₆₄ d5) ∗ ((s0.sp - 216#64) ↦₆₄ d6) ∗
        ((s0.sp - 200#64) ↦₆₄ nCap) ∗ ((s0.sp - 192#64) ↦₆₄ nPtr) ∗ ((s0.sp - 184#64) ↦₆₄ nLen) ∗
        ((s0.sp - 176#64) ↦₆₄ k0) ∗ ((s0.sp - 168#64) ↦₆₄ k1) ∗
        ((s0.sp - 152#64) ↦₆₄ d0) ∗ ((s0.sp - 144#64) ↦₆₄ d1) ∗
        ((s0.sp - 136#64) ↦₆₄ d2) ∗ ((s0.sp - 128#64) ↦₆₄ d3) ∗
        ((s0.sp - 120#64) ↦₆₄ d4) ∗ ((s0.sp - 112#64) ↦₆₄ d5) ∗ ((s0.sp - 104#64) ↦₆₄ d6))
      ?_ (hnext := ?_)
    · dsimp only [deallocBufCellsSpec]
      have hpure_dl2 :
          (s_dl2.readReg64 .x0 = nPtr ∧ s_dl2.readReg64 .x1 = nCap ∧
            s_dl2.readReg64 .x2 = 1#64 ∧ s_dl2.sp = s0.sp - 256#64 ∧ nCap ≠ 0#64 ∧
            LsRetAddr624 (s_dl2.readReg64 .lr)) = True :=
        eq_true ⟨by simp only [s_dl2, wp_norm, arm64_norm, *],
          by simp only [s_dl2, wp_norm, arm64_norm, *],
          by simp only [s_dl2, wp_norm, arm64_norm],
          hsp_dl2, hnCap,
          by simp (config := { decide := true }) [s_dl2, blkPl_573, wp_norm, arm64_norm, lsLen, *]⟩
      rw [hpure_dl2, ProofLib.pure_true, emp_sepConj]
      exact Entails.of_eq (by sep_ac_rfl)
    · rintro sf hcrl_sf hpc_sf hrun_sf hsp_sf
        ⟨hx19_sf, hx20_sf, hx21_sf, _, hx23_sf, hx24_sf, hx25_sf, _, _, _, _, hvregs_sf⟩
      dsimp only [deallocBufCellsSpec]
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun htr_dl2 => ?_
      rw [← M.stepEvents_append]
      have hsp_sf' : sf.sp = s0.sp - 256#64 := hsp_sf.trans hsp_dl2
      have hal_sf : sf.spAligned = true := sp_sub_256_spAligned hal0 hsp_sf'
      have hx19_sf' : sf.readReg64 .x19 = x.fut :=
        hx19_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h19_1])
      have hx20_sf' : sf.readReg64 .x20 = x.out :=
        hx20_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h20_1])
      have hx21_sf' : sf.readReg64 .x21 = d4 :=
        hx21_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h21_1])
      have hx23_sf' : sf.readReg64 .x23 = d2 :=
        hx23_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm])
      have hx24_sf' : sf.readReg64 .x24 = d3 :=
        hx24_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm])
      have hx25_sf' : sf.readReg64 .x25 = d1 :=
        hx25_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, h25_1])
      have hvregs_sf' : calleeSavedVRegs sf = calleeSavedVRegs s0 :=
        hvregs_sf.trans (by simp only [s_dl2, wp_norm, arm64_norm, hv1])
      have htr_sf' : sf.trace = s0.trace :=
        htr_dl2.trans (by simp only [s_dl2, wp_norm, arm64_norm, htr1])
      apply sepWP_seq_lscro (mid := (blkPl_573).base + bv% (348)) hcrl_sf
      wp_steps_sync_pool ((blkPl_573).base + bv% (348))
      apply bind_sepWP_state; intro s_ep
      apply SepWP.done (by simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega)
        (by simp only [s_ep, wp_norm, arm64_norm, *])
      intro _hcrl_ep
      have hpc_ep : s_ep.pc = (blkPl_573).base + bv% (348) := by
        simp only [s_ep, wp_norm, arm64_norm, *]; try bv_omega
      have hx26_ep : s_ep.readReg64 .x26 = d0 := by
        rw [hd0_tag]; simp only [s_ep, wp_norm, arm64_norm]; rfl
      exact step_epilogue_348_placed (.decodeErr e) d0 d1 d2 d3 d4 d5 d6
        d5 d6 d5 d6 nCap nPtr nLen k0 k1 d0 d1 d2 d3 d4 d5 d6
        (pkDecPayload A.repAlloc (.error e) d0 d1 d2 d3 d4 d5 d6)
        hpc_ep
        (by simp only [s_ep, wp_norm, arm64_norm, *])
        (by simp only [s_ep, wp_norm, arm64_norm, hsp_sf'])
        hal0
        (by simp only [s_ep, wp_norm, arm64_norm, hx19_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hx20_sf'])
        hx26_ep
        (by simp only [s_ep, wp_norm, arm64_norm, hx25_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hx23_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hx24_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hx21_sf'])
        (by simp only [s_ep, wp_norm, arm64_norm, hvregs_sf'])
        ⟨hAns, by simp only [s_ep, wp_norm, arm64_norm, htr_sf']⟩
        (cliPkGetPollEnv_cont_now (cliPkGetPollEnv_cont_dealloc hevs1 nCap.toNat 1))
        (decodeErr_reassemble A.repAlloc x.out e d0 d1 d2 d3 d4 d5 d6)
        (Entails.of_eq (by sep_ac_rfl))

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.BlocksPlacedBudget
