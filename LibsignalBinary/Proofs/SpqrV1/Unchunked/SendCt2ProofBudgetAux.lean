/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegsBudget
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Proof
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux -- shake: keep
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275 -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Fixed-Base Loops and Segment 2

Defines Segment 5b deallocation events (`sendCt2Seg5bEvents`), lifts the fixed-base
Issue-1275 loops with `VmPreserved`, and proves fixed-base Segment 2 (`+136 → +552`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.LibsignalTripleRatchet (extHookStack tripleRatchetProgAtExt)
open CryptoVerification.LibsignalSpqrV1 (
  Bytes flipEndiannessOfEncapsulationStateBytes issue1275NeedsFlip swapAdjacentPairs
)
open CryptoVerification.SpqrV1.States.Leaves (
  UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name
  unchunkedCt1SentEkReceivedSendCt2_fnOff
)
open CryptoVerification.SpqrV1.Unchunked (
  ScanLoopSaved SwapLoopSaved es_scan_split es_swap_join es_swap_split
  issue1275NeedsFlip_cons_cont issue1275NeedsFlip_cons_false_not_be
  issue1275NeedsFlip_cons_true_be issue1275_word_eq
  pointsToBytes_pair_pointsTo16 pointsToBytes_pair_split sendCt2EsWorkAt
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (sepWP_rebase_vmPreserved trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget (AllocContracts4K)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (
  SendCt2Reserve128Env UnchunkedSendCt2PostEnv UnchunkedSendCt2PreEnv
  fitsEvents_flipAlloc_of_preEnv
  sendCt2ConcatHmacEvents sendCt2FlipAllocEvents sendCt2Seg23Events
  sepWPp_weaken_pre
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget (
  send_ct2_5d8_to_604_wpp
)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (
  freeOnlyEvs_rustDeallocEvents freeOnlyEvs_sendCt2MdDeallocEvents
  sendCt2MdDeallocEvents sendCt2Seg5aEvents
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setMem_setPC_pre

/-! ## Segment 5b Deallocation Events -/

/-- Deallocation events of Segment 5b (`ct1`, `es`, and `ek` heap buffers). -/
def sendCt2Seg5bEvents (cap_ct1' esCap ekCap : BitVec 64) : List AllocEvent :=
  rustDeallocEvents cap_ct1'.toNat 1 ++
    rustDeallocEvents esCap.toNat 1 ++
    rustDeallocEvents ekCap.toNat 1

theorem freeOnlyEvs_sendCt2Seg5bEvents (cap_ct1' esCap ekCap : BitVec 64) :
    FreeOnlyEvs (sendCt2Seg5bEvents cap_ct1' esCap ekCap) :=
  FreeOnlyEvs.append
    (FreeOnlyEvs.append
      (freeOnlyEvs_rustDeallocEvents _ _)
      (freeOnlyEvs_rustDeallocEvents _ _))
    (freeOnlyEvs_rustDeallocEvents _ _)

/-- Appending `sendCt2Seg5bEvents cap_ct1' esCap ekCap` after Segments 2–5a satisfies
    `UnchunkedSendCt2PostEnv x`. -/
theorem unchunkedSendCt2PostEnv_of_seg5b {F : ShaCompress} {x : UnchunkedSendCt2Ghost F}
    {evsRes : List AllocEvent} (hRes : SendCt2Reserve128Env x.st.ct1.length evsRes)
    (cap_ct1' esCap ekCap : BitVec 64) :
    UnchunkedSendCt2PostEnv x
      ((sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2Seg5aEvents x.st.ct1.length) ++
        sendCt2Seg5bEvents cap_ct1' esCap ekCap) := by
  refine ⟨sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length,
    sendCt2MdDeallocEvents x.st.ct1.length ++ sendCt2Seg5bEvents cap_ct1' esCap ekCap,
    ⟨evsRes, hRes, rfl⟩,
    FreeOnlyEvs.append
      (freeOnlyEvs_sendCt2MdDeallocEvents x.st.ct1.length)
      (freeOnlyEvs_sendCt2Seg5bEvents cap_ct1' esCap ekCap),
    ?_⟩
  unfold sendCt2Seg5aEvents
  simp only [List.append_assoc]

/-! ## Fixed-Base `swapAdjacentPairs` Loop with `VmPreserved` -/

theorem swap_loop_step_last_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (basePtr : BitVec 64) (b0 b1 : BitVec 8) (s : State) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = 2046#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s (((basePtr + 2046#64) ↦ₛ [b0, b1]) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = (((basePtr + 2046#64) ↦ₛ [b1, b0]) ∗ Frame) ∧
        sf.readReg64 .x21 = 1#64 ∧
        SwapLoopSaved s sf) := by
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  rw [pointsToBytes_pair_split (basePtr + 2046#64) b0 b1 [], pointsToBytes_nil, sepConj_emp]
  wp_steps
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], ?_, by simp only [Reg.x21, arm64_norm], ?_⟩
  · rw [pointsToBytes_pair_split (basePtr + 2046#64) b1 b0 [], pointsToBytes_nil, sepConj_emp]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx22]

theorem swap_loop_step_more_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (basePtr off : BitVec 64) (b0 b1 : BitVec 8) (s : State) (Frame : SepProp)
    (hoff : off.toNat < 2046)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = off) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64)
      s (((basePtr + off) ↦₈ b0) ∗ ((basePtr + off + 1#64) ↦₈ b1) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame) ∧
        sf.readReg64 .x8 = off + 2#64 ∧
        SwapLoopSaved s sf) := by
  have hne : off + 2#64 ≠ 2048#64 := by bv_omega
  have hne_bne : (off + 2#64 != 2048#64) = true := bne_iff_ne.mpr hne
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hne_bne]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], by sep_ac_rfl,
    by simp only [Reg.x8, arm64_norm, hx8], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx22]

theorem swap_loop_vm_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (basePtr : BitVec 64) :
    ∀ (bs : Bytes) (off : BitVec 64) (s : State) (Frame : SepProp),
      bs ≠ [] →
      bs.length % 2 = 0 →
      off.toNat + bs.length = 2048 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x204#64 →
      s.status = .Running →
      s.readReg64 .x22 = basePtr →
      s.readReg64 .x8 = off →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
        s (((basePtr + off) ↦ₛ bs) ∗ Frame)
        (fun sf Pf =>
          VmPreserved s sf ∧
          Pf = (((basePtr + off) ↦ₛ swapAdjacentPairs bs) ∗ Frame) ∧
          sf.readReg64 .x21 = 1#64 ∧
          SwapLoopSaved s sf)
  | [], _, _, _, hne, _, _, _, _, _, _ => (hne rfl).elim
  | [_], _, _, _, _, hmod, _, _, _, _, _ => by simp at hmod
  | [b0, b1], off, s, Frame, _, _, hsum, hpc, hrun, hx22, hx8 => by
    have hoff : off = 2046#64 := by
      simp only [List.length_cons, List.length_nil] at hsum
      bv_omega
    subst hoff
    exact swap_loop_step_last_vm basePtr b0 b1 s Frame hpc hrun hx22 hx8
  | b0 :: b1 :: b2 :: rest, off, s, Frame, _, hmod, hsum, hpc, hrun, hx22, hx8 => by
    have hlen_ge : 3 ≤ (b0 :: b1 :: b2 :: rest).length := by simp
    have hoff_lt : off.toNat < 2046 := by omega
    have hrest_ne : (b2 :: rest) ≠ [] := List.cons_ne_nil b2 rest
    have hrest_mod : (b2 :: rest).length % 2 = 0 := by
      simp only [List.length_cons] at hmod ⊢
      omega
    have hoff2_sum : (off + 2#64).toNat + (b2 :: rest).length = 2048 := by
      simp only [List.length_cons] at hsum ⊢
      have h1 : (off + 2#64).toNat = off.toNat + 2 := by bv_omega
      omega
    have hpre_eq : ((basePtr + off) ↦ₛ (b0 :: b1 :: b2 :: rest)) ∗ Frame =
        ((basePtr + off) ↦₈ b0) ∗ ((basePtr + off + 1#64) ↦₈ b1) ∗
          (((basePtr + (off + 2#64)) ↦ₛ (b2 :: rest)) ∗ Frame) := by
      rw [pointsToBytes_pair_split (basePtr + off) b0 b1 (b2 :: rest)]
      have hadd : basePtr + off + 2#64 = basePtr + (off + 2#64) := by bv_omega
      rw [hadd]
      sep_ac_rfl
    rw [hpre_eq]
    refine SepWP.seq
      (swap_loop_step_more_vm basePtr off b0 b1 s
        (((basePtr + (off + 2#64)) ↦ₛ (b2 :: rest)) ∗ Frame)
        hoff_lt hpc hrun hx22 hx8)
      fun sm Pm hpcm hrunm ⟨hvm1, hPm, hx8_sm, hsaved1⟩ => ?_
    have hPm' : Pm =
        ((basePtr + (off + 2#64)) ↦ₛ (b2 :: rest)) ∗
          (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame) := by
      rw [hPm]
      sep_ac_rfl
    rw [hPm']
    refine SepWP.mono
      (swap_loop_vm_ok basePtr (b2 :: rest) (off + 2#64) sm
        (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame)
        hrest_ne hrest_mod hoff2_sum hpcm hrunm (hsaved1.x22.trans hx22) hx8_sm) ?_
    rintro sf Pf _ _ ⟨hvm2, hPf, hx21_sf, hsaved2⟩
    refine ⟨VmPreserved.trans hvm1 hvm2, ?_, hx21_sf, hsaved1.trans hsaved2⟩
    rw [hPf]
    dsimp only [swapAdjacentPairs]
    rw [pointsToBytes_pair_split (basePtr + off) b1 b0 (swapAdjacentPairs (b2 :: rest))]
    have hadd : basePtr + off + 2#64 = basePtr + (off + 2#64) := by bv_omega
    rw [hadd]
    sep_ac_rfl

theorem swap_loop_pool_ok {b : BitVec 64} {ext : String → Option (State → State)}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (basePtr : BitVec 64)
    (bs : Bytes) (off : BitVec 64) (s : State) (Frame : SepProp)
    (hne : bs ≠ [])
    (hmod : bs.length % 2 = 0)
    (hsum : off.toNat + bs.length = 2048)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 516#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = off) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 552#64)
      s (((basePtr + off) ↦ₛ bs) ∗ A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + off) ↦ₛ swapAdjacentPairs bs) ∗ A.pool lim st sf ∗ Frame) ∧
        sf.readReg64 .x21 = 1#64 ∧
        SwapLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine SepWP.seq
    (swap_loop_vm_ok basePtr bs off s (A.pool lim st s ∗ Frame)
      hne hmod hsum hpc hrun hx22 hx8)
    fun sf Pf hpcm hrunm ⟨hvm, hPf, hx21, hsaved⟩ => ?_
  rw [hPf, ← A.pool_of_vmPreserved hvm]
  exact SepWP.done hpcm hrunm ⟨rfl, hx21, hsaved, hvm⟩

/-! ## Fixed-Base `issue1275NeedsFlip` Scan Loop with `VmPreserved` -/

private theorem scan_exit_500_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  have hadrp :
      ((b + BitVec.ofNat 64
          (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") +
        256#64 &&& 18446744073709547520#64) +
        bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - 0x59000)) =
        b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    rw [unchunkedCt1SentEkReceivedSendCt2_fnOff]
    revert hb; bv_kernel
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc hadrp ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc hadrp
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc hadrp
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], rfl,
    by simp only [Reg.x21, arm64_norm],
    by simp only [Reg.x22, Reg.x19, arm64_norm],
    by simp only [Reg.x28, arm64_norm], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

private theorem scan_exit_574_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x174#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x1d8#64)
      s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf) := by
  have hadrp :
      ((b + BitVec.ofNat 64
          (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") +
        372#64 &&& 18446744073709547520#64) +
        bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - 0x59000)) =
        b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    rw [unchunkedCt1SentEkReceivedSendCt2_fnOff]
    revert hb; bv_kernel
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc hadrp ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc hadrp
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc hadrp
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

private theorem scan_head_step_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (ptr rem : BitVec 64) (w : BitVec 16) (s : State) (Frame : SepProp)
    (hrem_lo : 2 ≤ rem.toNat)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
      s ((ptr ↦₁₆ w) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = ((ptr ↦₁₆ w) ∗ Frame) ∧
        sf.readReg64 .x8 = ptr ∧
        sf.readReg64 .x9 = rem ∧
        sf.readReg64 .x10 = 2#64 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x12 = w.zeroExtend 64 ∧
        sf.readReg64 .x13 = s.readReg64 .x13 ∧
        sf.readReg64 .x14 = 2#64 ∧
        ScanLoopSaved s sf) := by
  have hult2 : rem.ult 2#64 = false := by
    simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not]
    omega
  have hne1 : (rem == 1#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step
  have hpc98 : ((if (rem == 1#64) = true then fnBase + 1064#64 else fnBase + 152#64) : BitVec 64) =
      fnBase + 152#64 := by simp only [hne1, Bool.false_eq_true, ↓reduceIte]
  wp_step
  refine SepWP.done (by simp only [arm64_norm, hne1]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], rfl,
    by simp only [Reg.x8, arm64_norm, hx8],
    by simp only [Reg.x9, arm64_norm, hx9],
    by simp only [Reg.x10, arm64_norm, hx10],
    by simp only [Reg.x11, arm64_norm],
    by simp only [Reg.x12, arm64_norm],
    by simp only [Reg.x13, arm64_norm],
    by simp only [Reg.x14, arm64_norm, hx9, hx10, hult2, Bool.false_eq_true, ↓reduceIte],
    ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

private theorem scan_continue_to_7c_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0000#16 ∨ w = 0xFFFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x7c#64)
      s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = P ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = s.readReg64 .x9 ∧
        sf.readReg64 .x10 = s.readReg64 .x10 ∧
        sf.readReg64 .x11 = 65534#64 ∧
        sf.readReg64 .x13 = 65535#64 ∧
        sf.readReg64 .x14 = s.readReg64 .x14 ∧
        ScanLoopSaved s sf) := by
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  rcases hw with rfl | rfl
  · wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨by simp only [wp_norm, arm64_norm], rfl,
      by simp only [Reg.x8, arm64_norm], by simp only [Reg.x9, arm64_norm],
      by simp only [Reg.x10, arm64_norm], by simp only [Reg.x11, arm64_norm, hx11],
      by simp only [Reg.x13, arm64_norm, hx13], by simp only [Reg.x14, arm64_norm], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨by simp only [wp_norm, arm64_norm], rfl,
      by simp only [Reg.x8, arm64_norm], by simp only [Reg.x9, arm64_norm],
      by simp only [Reg.x10, arm64_norm], by simp only [Reg.x11, arm64_norm, hx11],
      by simp only [Reg.x13, arm64_norm, hx13], by simp only [Reg.x14, arm64_norm], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

private theorem scan_7c_last_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (s : State) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x7c#64)
    (hrun : s.status = .Running)
    (hx9 : s.readReg64 .x9 = 2#64)
    (hx14 : s.readReg64 .x14 = 2#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = P ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], rfl,
    by simp only [Reg.x21, arm64_norm],
    by simp only [Reg.x22, Reg.x19, arm64_norm],
    by simp only [Reg.x28, arm64_norm], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

private theorem scan_7c_more_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (ptr rem : BitVec 64) (s : State) (P : SepProp)
    (hrem_gt : 2 < rem.toNat) (hrem_hi : rem.toNat ≤ 512)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x7c#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx14 : s.readReg64 .x14 = 2#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
      s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = P ∧
        sf.readReg64 .x8 = ptr + 2#64 ∧
        sf.readReg64 .x9 = rem - 2#64 ∧
        sf.readReg64 .x10 = s.readReg64 .x10 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x13 = s.readReg64 .x13 ∧
        ScanLoopSaved s sf) := by
  have hsub_ne : (rem - 2#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; bv_omega
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hsub_ne]) (by simpa only [arm64_norm] using hrun) ?_
  refine ⟨by simp only [wp_norm, arm64_norm], rfl,
    by simp only [Reg.x8, arm64_norm, hx8, hx14],
    by simp only [Reg.x9, arm64_norm, hx9, hx14],
    by simp only [Reg.x10, arm64_norm],
    by simp only [Reg.x11, arm64_norm],
    by simp only [Reg.x13, arm64_norm],
    ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

private theorem scan_true_to_574_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x174#64)
      s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = P ∧
        ScanLoopSaved s sf) := by
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  rcases hw with rfl | rfl | rfl
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun)
      ⟨by simp only [wp_norm, arm64_norm], rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun)
      ⟨by simp only [wp_norm, arm64_norm], rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun)
      ⟨by simp only [wp_norm, arm64_norm], rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

private theorem scan_false_12_fffe_to_228_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw : w = 0x0001#16 ∨ w = 0x0002#16 ∨ w = 0xFFFE#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = P ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  rcases hw with rfl | rfl | rfl
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨by simp only [wp_norm, arm64_norm], rfl,
      by simp only [Reg.x21, arm64_norm],
      by simp only [Reg.x22, Reg.x19, arm64_norm],
      by simp only [Reg.x28, arm64_norm, hx28], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨by simp only [wp_norm, arm64_norm], rfl,
      by simp only [Reg.x21, arm64_norm],
      by simp only [Reg.x22, Reg.x19, arm64_norm],
      by simp only [Reg.x28, arm64_norm, hx28], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]
  · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
    refine ⟨by simp only [wp_norm, arm64_norm], rfl,
      by simp only [Reg.x21, arm64_norm],
      by simp only [Reg.x22, Reg.x19, arm64_norm],
      by simp only [Reg.x28, arm64_norm, hx28], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
        Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm, hx28]

private theorem scan_weird_le511_to_500_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hle511 : w.toNat ≤ 511)
    (hw0 : w ≠ 0x0000#16) (hw1 : w ≠ 0x0001#16) (hw2 : w ≠ 0x0002#16) (hw256 : w ≠ 0x0100#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
      s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = P ∧
        ScanLoopSaved s sf) := by
  have hc1 : (w.zeroExtend 32).sle 511#32 = true := by revert hle511; bv_kernel
  have hc2 : (w.zeroExtend 32 != 0#32) = true := by revert hw0; bv_kernel
  have hc3 : (w.zeroExtend 32 - 1#32).ult 2#32 = false := by revert hw0 hw1 hw2; bv_kernel
  have hc4 : (w.zeroExtend 32 == 256#32) = false := by revert hw256; bv_kernel
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hc1, hc2, hc3, hc4])
    (by simpa only [arm64_norm] using hrun)
    ⟨by simp only [wp_norm, arm64_norm], rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

private theorem scan_weird_gt511_to_500_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hgt511 : ¬(w.toNat ≤ 511))
    (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16) (hwfffe : w ≠ 0xFFFE#16) (hwffff : w ≠ 0xFFFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
      s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = P ∧
        ScanLoopSaved s sf) := by
  have hc1 : (w.zeroExtend 32).sle 511#32 = false := by revert hgt511; bv_kernel
  have hc2 : (w.zeroExtend 32).sle 65534#32 = true := by revert hwffff; bv_kernel
  have hc3 : (w.zeroExtend 32 == 512#32) = false := by revert hw512; bv_kernel
  have hc4 : (w.zeroExtend 32 == 65279#32) = false := by revert hwfeff; bv_kernel
  have hc5 : (w.zeroExtend 32 == 65534#32) = false := by revert hwfffe; bv_kernel
  send_ct2_fetches b trapHooks 552
  dsimp only [tripleRatchetProgAtExt, unchunkedCt1SentEkReceivedSendCt2Name,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  simp +singlePass only [Program.fnAddr_rebase, SendCt2StepsBudgetAux.fetch_withSvc _ noSyscalls] at *
  revert hpc
  generalize_entry
    (libsignalSessionCode.fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") =
      fnOffVal reverting [Program.fetch, SepWP]
  generalize b + BitVec.ofNat 64 fnOffVal = fnBase at *
  clear fnOffVal
  intro hpc
  apply sepWP_rebase_vmPreserved
  generalize_entry libsignalSessionCode = codeProg reverting [Program.fetch, SepWP]
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  refine SepWP.done (by simp only [arm64_norm, hc1, hc2, hc3, hc4, hc5])
    (by simpa only [arm64_norm] using hrun)
    ⟨by simp only [wp_norm, arm64_norm], rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Reg.x19, Reg.x20, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27,
      Reg.x28, Reg.x29, Reg.x30, State.sp, arm64_norm]

private theorem scan_weird_to_500_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (P : SepProp)
    (hw0 : w ≠ 0x0000#16) (hwffff : w ≠ 0xFFFF#16)
    (hw1 : w ≠ 0x0001#16) (hw2 : w ≠ 0x0002#16) (hwfffe : w ≠ 0xFFFE#16)
    (hw256 : w ≠ 0x0100#16) (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x100#64)
      s P
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = P ∧
        ScanLoopSaved s sf) := by
  by_cases hle511 : w.toNat ≤ 511
  · exact scan_weird_le511_to_500_vm w s P hle511 hw0 hw1 hw2 hw256 hpc hrun hx12
  · exact scan_weird_gt511_to_500_vm w s P hle511 hw512 hwfeff hwfffe hwffff hpc hrun hx11 hx12

private theorem scan_9c_false_exit_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hw0 : w ≠ 0x0000#16) (hwffff : w ≠ 0xFFFF#16)
    (hw256 : w ≠ 0x0100#16) (hw512 : w ≠ 0x0200#16) (hwfeff : w ≠ 0xFEFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  by_cases hw_le : w = 0x0001#16 ∨ w = 0x0002#16 ∨ w = 0xFFFE#16
  · exact scan_false_12_fffe_to_228_vm w s
      (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      hw_le hpc hrun hx11 hx12 hx28
  · push Not at hw_le
    rcases hw_le with ⟨hw1, hw2, hwfffe⟩
    refine SepWP.seq
      (scan_weird_to_500_vm w s
        (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
        hw0 hwffff hw1 hw2 hwfffe hw256 hw512 hwfeff hpc hrun hx11 hx12)
      fun sm Pm hpcm hrunm ⟨hvm1, hPm, hsaved1⟩ => ?_
    rw [hPm]
    refine SepWP.mono
      (scan_exit_500_vm sm Frame hb hpcm hrunm (hsaved1.x28.trans hx28)) ?_
    rintro sf Pf _ _ ⟨hvm2, hPf, hx21_sf, hx22_sf, hx28_sf, hsaved2⟩
    exact ⟨VmPreserved.trans hvm1 hvm2, hPf, hx21_sf, hx22_sf.trans hsaved1.x19, hx28_sf,
      hsaved1.trans hsaved2⟩

private theorem scan_9c_true_exit_vm {b : BitVec 64} {ext : String → Option (State → State)}
    (w : BitVec 16) (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hw : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x9c#64)
    (hrun : s.status = .Running)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx12 : s.readReg64 .x12 = w.zeroExtend 64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x1d8#64)
      s (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf) := by
  refine SepWP.seq
    (scan_true_to_574_vm w s
      (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      hw hpc hrun hx11 hx12)
    fun sm Pm hpcm hrunm ⟨hvm1, hPm, hsaved1⟩ => ?_
  rw [hPm]
  refine SepWP.mono (scan_exit_574_vm sm Frame hb hpcm hrunm) ?_
  rintro sf Pf _ _ ⟨hvm2, hPf, hsaved2⟩
  exact ⟨VmPreserved.trans hvm1 hvm2, hPf, hsaved1.trans hsaved2⟩

theorem scan_loop_false_vm_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = false)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
      s ((ptr ↦ₛ bs) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = ((ptr ↦ₛ bs) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf) := by
  match bs with
  | [] => exact absurd rfl hbs_ne
  | [_] => simp at hbs_mod
  | b0 :: b1 :: rest =>
    have hrem_lo : 2 ≤ rem.toNat := by
      subst hrem
      simp only [List.length_cons] at hbs_le ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    let w : BitVec 16 := (b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16
    have hw_eq : w = b1 ++ b0 := issue1275_word_eq b0 b1
    rw [pointsToBytes_pair_pointsTo16 ptr b0 b1 rest, ← hw_eq, sepConj_assoc]
    refine SepWP.seq
      (scan_head_step_vm ptr rem w s
        (((ptr + 2#64) ↦ₛ rest) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          Frame)
        hrem_lo hpc hrun hx8 hx9 hx10)
      fun sm Pm hpcm hrunm ⟨hvm_m, hPm, hx8_m, hx9_m, hx10_m, hx11_0, hx12_m, hx13_0, hx14_m, hsaved_m⟩ => ?_
    have hx11_m : sm.readReg64 .x11 = 65534#64 := hx11_0.trans hx11
    have hx13_m : sm.readReg64 .x13 = 65535#64 := hx13_0.trans hx13
    rw [hPm]
    by_cases hw_cont : w = 0x0000#16 ∨ w = 0xFFFF#16
    · have hflip_rest : issue1275NeedsFlip rest = false := by
        rwa [issue1275NeedsFlip_cons_cont b0 b1 rest hw_cont] at hflip
      refine SepWP.seq
        (scan_continue_to_7c_vm w sm
          ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗
            ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
            Frame))
          hw_cont hpcm hrunm hx11_m hx12_m hx13_m)
        fun s7c P7c hpc7c hrun7c ⟨hvm_7, hP7c, hx8_70, hx9_70, hx10_70, hx11_7, hx13_7, hx14_70, hsaved_70⟩ => ?_
      have hx8_7 : s7c.readReg64 .x8 = ptr := hx8_70.trans hx8_m
      have hx9_7 : s7c.readReg64 .x9 = rem := hx9_70.trans hx9_m
      have hx10_7 : s7c.readReg64 .x10 = 2#64 := hx10_70.trans hx10_m
      have hx14_7 : s7c.readReg64 .x14 = 2#64 := hx14_70.trans hx14_m
      have hsaved_7 : ScanLoopSaved s s7c := hsaved_m.trans hsaved_70
      have hvm_s7 : VmPreserved s s7c := VmPreserved.trans hvm_m hvm_7
      rw [hP7c]
      match rest with
      | [] =>
        have hrem2 : rem = 2#64 := by subst hrem; rfl
        refine SepWP.mono
          (scan_7c_last_vm s7c
            ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ []) ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              Frame))
            hpc7c hrun7c (hx9_7.trans hrem2) hx14_7 (hsaved_7.x28.trans hx28)) ?_
        rintro sf Pf _ _ ⟨hvm_f, hPf, hx21_f, hx22_f, hx28_f, hsaved_f⟩
        exact ⟨VmPreserved.trans hvm_s7 hvm_f, hPf, hx21_f, hx22_f.trans hsaved_7.x19, hx28_f,
          hsaved_7.trans hsaved_f⟩
      | [_] => simp at hbs_mod
      | b2 :: b3 :: rest' =>
        have hrest_ne : (b2 :: b3 :: rest') ≠ [] := List.cons_ne_nil _ _
        have hrest_mod : (b2 :: b3 :: rest').length % 2 = 0 := by
          simp only [List.length_cons] at hbs_mod ⊢; omega
        have hrest_le : (b2 :: b3 :: rest').length ≤ 512 := by
          simp only [List.length_cons] at hbs_le ⊢; omega
        have hrem_gt : 2 < rem.toNat := by
          subst hrem
          simp only [List.length_cons] at hbs_le ⊢
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hrem_hi : rem.toNat ≤ 512 := by
          subst hrem
          simp only [List.length_cons] at hbs_le ⊢
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hrem_sub : rem - 2#64 = BitVec.ofNat 64 (b2 :: b3 :: rest').length := by
          subst hrem
          simp only [List.length_cons] at hbs_le ⊢
          bv_omega
        refine SepWP.seq
          (scan_7c_more_vm ptr rem s7c
            ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              Frame))
            hrem_gt hrem_hi hpc7c hrun7c hx8_7 hx9_7 hx14_7)
          fun s88 P88 hpc88 hrun88 ⟨hvm_8, hP88, hx8_8, hx9_8, hx10_80, hx11_80, hx13_80, hsaved_80⟩ => ?_
        have hx10_8 : s88.readReg64 .x10 = 2#64 := hx10_80.trans hx10_7
        have hx11_8 : s88.readReg64 .x11 = 65534#64 := hx11_80.trans hx11_7
        have hx13_8 : s88.readReg64 .x13 = 65535#64 := hx13_80.trans hx13_7
        have hsaved_8 : ScanLoopSaved s s88 := hsaved_7.trans hsaved_80
        have hvm_s8 : VmPreserved s s88 := VmPreserved.trans hvm_s7 hvm_8
        have hP88' : P88 =
            ((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              ((ptr ↦₁₆ w) ∗ Frame) := by
          rw [hP88]
          sep_ac_rfl
        rw [hP88']
        refine SepWP.mono
          (scan_loop_false_vm_ok (ptr + 2#64) (b2 :: b3 :: rest') (rem - 2#64) s88
            ((ptr ↦₁₆ w) ∗ Frame)
            hb hrest_ne hrest_mod hrest_le hrem_sub hflip_rest hpc88 hrun88
            hx8_8 hx9_8 hx10_8 hx11_8 hx13_8 (hsaved_8.x28.trans hx28)) ?_
        rintro sf Pf _ _ ⟨hvm_f, hPf, hx21_f, hx22_f, hx28_f, hsaved_f⟩
        refine ⟨VmPreserved.trans hvm_s8 hvm_f, ?_, hx21_f, hx22_f.trans hsaved_8.x19, hx28_f,
          hsaved_8.trans hsaved_f⟩
        rw [hPf]
        sep_ac_rfl
    · push Not at hw_cont
      rcases hw_cont with ⟨hw0, hwffff⟩
      have hw_not_be : ¬(w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16) :=
        issue1275NeedsFlip_cons_false_not_be b0 b1 rest hflip
      push Not at hw_not_be
      rcases hw_not_be with ⟨hw256, hw512, hwfeff⟩
      have hpre_eq :
          ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗
            ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
            Frame)) =
          (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
            ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)) := by
        sep_ac_rfl
      conv => arg 4; rw [hpre_eq]
      refine SepWP.mono
        (scan_9c_false_exit_vm w sm ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)
          hb hw0 hwffff hw256 hw512 hwfeff hpcm hrunm hx11_m hx12_m (hsaved_m.x28.trans hx28)) ?_
      rintro sf Pf _ _ ⟨hvm_f, hPf, hx21_f, hx22_f, hx28_f, hsaved_f⟩
      refine ⟨VmPreserved.trans hvm_m hvm_f, ?_, hx21_f, hx22_f.trans hsaved_m.x19, hx28_f,
        hsaved_m.trans hsaved_f⟩
      rw [hPf]
      sep_ac_rfl

theorem scan_loop_false_pool_ok {b : BitVec 64} {ext : String → Option (State → State)}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hb : b &&& 4095#64 = 0#64)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = false)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 136#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 552#64)
      s ((ptr ↦ₛ bs) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          A.pool lim st sf ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine SepWP.seq
    (scan_loop_false_vm_ok ptr bs rem s (A.pool lim st s ∗ Frame)
      hb hbs_ne hbs_mod hbs_le hrem hflip hpc hrun hx8 hx9 hx10 hx11 hx13 hx28)
    fun sf Pf hpcm hrunm ⟨hvm, hPf, hx21, hx22, hx28', hsaved⟩ => ?_
  rw [hPf, ← A.pool_of_vmPreserved hvm]
  exact SepWP.done hpcm hrunm ⟨rfl, hx21, hx22, hx28', hsaved, hvm⟩

theorem scan_loop_true_vm_ok {b : BitVec 64} {ext : String → Option (State → State)}
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x88#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x1d8#64)
      s ((ptr ↦ₛ bs) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        VmPreserved s sf ∧
        Pf = ((ptr ↦ₛ bs) ∗ ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf) := by
  match bs with
  | [] => exact absurd rfl hbs_ne
  | [_] => simp at hbs_mod
  | b0 :: b1 :: rest =>
    have hrem_lo : 2 ≤ rem.toNat := by
      subst hrem
      simp only [List.length_cons] at hbs_le ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    let w : BitVec 16 := (b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16
    have hw_eq : w = b1 ++ b0 := issue1275_word_eq b0 b1
    rw [pointsToBytes_pair_pointsTo16 ptr b0 b1 rest, ← hw_eq, sepConj_assoc]
    refine SepWP.seq
      (scan_head_step_vm ptr rem w s
        (((ptr + 2#64) ↦ₛ rest) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          Frame)
        hrem_lo hpc hrun hx8 hx9 hx10)
      fun sm Pm hpcm hrunm ⟨hvm_m, hPm, hx8_m, hx9_m, hx10_m, hx11_0, hx12_m, hx13_0, hx14_m, hsaved_m⟩ => ?_
    have hx11_m : sm.readReg64 .x11 = 65534#64 := hx11_0.trans hx11
    have hx13_m : sm.readReg64 .x13 = 65535#64 := hx13_0.trans hx13
    rw [hPm]
    by_cases hw_cont : w = 0x0000#16 ∨ w = 0xFFFF#16
    · have hflip_rest : issue1275NeedsFlip rest = true := by
        rwa [issue1275NeedsFlip_cons_cont b0 b1 rest hw_cont] at hflip
      match rest with
      | [] =>
        dsimp only [issue1275NeedsFlip] at hflip_rest
        contradiction
      | [_] => simp at hbs_mod
      | b2 :: b3 :: rest' =>
        have hrest_ne : (b2 :: b3 :: rest') ≠ [] := List.cons_ne_nil _ _
        have hrest_mod : (b2 :: b3 :: rest').length % 2 = 0 := by
          simp only [List.length_cons] at hbs_mod ⊢; omega
        have hrest_le : (b2 :: b3 :: rest').length ≤ 512 := by
          simp only [List.length_cons] at hbs_le ⊢; omega
        have hrem_gt : 2 < rem.toNat := by
          subst hrem
          simp only [List.length_cons] at hbs_le ⊢
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hrem_hi : rem.toNat ≤ 512 := by
          subst hrem
          simp only [List.length_cons] at hbs_le ⊢
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        have hrem_sub : rem - 2#64 = BitVec.ofNat 64 (b2 :: b3 :: rest').length := by
          subst hrem
          simp only [List.length_cons] at hbs_le ⊢
          bv_omega
        refine SepWP.seq
          (scan_continue_to_7c_vm w sm
            ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              Frame))
            hw_cont hpcm hrunm hx11_m hx12_m hx13_m)
          fun s7c P7c hpc7c hrun7c ⟨hvm_7, hP7c, hx8_70, hx9_70, hx10_70, hx11_7, hx13_7, hx14_70, hsaved_70⟩ => ?_
        have hx8_7 : s7c.readReg64 .x8 = ptr := hx8_70.trans hx8_m
        have hx9_7 : s7c.readReg64 .x9 = rem := hx9_70.trans hx9_m
        have hx10_7 : s7c.readReg64 .x10 = 2#64 := hx10_70.trans hx10_m
        have hx14_7 : s7c.readReg64 .x14 = 2#64 := hx14_70.trans hx14_m
        have hsaved_7 : ScanLoopSaved s s7c := hsaved_m.trans hsaved_70
        have hvm_s7 : VmPreserved s s7c := VmPreserved.trans hvm_m hvm_7
        rw [hP7c]
        refine SepWP.seq
          (scan_7c_more_vm ptr rem s7c
            ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              Frame))
            hrem_gt hrem_hi hpc7c hrun7c hx8_7 hx9_7 hx14_7)
          fun s88 P88 hpc88 hrun88 ⟨hvm_8, hP88, hx8_8, hx9_8, hx10_80, hx11_80, hx13_80, hsaved_80⟩ => ?_
        have hx10_8 : s88.readReg64 .x10 = 2#64 := hx10_80.trans hx10_7
        have hx11_8 : s88.readReg64 .x11 = 65534#64 := hx11_80.trans hx11_7
        have hx13_8 : s88.readReg64 .x13 = 65535#64 := hx13_80.trans hx13_7
        have hsaved_8 : ScanLoopSaved s s88 := hsaved_7.trans hsaved_80
        have hvm_s8 : VmPreserved s s88 := VmPreserved.trans hvm_s7 hvm_8
        have hP88' : P88 =
            ((ptr + 2#64) ↦ₛ (b2 :: b3 :: rest')) ∗
              ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
              ((ptr ↦₁₆ w) ∗ Frame) := by
          rw [hP88]
          sep_ac_rfl
        rw [hP88']
        refine SepWP.mono
          (scan_loop_true_vm_ok (ptr + 2#64) (b2 :: b3 :: rest') (rem - 2#64) s88
            ((ptr ↦₁₆ w) ∗ Frame)
            hb hrest_ne hrest_mod hrest_le hrem_sub hflip_rest hpc88 hrun88
            hx8_8 hx9_8 hx10_8 hx11_8 hx13_8) ?_
        rintro sf Pf _ _ ⟨hvm_f, hPf, hsaved_f⟩
        refine ⟨VmPreserved.trans hvm_s8 hvm_f, ?_, hsaved_8.trans hsaved_f⟩
        rw [hPf]
        sep_ac_rfl
    · have hw_be : w = 0x0100#16 ∨ w = 0x0200#16 ∨ w = 0xFEFF#16 :=
        issue1275NeedsFlip_cons_true_be b0 b1 rest hflip hw_cont
      have hpre_eq :
          ((ptr ↦₁₆ w) ∗ (((ptr + 2#64) ↦ₛ rest) ∗
            ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
            Frame)) =
          (((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
            ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)) := by
        sep_ac_rfl
      conv => arg 4; rw [hpre_eq]
      refine SepWP.mono
        (scan_9c_true_exit_vm w sm ((ptr ↦₁₆ w) ∗ ((ptr + 2#64) ↦ₛ rest) ∗ Frame)
          hb hw_be hpcm hrunm hx11_m hx12_m) ?_
      rintro sf Pf _ _ ⟨hvm_f, hPf, hsaved_f⟩
      refine ⟨VmPreserved.trans hvm_m hvm_f, ?_, hsaved_m.trans hsaved_f⟩
      rw [hPf]
      sep_ac_rfl

theorem scan_loop_true_pool_ok {b : BitVec 64} {ext : String → Option (State → State)}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hb : b &&& 4095#64 = 0#64)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = true)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 136#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 472#64)
      s ((ptr ↦ₛ bs) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          A.pool lim st sf ∗ Frame) ∧
        ScanLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine SepWP.seq
    (scan_loop_true_vm_ok ptr bs rem s (A.pool lim st s ∗ Frame)
      hb hbs_ne hbs_mod hbs_le hrem hflip hpc hrun hx8 hx9 hx10 hx11 hx13)
    fun sf Pf hpcm hrunm ⟨hvm, hPf, hsaved⟩ => ?_
  rw [hPf, ← A.pool_of_vmPreserved hvm]
  exact SepWP.done hpcm hrunm ⟨rfl, hsaved, hvm⟩

/-! ## Fixed-Base Segment 2 (`+136 → +552`) -/

/-- Fixed-base (`tripleRatchetProgAtExt b ext`) budget-threaded Segment 2 (`+136 → +552`):
    scans `es[1536..2048)` for the libcrux issue-1275 halfword bound and conditionally allocates
    and byte-swaps a 2080-byte workspace, updating `A.pool lim stCost` to
    `A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost)`. -/
theorem send_ct2_scan_to_628_wpp {b : BitVec 64} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (x : UnchunkedSendCt2Ghost F) (stCost : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hb : b &&& 4095#64 = 0#64)
    (hFit : FitsEvents M lim stCost (sendCt2FlipAllocEvents x.st.es))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 552#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp := by
  have hlen512 : ((x.st.es.drop 1536).take 512).length = 512 := by
    rw [List.length_take, List.length_drop, hes_len]; rfl
  have hbs_ne : (x.st.es.drop 1536).take 512 ≠ [] := by
    intro hnil; rw [hnil] at hlen512; contradiction
  have hbs_mod : ((x.st.es.drop 1536).take 512).length % 2 = 0 := by rw [hlen512]
  have hbs_le : ((x.st.es.drop 1536).take 512).length ≤ 512 := by omega
  have hrem_eq : (512#64 : BitVec 64) = BitVec.ofNat 64 ((x.st.es.drop 1536).take 512).length := by
    rw [hlen512]
  let logCell : SepProp :=
    (b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64
  have hpre_split : ∀ (P_pool : SepProp),
      ((esPtr ↦ₛ x.st.es) ∗ logCell ∗
        P_pool ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) =
      (((esPtr + 1536#64) ↦ₛ ((x.st.es.drop 1536).take 512)) ∗
        logCell ∗
        P_pool ∗
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
    intro P_pool
    rw [es_scan_split esPtr x.st.es hes_len]
    sep_ac_rfl
  by_cases hflip : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = false
  · refine SepWPp.of_sepWP
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 552#64) ?_
    change SepWP _ _ _ ((esPtr ↦ₛ x.st.es) ∗ logCell ∗
      A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) _
    rw [hpre_split (A.pool lim stCost st)]
    refine SepWP.mono
      (scan_loop_false_pool_ok A lim stCost
        (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hb hbs_ne hbs_mod hbs_le hrem_eq hflip hpc hrun hx8 hx9 hx10 hx11 hx13 hx28) ?_
    rintro sf Pf hpc_sf hrun_sf ⟨hPf, hx21_sf, hx22_sf, hx28_sf, hsaved, _⟩
    have hwork : (esPtr ↦ₛ x.st.es) ⊢ sendCt2EsWorkAt A.repAlloc esPtr esPtr x.st.es := by
      unfold sendCt2EsWorkAt
      simp only [hflip, Bool.false_eq_true, ↓reduceIte]
      exact Entails.pure_right trivial (Entails.refl _)
    have hevs_nil : sendCt2FlipAllocEvents x.st.es = [] := by
      unfold sendCt2FlipAllocEvents
      simp only [hflip, Bool.false_eq_true, ↓reduceIte]
    have hPf_back : Pf ⊢
        sendCt2EsWorkAt A.repAlloc esPtr esPtr x.st.es ∗
          logCell ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) sf ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      change _ = (((esPtr + 1536#64) ↦ₛ ((x.st.es.drop 1536).take 512)) ∗ logCell ∗
        A.pool lim stCost sf ∗ _) at hPf
      rw [hPf, ← hpre_split (A.pool lim stCost sf), hevs_nil, M.stepEvents_nil]
      exact sepConj_mono_left hwork
    refine sepWPp_weaken_pre hPf_back ?_
    exact hcont sf esPtr hpc_sf hrun_sf
      (hsaved.sp.trans hsp) (hsaved.trace.trans htr) (hsaved.vregs.trans hvregs)
      (hsaved.x19.trans hx19) hsaved.x20
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx21_sf])
      (hx22_sf.trans hx19)
      hsaved.x23 hsaved.x24 hsaved.x25 hsaved.x26 hsaved.x27
      (by simp only [hflip, Bool.false_eq_true, ↓reduceIte, hx28_sf])
      hsaved.x29
  · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
      Bool.eq_true_of_not_eq_false hflip
    have hevs_alloc : sendCt2FlipAllocEvents x.st.es = rustAllocEvents 2080 1 := by
      unfold sendCt2FlipAllocEvents
      simp only [hflip_t, ↓reduceIte]
    have hFit2080 : FitsEvents M lim stCost (rustAllocEvents 2080 1) := by
      rwa [← hevs_alloc]
    refine SepWPp.of_sepWP
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 472#64) ?_
    change SepWP _ _ _ ((esPtr ↦ₛ x.st.es) ∗ logCell ∗
      A.pool lim stCost st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) _
    rw [hpre_split (A.pool lim stCost st)]
    refine SepWP.mono
      (scan_loop_true_pool_ok A lim stCost
        (esPtr + 1536#64) ((x.st.es.drop 1536).take 512) 512#64 st
        (((esPtr ↦ₛ (x.st.es.take 1536)) ∗ ((esPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        hb hbs_ne hbs_mod hbs_le hrem_eq hflip_t hpc hrun hx8 hx9 hx10 hx11 hx13) ?_
    rintro s5d8 P5d8 hpc_5d8 hrun_5d8 ⟨hP5d8, hsaved1, _⟩
    have hP5d8_eq : P5d8 =
        (esPtr ↦ₛ x.st.es) ∗ A.pool lim stCost s5d8 ∗ stackAt (s0.sp - 336#64) extHookStack ∗
          (logCell ∗ F_frame) := by
      change _ = (((esPtr + 1536#64) ↦ₛ ((x.st.es.drop 1536).take 512)) ∗ logCell ∗
        A.pool lim stCost s5d8 ∗ _) at hP5d8
      rw [hP5d8, ← hpre_split (A.pool lim stCost s5d8)]
      sep_ac_rfl
    rw [hP5d8_eq]
    refine send_ct2_5d8_to_604_wpp hA
      x stCost esPtr s0 s5d8 (logCell ∗ F_frame)
      hFit2080 hes_len hpc_5d8 hrun_5d8
      (hsaved1.sp.trans hsp) hsp_s0 (hsaved1.trace.trans htr)
      (hsaved1.vregs.trans hvregs) (hsaved1.x19.trans hx19) ?_
    intro s604 esWorkPtr hwork_ne hpc604 hrun604 hsp604 htr604 hvregs604
      hx8_604 hx19_604 hx20_604 hx22_604 hx23_604 hx24_604 hx25_604 hx26_604
      hx27_604 hx28_604 hx29_604
    refine SepWPp.of_sepWP
      (mid := (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 552#64) ?_
    have h2048_len : (x.st.es.take 2048).length = 2048 := by
      rw [List.length_take, hes_len]; rfl
    have h2048_ne : x.st.es.take 2048 ≠ [] := by
      intro hnil; rw [hnil] at h2048_len; contradiction
    have h2048_mod : (x.st.es.take 2048).length % 2 = 0 := by rw [h2048_len]
    have h2048_sum : (0#64 : BitVec 64).toNat + (x.st.es.take 2048).length = 2048 := by
      rw [h2048_len]; rfl
    have hsplit_swap :
        (esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s604 ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          (logCell ∗ F_frame) =
        (((esWorkPtr + 0#64) ↦ₛ (x.st.es.take 2048)) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) s604 ∗
          (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
            (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
            logCell ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)) := by
      rw [es_swap_split esWorkPtr x.st.es hes_len]
      sep_ac_rfl
    rw [hsplit_swap]
    refine SepWP.mono
      (swap_loop_pool_ok A lim (M.stepEvents (rustAllocEvents 2080 1) stCost)
        esWorkPtr (x.st.es.take 2048) 0#64 s604
        (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
          (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          logCell ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
        h2048_ne h2048_mod h2048_sum hpc604 hrun604 hx22_604 hx8_604) ?_
    rintro st' Pf2 hpc' hrun' ⟨hPf2, hx21', hsaved2, _⟩
    have hwork :
        (esPtr ↦ₛ x.st.es) ∗
          (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1 ⊢
          sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es := by
      unfold sendCt2EsWorkAt
      simp only [hflip_t, ↓reduceIte, RustCliAllocBudget.repAlloc_live]
      exact Entails.pure_right hwork_ne (Entails.of_eq (by sep_ac_rfl))
    have hPf2_reord :
        ((esWorkPtr + 0#64) ↦ₛ swapAdjacentPairs (x.st.es.take 2048)) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          (((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048)) ∗
            (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
            logCell ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) =
        (((esWorkPtr + 0#64) ↦ₛ swapAdjacentPairs (x.st.es.take 2048)) ∗
          ((esWorkPtr + 2048#64) ↦ₛ (x.st.es.drop 2048))) ∗
          (esPtr ↦ₛ x.st.es) ∗ A.live esWorkPtr 2080 1 ∗
          logCell ∗
          A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      sep_ac_rfl
    have hpost_ent : Pf2 ⊢
        sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          logCell ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) stCost) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗ F_frame := by
      rw [hPf2, hPf2_reord, es_swap_join esWorkPtr x.st.es hes_len, hevs_alloc]
      refine Entails.trans (Entails.of_eq (show _ =
        ((esPtr ↦ₛ x.st.es) ∗ (esWorkPtr ↦ₛ flipEndiannessOfEncapsulationStateBytes x.st.es) ∗
          A.live esWorkPtr 2080 1) ∗
          (logCell ∗
            A.pool lim (M.stepEvents (rustAllocEvents 2080 1) stCost) st' ∗
            stackAt (s0.sp - 336#64) extHookStack ∗ F_frame) by sep_ac_rfl)) ?_
      exact sepConj_mono_left hwork
    refine sepWPp_weaken_pre hpost_ent ?_
    exact hcont st' esWorkPtr hpc' hrun'
      (hsaved2.sp.trans hsp604) (hsaved2.trace.trans htr604) (hsaved2.vregs.trans hvregs604)
      (hsaved2.x19.trans hx19_604)
      ((hsaved2.x20.trans hx20_604).trans hsaved1.x20)
      (by simp only [hflip_t, ↓reduceIte, hx21'])
      (hsaved2.x22.trans hx22_604)
      ((hsaved2.x23.trans hx23_604).trans hsaved1.x23)
      ((hsaved2.x24.trans hx24_604).trans hsaved1.x24)
      ((hsaved2.x25.trans hx25_604).trans hsaved1.x25)
      ((hsaved2.x26.trans hx26_604).trans hsaved1.x26)
      ((hsaved2.x27.trans hx27_604).trans hsaved1.x27)
      (by simp only [hflip_t, ↓reduceIte, hsaved2.x28.trans hx28_604])
      ((hsaved2.x29.trans hx29_604).trans hsaved1.x29)

theorem send_ct2_scan_to_628_preEnv_wpp {b : BitVec 64} {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A lim ext)
    (x : UnchunkedSendCt2Ghost F) (st0 : M.σ) (esPtr : BitVec 64)
    (s0 st : State) (F_frame : SepProp)
    {Q Qp : State → SepProp → Prop}
    (hb : b &&& 4095#64 = 0#64)
    (hPre : FitsEnv M lim st0 (UnchunkedSendCt2PreEnv x))
    (hes_len : x.st.es.length = 2080)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 136#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx8 : st.readReg64 .x8 = esPtr + 1536#64)
    (hx9 : st.readReg64 .x9 = 512#64)
    (hx10 : st.readReg64 .x10 = 2#64)
    (hx11 : st.readReg64 .x11 = 65534#64)
    (hx13 : st.readReg64 .x13 = 65535#64)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx28 : st.readReg64 .x28 = bv% (2 ^ 64 - 1))
    (hcont : ∀ (st' : State) (esWorkPtr : BitVec 64),
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 552#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64) →
      st'.readReg64 .x22 = esWorkPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = st.readReg64 .x27 →
      st'.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)) →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (sendCt2EsWorkAt A.repAlloc esPtr esWorkPtr x.st.es ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents (sendCt2FlipAllocEvents x.st.es) st0) st' ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      ((esPtr ↦ₛ x.st.es) ∗
        ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
        A.pool lim st0 st ∗ stackAt (s0.sp - 336#64) extHookStack ∗ F_frame)
      Q Qp :=
  send_ct2_scan_to_628_wpp hA x st0 esPtr s0 st F_frame hb
    (fitsEvents_flipAlloc_of_preEnv hPre) hes_len hpc hrun hsp hsp_s0 htr hvregs
    hx8 hx9 hx10 hx11 hx13 hx19 hx28 hcont

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2ProofBudgetAux
