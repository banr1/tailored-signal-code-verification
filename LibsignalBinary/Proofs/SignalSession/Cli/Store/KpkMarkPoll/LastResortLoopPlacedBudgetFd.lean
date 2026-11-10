/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded Relocatable 37-Byte Chunk Loop for `KpkMarkPoll`

Proves `.keepsFs` `bcmp` transfer and `FdsGe3Closed`-threaded `kpk_bcmp_loop_20c_placed_fd` and
`kpk_bcmp_loop_20c_env_placed_fd` on Block `578` (`lsProg_578 H`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoVerification (
  IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks ls_externAt?_of_mem lsmpl
  lsρ
)
open CryptoVerification.LibsignalTripleRatchet (
  doReserveStackX extHookStack finishGrowStackX
)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded withLsCodeRoLoaded
)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession.Cli (
  CliBcmpCall DirGhost KpkMarkAns KpkMarkPollGhost KpkSeenOk KyberGhost ReadRule
  baseKeyEntry baseKeysName cliBcmpName cliBcmpSpec dirAt hasChunk keyName kpkMarkBoxAt
  kpkMarkOf kpkMarkOutAt
)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_578 blkPl_578 lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (CliPanicHooksPlaced)
open CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers (
  fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState fs_writeReg fs_writeReg32
  fs_writeReg64 fs_writeVReg128
)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers (
  baseKeyEntry_length bind_sepWPp_state_mark chunk_at_idx_eq cmp_37_hi_false cs_vregs
  cs_x19 cs_x20 cs_x21 cs_x22 cs_x23 cs_x24 cs_x25 cs_x26 cs_x27 cs_x28 cs_x29
  csel_min_37_eq epiloguePre hasChunk_false_of_all_ne hasChunk_true_of_match
  header3_entails_memRegion24 kpkMarkRoBundlePlaced kpkMinStk kpkSubMax
  restore_kpkMarkStack reusedStrAddrPlaced savedCalleeSlots
  sepWPp_conseq sepWPp_of_sepWP_lscro setWidth_32_setWidth_64 spAligned_sub_f0
  subStack_split vecU8Tail
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
  rustAllocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  FdsGe3Closed withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsFsPlaced dirPutSpecPlaced kpkMarkPollSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget (
  kpk_call_total_raw_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudget (
  kpkAppendPrePutEvents kpkAppendReserveEvents kpkReusedEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudgetFd (
  kpk_append_37c_placed_fd kpk_reused_230_placed_fd
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudget (
  KpkBcmpLoopEnv kpkMark_post_entails_placed
)

private theorem bv_sub_add_lit_kpk (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit_kpk BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64
  fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState
  fs_writeReg fs_writeReg32 fs_writeReg64 fs_writeVReg128
  State.fs_setStatus State.fs_appendTrace

local macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

local macro "kpk_pool_norm" : tactic =>
  `(tactic|
    try simp only [RustCliAllocBudget.pool_setPC, RustCliAllocBudget.pool_advancePC,
      RustCliAllocBudget.pool_setPState, RustCliAllocBudget.pool_writeReg64,
      RustCliAllocBudget.pool_writeReg32, RustCliAllocBudget.pool_writeReg,
      RustCliAllocBudget.pool_applyWriteback, RustCliAllocBudget.pool_setFpsr,
      RustCliAllocBudget.pool_orFpsr, RustCliAllocBudget.pool_nextOracle,
      RustCliAllocBudget.pool_stepExclOracle, RustCliAllocBudget.pool_stepExclLoop])

/-! ## 1. Postcondition & Stack-Restoration Unpack Helpers (`withFdsGe3Closed`) -/

theorem kpkMark_post_entails_placed_fd [LibsignalPlacement] {M : AllocCostModel} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop} {stk : Nat}
    (x : KpkMarkPollGhost) (st : M.σ) (s0 sf : State)
    (evs : List AllocEvent) (res : KpkMarkAns × KyberGhost)
    (hfds : FdsGe3Closed sf.fs)
    (hres : res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
        sf.trace = s0.trace ∧ MarkEnv s0.fs.files x evs) :
    (kpkMarkOutAt A.repAlloc x.out res.1 ∗
      dirAt A.repAlloc x.self res.2.oneTime ∗
      dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort ∗
      kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp stk) ⊢
      (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)).post (x, st) s0 sf := by
  dsimp only [withFdsGe3Closed]
  exact Entails.pure_right hfds (kpkMark_post_entails_placed x st s0 sf evs res hres)

theorem kpkMark_final_ext_placed_fd [LibsignalPlacement] {M : AllocCostModel} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) (hhi_stk : stk ≤ 2 ^ 64)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 sf : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (evs : List AllocEvent) (res : KpkMarkAns × KyberGhost)
    (hfds : FdsGe3Closed sf.fs)
    (hres : res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
        sf.trace = s0.trace ∧ MarkEnv s0.fs.files x evs) :
    (kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      (kpkMarkOutAt A.repAlloc x.out res.1 ∗
        dirAt A.repAlloc x.self res.2.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          savedCalleeSlots s0))) ⊢
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)).post
          (x, st) s0 sf := by
  refine sepConj_mono_right ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (restore_kpkMarkStack s0 hstk hhi_stk f0 f1 f2 f3 tmp32)))))))
    (kpkMark_post_entails_placed_fd x st s0 sf evs res hfds hres)

private theorem w0_cbnz_cond_false_p {v : BitVec 64} (hne : v.setWidth 32 ≠ 0#32) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 v) == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  apply hne
  have h32 := congrArg (BitVec.setWidth 32) h
  simpa [setWidth_32_setWidth_64] using h32

theorem kpkMark_final_sub_placed_fd [LibsignalPlacement] {M : AllocCostModel} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) (hhi_stk : stk ≤ 2 ^ 64)
    (x : KpkMarkPollGhost) (st : M.σ) (s0 sf : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (evs : List AllocEvent) (res : KpkMarkAns × KyberGhost)
    (hfds : FdsGe3Closed sf.fs)
    (hres : res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
        sf.trace = s0.trace ∧ MarkEnv s0.fs.files x evs) :
    (kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
      (kpkMarkOutAt A.repAlloc x.out res.1 ∗
        dirAt A.repAlloc x.self res.2.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          memRegion (s0.sp - 0xe8#64) 8 ∗
          memRegion (s0.sp - 0xe0#64) 8 ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          savedCalleeSlots s0))) ⊢
      kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (withFdsGe3Closed (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk)).post
          (x, st) s0 sf := by
  have hmin : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  rw [subStack_split s0.sp hext hmin,
      ProofLib.memRegion_eight (s0.sp - 0xe8#64),
      ProofLib.memRegion_eight (s0.sp - 0xe0#64)]
  kpk_sep_norm
  refine Entails.sepExists_elim fun f0 => Entails.sepExists_elim fun f1 => ?_
  refine Entails.trans (Entails.of_eq ?_)
    (kpkMark_final_ext_placed_fd hstk hhi_stk x st s0 sf wDot wR0 wR7 wM0 wM6 f0 f1 f2 f3 tmp32
      evs res hfds hres)
  sep_ac_rfl

/-! ## 2. `.keepsFs` `bcmp` Hook Transfer & Call Wrapper -/

/-- Extern `bcmp` hook transfer with `(withVmPreserved cliBcmpSpec).keepsFs`. -/
theorem kpk_bcmp_placed_ok_fd [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ cliBcmpName) (withVmPreserved cliBcmpSpec).keepsFs := by
  obtain ⟨f, hf, hok⟩ := hBcmp
  exact subroutine_ok_of_hookOk ((ls_externAt?_of_mem (by decide) hi hunmut).trans hf) hok

private theorem kpk_call_bcmp_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program}
    {callee ret_pc ret : BitVec 64}
    (hcall : subroutine_ok prog callee (withVmPreserved cliBcmpSpec).keepsFs)
    (xg : CliBcmpCall) (st : M.σ) (F : SepProp)
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = callee) (hrun : s.status = .Running) (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpre : P ⊢ cliBcmpSpec.pre xg s ∗ A.pool lim st s ∗ F)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.fs = s.fs →
      SepWPp prog ret sm (cliBcmpSpec.post xg s sm ∗ A.pool lim st sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  refine kpk_call_total_raw_placed hcall xg (A.pool lim st s ∗ F)
    hpc hrun hsp_align hlr hcrl ?_ ?_ ?_ ?_ ?_
  · dsimp only [Spec.keepsFs, withVmPreserved]
    exact hpre
  · intro sm R' hm
    dsimp only [Spec.keepsFs, withVmPreserved, cliBcmpSpec] at hm
    exact not_satisfies_false_sepConj hm
  · intro code sm R' hm
    dsimp only [Spec.keepsFs, withVmPreserved, cliBcmpSpec] at hm
    exact not_satisfies_false_sepConj hm
  · intro sm R' hm
    dsimp only [Spec.keepsFs, withVmPreserved, cliBcmpSpec] at hm
    exact not_satisfies_false_sepConj hm
  · intro sm hpcm hrunm hspm hcsm hcrlm
    dsimp only [Spec.keepsFs, withVmPreserved]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun hfsm => SepWPp.pure_elim fun hvm => ?_
    rw [← A.pool_of_vmPreserved (lim := lim) (st := st) hvm]
    exact sepWPp_conseq (Entails.of_eq (by sep_ac_rfl))
      (hnext sm hpcm hrunm hspm hcsm hcrlm hfsm)

/-! ## 3. 37-Byte Chunk Loop (`+512 .. +556`, `kpk_bcmp_loop_20c_placed_fd`) -/

set_option maxHeartbeats 1200000 in
/-- `FdsGe3Closed`-threaded 37-byte chunk `bcmp` loop at `+524 .. +556` (back-edge `+512 .. +520`),
exiting through `kpk_reused_230_placed_fd` or `kpk_append_37c_placed_fd`. -/
theorem kpk_bcmp_loop_20c_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {rd : ReadRule}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (x : KpkMarkPollGhost) (st : M.σ) (s0 : State)
    (wR0 wR7 : BitVec 64)
    (usedCap usedPtr : BitVec 64)
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64)
    (F : SepProp) {Q Qp : State → SepProp → Prop}
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok [])
    (hget2 : x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) = .ok seenBs)
    (hfit_reused : hasChunk seenBs (baseKeyEntry x.signedId x.baseKey) = true →
      FitsEvents M lim st (rustAllocEvents 15 1))
    (hfit_res : hasChunk seenBs (baseKeyEntry x.signedId x.baseKey) = false →
      FitsEvents M lim st (kpkAppendReserveEvents seenCap seenBs))
    (hfit_put : hasChunk seenBs (baseKeyEntry x.signedId x.baseKey) = false →
      FitsEnv M lim (M.stepEvents (kpkAppendPrePutEvents seenCap seenBs usedCap) st)
        (PutEnv x.kg.lastResort (baseKeysName x.id)
          (seenBs ++ baseKeyEntry x.signedId x.baseKey)))
    (hu_len : (baseKeyEntry x.signedId x.baseKey).length ≤ usedCap.toNat)
    (hu_lt : usedCap.toNat < 2 ^ 63) (hu_ptr : usedPtr ≠ 0#64)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : (baseKeysName x.id).length ≤ fileCap.toNat)
    (hf_lt : fileCap.toNat < 2 ^ 63) (hf_ptr : filePtr ≠ 0#64)
    (hk_res : ∀ (sf : State) (evs_loop : List AllocEvent) (P_f : SepProp)
        (ans : KpkMarkAns) (kg' : KyberGhost),
      (ans, kg') = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey →
      sf.trace = s0.trace →
      FdsGe3Closed sf.fs →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      KpkBcmpLoopEnv PutEnv x usedCap seenCap fileCap seenBs evs_loop →
      (P_f ⊢ kpkMarkOutAt A.repAlloc x.out ans ∗
        dirAt A.repAlloc x.self kg'.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) kg'.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        memRegion (s0.sp - 0xe8#64) 8 ∗
        memRegion (s0.sp - 0xe0#64) 8 ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        A.pool lim (M.stepEvents evs_loop st) sf ∗ F) →
      Q sf P_f) :
    ∀ (rem : Nat) (s : State) (idx : Nat) (pre suf : List (BitVec 8)) (P : SepProp),
      seenBs = pre ++ suf →
      pre.length = idx * 37 →
      suf.length = (rem + 1) * 37 →
      (∀ j < idx, (seenBs.drop (j * 37)).take 37 ≠ baseKeyEntry x.signedId x.baseKey) →
      s.pc = (blkPl_578).base + 524#64 →
      s.status = .Running →
      s.sp = s0.sp - 0xf0#64 →
      s.readReg64 .x29 = s0.sp - 0x60#64 →
      s.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl s.mem →
      FdsGe3Closed s.fs →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = x.fut →
      s.readReg64 .x20 = x.out →
      s.readReg64 .x21 = seenPtr + BitVec.ofNat 64 pre.length →
      s.readReg64 .x22 = BitVec.ofNat 64 seenBs.length →
      s.readReg64 .x24 = usedPtr →
      s.readReg64 .x25 = BitVec.ofNat 64 suf.length →
      s.readReg64 .x26 = x.self →
      s.readReg64 .x27 = seenCap →
      s.readReg64 .x28 = 37#64 →
      (P ⊢
        (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
        bytesAt false usedPtr (baseKeyEntry x.signedId x.baseKey) ∗
        vecU8Tail A.repAlloc usedCap usedPtr (baseKeyEntry x.signedId x.baseKey) ∗
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        epiloguePre s0 x ∗ A.pool lim st s ∗ F) →
      SepWPp (lsProg_578 H) (s0.readReg64 .lr) s P Q Qp := by
  let usedBs := baseKeyEntry x.signedId x.baseKey
  have hused37 : usedBs.length = 37 := baseKeyEntry_length x.signedId x.baseKey
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hbcmp := kpk_bcmp_placed_ok_fd (prog := lsProg_578 H) hBcmp
  have hreused := @kpk_reused_230_placed_fd _ M A lim H hFsAlloc
  have happend := @kpk_append_37c_placed_fd _ M A lim H PutEnv decStk getStk putStk hFsAlloc hP hPut
  dsimp only [lsProg_578] at hbcmp hreused happend
  clear hFsAlloc hP hBcmp hPut
  intro rem
  induction rem with
  | zero =>
    intro s idx pre suf P hseen hpre hsuf hall_pre hpc hrun hsp hfp htr hcrl hfds hvregs
      r19 r20 r21 r22 r24 r25 r26 r27 r28 hfoc
    change SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P Q Qp
    have _hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
    have hsuf_lt64 : suf.length < 2 ^ 64 := by rw [hseen, List.length_append] at hs_len; omega
    have hsuf_ge37 : 37 ≤ (BitVec.ofNat 64 suf.length).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuf_lt64]; omega
    have hcsel := csel_min_37_eq hsuf_ge37
    have _hhi_f := cmp_37_hi_false hsuf_ge37
    let chunk := suf.take 37
    have hchunk_eq : suf = chunk := (List.take_of_length_le (by omega)).symm
    have hchunk_len : chunk.length = 37 := by dsimp [chunk]; rw [List.length_take]; omega
    refine sepWPp_conseq hfoc ?_
    have hsplit_seen :
        bytesAt false seenPtr seenBs =
        (seenPtr ↦ₛ pre) ∗ ((seenPtr + BitVec.ofNat 64 pre.length) ↦ₛ chunk) := by
      rw [bytesAt]
      simp only [Bool.false_eq_true, ite_false]
      rw [hseen, hchunk_eq, pointsToBytes_append]
    rw [hsplit_seen, subStack_split s0.sp hext_le hhi]
    have hused_bytes : bytesAt false usedPtr usedBs = (usedPtr ↦ₛ usedBs) := rfl
    have hchunk_bytes :
        bytesAt false (seenPtr + BitVec.ofNat 64 pre.length) chunk =
        ((seenPtr + BitVec.ofNat 64 pre.length) ↦ₛ chunk) := rfl
    rw [hused_bytes]
    apply sepWPp_of_sepWP_lscro hcrl (mid := lsρ cliBcmpName)
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_bc
    apply bind_sepWPp_state_mark; intro st_bc
    have hsp_bc : st_bc.sp = s0.sp - 0xf0#64 := by dsimp only [st_bc]; (try kpk_norm)
    have hfs_bc : st_bc.fs = s.fs := by dsimp only [st_bc]; kpk_norm
    dsimp only [st_bc] at *
    refine kpk_call_bcmp_placed_fd hbcmp
      (CliBcmpCall.mk (seenPtr + BitVec.ofNat 64 pre.length) false chunk usedPtr false usedBs)
      st
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        (seenPtr ↦ₛ pre) ∗
        (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
        vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        epiloguePre s0 x ∗ F)
      (ret_pc := (blkPl_578).base + 556#64)
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_bc)
      (by kpk_norm)
      hcrl_bc
      (by
        dsimp only [cliBcmpSpec]
        simp only [hchunk_bytes, hused_bytes, hsp_bc, sepConj_assoc]
        refine Entails.pure_right ⟨by kpk_norm, by kpk_norm, ?_, by rw [hused37, hchunk_len]⟩ ?_
        · have : st_bc.readReg64 .x2 = 37#64 := by dsimp only [st_bc]; (try kpk_norm); try rfl
          rw [this, hchunk_len]; rfl
        · kpk_pool_norm
          kpk_sep_norm
          sep_focus)
      fun sm hpcm hrunm hspm hcsm hcrl_m hfsm => ?_
    have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_bc
    have hsm_fds : FdsGe3Closed sm.fs := by rw [hfsm, hfs_bc]; exact hfds
    have _hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
    simp only [cliBcmpSpec, hchunk_bytes, hused_bytes, hsp_bc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨heq_iff, htrm⟩ => ?_
    have hsm_tr : sm.trace = s0.trace := by rw [htrm]; kpk_norm
    by_cases hmatch : chunk = usedBs
    · have hw0 : (sm.readReg64 .x0).setWidth 32 = 0#32 := heq_iff.mpr hmatch
      have _hw0_beq : ((sm.readReg64 .x0).setWidth 32 == 0#32) = true := beq_iff_eq.mpr hw0
      have hhas : hasChunk seenBs usedBs = true :=
        hasChunk_true_of_match hused37 hseen hpre hsuf hmatch
      have hans : (KpkMarkAns.reused, x.kg) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1, hget2]
        have hmod0 : seenBs.length % usedBs.length = 0 := by
          rw [hseen, List.length_append, hpre, hsuf, hused37]; omega
        simp [usedBs, hmod0, hhas]
      apply sepWPp_of_sepWP_lscro hcrl_m (mid := (blkPl_578).base + 560#64)
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_230
      refine hreused x st s0 _ wR0 wR7
        usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr (baseKeysName x.id) _
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
          ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗ F)
        (hfit_reused hhas)
        hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
        hcrl_230
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcsm)]; kpk_norm))
        (by
          rw [hsplit_seen, hused_bytes]
          kpk_pool_norm
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_r P_r htr_r hfs_r hsp_r hcs_r hPr =>
          hk_res sf_r (kpkReusedEvents usedCap seenCap fileCap) P_r .reused x.kg
            hans htr_r
            (by simp only [wp_norm, arm64_norm] at hfs_r; rw [hfs_r]; exact hsm_fds)
            hsp_r hcs_r (KpkBcmpLoopEnv.of_reused hhas) <| by
              refine Entails.trans hPr ?_
              have hm_e8 := pointsTo64_entails_memRegion (s0.sp - 0xe8#64)
                (BitVec.ofNat 64 (baseKeysName x.id).length)
              have hm_e0 := pointsTo64_entails_memRegion (s0.sp - 0xe0#64) seenPtr
              have hm_c8 := header3_entails_memRegion24 (s0.sp - 0xc8#64)
                (s0.sp - 0xc0#64) (s0.sp - 0xb8#64) seenCap seenPtr
                (BitVec.ofNat 64 seenBs.length) (by bv_omega) (by bv_omega)
              have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
                (s0.sp - 0x78#64) (s0.sp - 0x70#64) usedCap usedPtr 37#64
                (by bv_omega) (by bv_omega)
              rw [subStack_split s0.sp hext_le hhi]
              kpk_sep_norm
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right
                      (sepConj_mono hm_e8
                        (sepConj_mono hm_e0
                          (sepConj_mono_right (sepConj_mono_right
                            (sepConj_mono hm_c8
                              (sepConj_mono_right (sepConj_mono_left hm_80))))))))))))))
              sep_focus
    · have hw0_ne : (sm.readReg64 .x0).setWidth 32 ≠ 0#32 := mt heq_iff.mp hmatch
      have _hw0_beq :
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false :=
        w0_cbnz_cond_false_p hw0_ne
      have hx25_sm : sm.readReg64 .x25 = 37#64 := by
        rw [(cs_x25 hcsm)]
        have : st_bc.readReg64 .x25 = BitVec.ofNat 64 suf.length := by dsimp only [st_bc]; kpk_norm
        rw [this, hsuf]
      have hx23_sm : sm.readReg64 .x23 = 37#64 := by
        rw [(cs_x23 hcsm)]
        have : st_bc.readReg64 .x23 =
            (if (37#64 : BitVec 64).ult (BitVec.ofNat 64 suf.length) then 37#64
             else BitVec.ofNat 64 suf.length) := by dsimp only [st_bc]; (try kpk_norm); try rfl
        rw [this, hcsel]
      have _hsub_zero : sm.readReg64 .x25 - sm.readReg64 .x23 = 0#64 := by
        rw [hx25_sm, hx23_sm]; rfl
      have hhas_f : hasChunk seenBs usedBs = false := by
        refine hasChunk_false_of_all_ne hused37
          (k := idx + 1) (by rw [hseen, List.length_append, hpre, hsuf]; omega) ?_
        intro j hj
        by_cases hlt_j : j < idx
        · exact hall_pre j hlt_j
        · have hjeq : j = idx := by omega
          subst hjeq
          rw [chunk_at_idx_eq hseen hpre]
          exact hmatch
      have hmod0 : seenBs.length % usedBs.length = 0 := by
        rw [hseen, List.length_append, hpre, hsuf, hused37]; omega
      have hseen32 : seenBs.length < 2 ^ 32 := hSeenOk seenBs hget2 hmod0 hhas_f
      have hans :
          (KpkMarkAns.ok,
            { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) (seenBs ++ usedBs) }) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1, hget2]
        simp [usedBs, hmod0, hhas_f]
      apply sepWPp_of_sepWP_lscro hcrl_m (mid := (blkPl_578).base + 892#64)
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_37c
      refine happend x st s0 _
        usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr (baseKeysName x.id) _
        ((reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
          ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
          ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗ F)
        hhi hlr_chg (hfit_res hhas_f) (hfit_put hhas_f)
        hused37 hu_len hu_lt hu_ptr hseen32 hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
        hcrl_37c
        (by simp only [wp_norm, arm64_norm]; exact hsm_fds)
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x22 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm)]; kpk_norm))
        (by
          rw [subStack_split s0.sp hext_le hhi, hsplit_seen, hused_bytes]
          kpk_pool_norm
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_a evs_put P_a htr_a hfds_a hsp_a hcs_a hput_a hPa =>
          hk_res sf_a (kpkAppendPrePutEvents seenCap seenBs usedCap ++ evs_put) P_a .ok
            { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) (seenBs ++ usedBs) }
            hans htr_a hfds_a hsp_a hcs_a (KpkBcmpLoopEnv.of_append hhas_f hput_a) <| by
              refine Entails.trans hPa ?_
              have hm_e8 := pointsTo64_entails_memRegion (s0.sp - 0xe8#64)
                (BitVec.ofNat 64 (baseKeysName x.id).length)
              have hm_e0 := pointsTo64_entails_memRegion (s0.sp - 0xe0#64) seenPtr
              have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
                (s0.sp - 0x78#64) (s0.sp - 0x70#64) usedCap usedPtr 37#64
                (by bv_omega) (by bv_omega)
              kpk_sep_norm
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right
                      (sepConj_mono hm_e8
                        (sepConj_mono hm_e0
                          (sepConj_mono_right (sepConj_mono_right
                            (sepConj_mono_right (sepConj_mono_right
                              (sepConj_mono_left hm_80))))))))))))))
              sep_focus
  | succ rem' ih =>
    intro s idx pre suf P hseen hpre hsuf hall_pre hpc hrun hsp hfp htr hcrl hfds hvregs
      r19 r20 r21 r22 r24 r25 r26 r27 r28 hfoc
    change SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s P Q Qp
    have _hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
    have hsuf_lt64 : suf.length < 2 ^ 64 := by rw [hseen, List.length_append] at hs_len; omega
    have hsuf_ge37 : 37 ≤ (BitVec.ofNat 64 suf.length).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuf_lt64]; omega
    have hcsel := csel_min_37_eq hsuf_ge37
    have hhi_f := cmp_37_hi_false hsuf_ge37
    let chunk := suf.take 37
    let rest := suf.drop 37
    have hchunk_len : chunk.length = 37 := by dsimp [chunk]; rw [List.length_take]; omega
    have hrest_len : rest.length = (rem' + 1) * 37 := by
      dsimp [rest]; rw [List.length_drop]; omega
    refine sepWPp_conseq hfoc ?_
    have hsplit_seen :
        bytesAt false seenPtr seenBs =
        (seenPtr ↦ₛ pre) ∗ ((seenPtr + BitVec.ofNat 64 pre.length) ↦ₛ chunk) ∗
          ((seenPtr + BitVec.ofNat 64 pre.length + 37#64) ↦ₛ rest) := by
      rw [bytesAt]
      simp only [Bool.false_eq_true, ite_false]
      rw [hseen, ← List.take_append_drop 37 suf, pointsToBytes_append, pointsToBytes_append,
        hchunk_len]
    rw [hsplit_seen, subStack_split s0.sp hext_le hhi]
    have hused_bytes : bytesAt false usedPtr usedBs = (usedPtr ↦ₛ usedBs) := rfl
    have hchunk_bytes :
        bytesAt false (seenPtr + BitVec.ofNat 64 pre.length) chunk =
        ((seenPtr + BitVec.ofNat 64 pre.length) ↦ₛ chunk) := rfl
    rw [hused_bytes]
    have _hcsel2 : (if (37#64).ult (BitVec.ofNat 64 ((rem' + 1 + 1) * 37)) = true
        then 37#64 else BitVec.ofNat 64 ((rem' + 1 + 1) * 37)) = 37#64 := hsuf ▸ hcsel
    have _hhi_f2 : (BitVec.ofNat 64 ((rem' + 1 + 1) * 37)).ult 37#64 = false := hsuf ▸ hhi_f
    apply sepWPp_of_sepWP_lscro hcrl (mid := lsρ cliBcmpName)
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_bc
    apply bind_sepWPp_state_mark; intro st_bc
    have hsp_bc : st_bc.sp = s0.sp - 0xf0#64 := by dsimp only [st_bc]; (try kpk_norm)
    have hfs_bc : st_bc.fs = s.fs := by dsimp only [st_bc]; kpk_norm
    dsimp only [st_bc] at *
    refine kpk_call_bcmp_placed_fd hbcmp
      (CliBcmpCall.mk (seenPtr + BitVec.ofNat 64 pre.length) false chunk usedPtr false usedBs)
      st
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        (seenPtr ↦ₛ pre) ∗
        ((seenPtr + BitVec.ofNat 64 pre.length + 37#64) ↦ₛ rest) ∗
        (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
        vecU8Tail A.repAlloc usedCap usedPtr usedBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        epiloguePre s0 x ∗ F)
      (ret_pc := (blkPl_578).base + 556#64)
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_bc)
      (by kpk_norm)
      hcrl_bc
      (by
        dsimp only [cliBcmpSpec]
        simp only [hchunk_bytes, hused_bytes, hsp_bc, sepConj_assoc]
        refine Entails.pure_right ⟨by kpk_norm, by kpk_norm, ?_, by rw [hused37, hchunk_len]⟩ ?_
        · have : st_bc.readReg64 .x2 = 37#64 := by dsimp only [st_bc]; (try kpk_norm); try rfl
          rw [this, hchunk_len]; rfl
        · kpk_pool_norm
          kpk_sep_norm
          sep_focus)
      fun sm hpcm hrunm hspm hcsm hcrl_m hfsm => ?_
    have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_bc
    have hsm_fds : FdsGe3Closed sm.fs := by rw [hfsm, hfs_bc]; exact hfds
    have _hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
    simp only [cliBcmpSpec, hchunk_bytes, hused_bytes, hsp_bc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨heq_iff, htrm⟩ => ?_
    have hsm_tr : sm.trace = s0.trace := by rw [htrm]; kpk_norm
    by_cases hmatch : chunk = usedBs
    · have hw0 : (sm.readReg64 .x0).setWidth 32 = 0#32 := heq_iff.mpr hmatch
      have _hw0_beq : ((sm.readReg64 .x0).setWidth 32 == 0#32) = true := beq_iff_eq.mpr hw0
      have hhas : hasChunk seenBs usedBs = true :=
        hasChunk_true_of_match hused37 hseen hpre hsuf hmatch
      have hans : (KpkMarkAns.reused, x.kg) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1, hget2]
        have hmod0 : seenBs.length % usedBs.length = 0 := by
          rw [hseen, List.length_append, hpre, hsuf, hused37]; omega
        simp [usedBs, hmod0, hhas]
      apply sepWPp_of_sepWP_lscro hcrl_m (mid := (blkPl_578).base + 560#64)
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_230
      refine hreused x st s0 _ wR0 wR7
        usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr (baseKeysName x.id) _
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
          ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗ F)
        (hfit_reused hhas)
        hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
        hcrl_230
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcsm)]; kpk_norm))
        (by
          rw [hsplit_seen, hused_bytes]
          kpk_pool_norm
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_r P_r htr_r hfs_r hsp_r hcs_r hPr =>
          hk_res sf_r (kpkReusedEvents usedCap seenCap fileCap) P_r .reused x.kg
            hans htr_r
            (by simp only [wp_norm, arm64_norm] at hfs_r; rw [hfs_r]; exact hsm_fds)
            hsp_r hcs_r (KpkBcmpLoopEnv.of_reused hhas) <| by
              refine Entails.trans hPr ?_
              have hm_e8 := pointsTo64_entails_memRegion (s0.sp - 0xe8#64)
                (BitVec.ofNat 64 (baseKeysName x.id).length)
              have hm_e0 := pointsTo64_entails_memRegion (s0.sp - 0xe0#64) seenPtr
              have hm_c8 := header3_entails_memRegion24 (s0.sp - 0xc8#64)
                (s0.sp - 0xc0#64) (s0.sp - 0xb8#64) seenCap seenPtr
                (BitVec.ofNat 64 seenBs.length) (by bv_omega) (by bv_omega)
              have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
                (s0.sp - 0x78#64) (s0.sp - 0x70#64) usedCap usedPtr 37#64
                (by bv_omega) (by bv_omega)
              rw [subStack_split s0.sp hext_le hhi]
              kpk_sep_norm
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right
                      (sepConj_mono hm_e8
                        (sepConj_mono hm_e0
                          (sepConj_mono_right (sepConj_mono_right
                            (sepConj_mono hm_c8
                              (sepConj_mono_right (sepConj_mono_left hm_80))))))))))))))
              sep_focus
    · have hw0_ne : (sm.readReg64 .x0).setWidth 32 ≠ 0#32 := mt heq_iff.mp hmatch
      have _hw0_beq :
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false :=
        w0_cbnz_cond_false_p hw0_ne
      have hx25_sm : sm.readReg64 .x25 = BitVec.ofNat 64 suf.length := by
        rw [(cs_x25 hcsm)]; kpk_norm
      have hx23_sm : sm.readReg64 .x23 = 37#64 := by
        rw [(cs_x23 hcsm)]; kpk_norm
      have hx21_sm : sm.readReg64 .x21 = seenPtr + BitVec.ofNat 64 pre.length := by
        rw [(cs_x21 hcsm)]; kpk_norm
      have _hsub_rest : sm.readReg64 .x25 - sm.readReg64 .x23 = BitVec.ofNat 64 rest.length := by
        rw [hx25_sm, hx23_sm]
        apply BitVec.eq_of_toNat_eq
        have hs1 : (BitVec.ofNat 64 suf.length).toNat = suf.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuf_lt64]
        have hs2 : (BitVec.ofNat 64 rest.length).toNat = rest.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have h37 : (37#64 : BitVec 64).toNat = 37 := rfl
        rw [BitVec.toNat_sub_of_le
          ((BitVec.le_def (x := 37#64) (y := BitVec.ofNat 64 suf.length)).mpr hsuf_ge37),
          hs1, h37, hs2]
        omega
      have hrest_ne0_1 : (BitVec.ofNat 64 rest.length == 0#64) = false := by
        apply beq_false_of_ne
        intro h0
        have ht := congrArg BitVec.toNat h0
        have hs2 : (BitVec.ofNat 64 rest.length).toNat = rest.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hs2] at ht
        change rest.length = 0 at ht
        omega
      have _hrest_ne0_2 : (BitVec.ofNat 64 ((rem' + 1) * 37) == 0#64) = false :=
        hrest_len ▸ hrest_ne0_1
      have _hadd_pre : sm.readReg64 .x21 + sm.readReg64 .x23 =
          seenPtr + BitVec.ofNat 64 (pre ++ chunk).length := by
        rw [hx21_sm, hx23_sm, List.length_append, hchunk_len, BitVec.ofNat_add]; bv_omega
      clear hx25_sm hx23_sm hx21_sm
      apply sepWPp_of_sepWP_lscro hcrl_m (mid := (blkPl_578).base + 524#64)
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hcrl_next
      refine ih _ (idx + 1) (pre ++ chunk) rest _
        (by rw [hseen, ← List.take_append_drop 37 suf, List.append_assoc])
        (by rw [List.length_append, hpre, hchunk_len]; omega)
        hrest_len
        (by
          intro j hj
          by_cases hlt_j : j < idx
          · exact hall_pre j hlt_j
          · have hjeq : j = idx := by omega
            subst hjeq
            rw [chunk_at_idx_eq hseen hpre]
            exact hmatch)
        (by kpk_norm)
        (by kpk_norm)
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
        hcrl_next
        (by simp only [wp_norm, arm64_norm]; exact hsm_fds)
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
        (by simp only [wp_norm, arm64_norm, *])
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x22 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcsm)]; kpk_norm))
        (by simp only [wp_norm, arm64_norm, *])
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm)]; kpk_norm))
        (by
          rw [subStack_split s0.sp hext_le hhi, hsplit_seen, hused_bytes]
          kpk_pool_norm
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)

/-- `FitsEnv`-bundled wrapper around `kpk_bcmp_loop_20c_placed_fd` discharging `hfit_reused`,
`hfit_res`, and `hfit_put` from a single `FitsEnv M lim st (KpkBcmpLoopEnv ...)`. -/
theorem kpk_bcmp_loop_20c_env_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {rd : ReadRule}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk : Nat}
    (hFsAlloc : AllocContractsFsPlaced A lim H)
    (hP : CliPanicHooksPlaced H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec).keepsFs)
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542)
      (withFdsGe3Closed (dirPutSpecPlaced A lim PutEnv putStk)))
    (x : KpkMarkPollGhost) (st : M.σ) (s0 : State)
    (wR0 wR7 : BitVec 64)
    (usedCap usedPtr : BitVec 64)
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64)
    (F : SepProp) {Q Qp : State → SepProp → Prop}
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok [])
    (hget2 : x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) = .ok seenBs)
    (hfit : FitsEnv M lim st (KpkBcmpLoopEnv PutEnv x usedCap seenCap fileCap seenBs))
    (hu_len : (baseKeyEntry x.signedId x.baseKey).length ≤ usedCap.toNat)
    (hu_lt : usedCap.toNat < 2 ^ 63) (hu_ptr : usedPtr ≠ 0#64)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : (baseKeysName x.id).length ≤ fileCap.toNat)
    (hf_lt : fileCap.toNat < 2 ^ 63) (hf_ptr : filePtr ≠ 0#64)
    (hk_res : ∀ (sf : State) (evs_loop : List AllocEvent) (P_f : SepProp)
        (ans : KpkMarkAns) (kg' : KyberGhost),
      (ans, kg') = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey →
      sf.trace = s0.trace →
      FdsGe3Closed sf.fs →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      KpkBcmpLoopEnv PutEnv x usedCap seenCap fileCap seenBs evs_loop →
      (P_f ⊢ kpkMarkOutAt A.repAlloc x.out ans ∗
        dirAt A.repAlloc x.self kg'.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) kg'.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        memRegion (s0.sp - 0xe8#64) 8 ∗
        memRegion (s0.sp - 0xe0#64) 8 ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        A.pool lim (M.stepEvents evs_loop st) sf ∗ F) →
      Q sf P_f) :
    ∀ (rem : Nat) (s : State) (idx : Nat) (pre suf : List (BitVec 8)) (P : SepProp),
      seenBs = pre ++ suf →
      pre.length = idx * 37 →
      suf.length = (rem + 1) * 37 →
      (∀ j < idx, (seenBs.drop (j * 37)).take 37 ≠ baseKeyEntry x.signedId x.baseKey) →
      s.pc = (blkPl_578).base + 524#64 →
      s.status = .Running →
      s.sp = s0.sp - 0xf0#64 →
      s.readReg64 .x29 = s0.sp - 0x60#64 →
      s.trace = s0.trace →
      LibsignalCodeRoLoaded lsmpl s.mem →
      FdsGe3Closed s.fs →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = x.fut →
      s.readReg64 .x20 = x.out →
      s.readReg64 .x21 = seenPtr + BitVec.ofNat 64 pre.length →
      s.readReg64 .x22 = BitVec.ofNat 64 seenBs.length →
      s.readReg64 .x24 = usedPtr →
      s.readReg64 .x25 = BitVec.ofNat 64 suf.length →
      s.readReg64 .x26 = x.self →
      s.readReg64 .x27 = seenCap →
      s.readReg64 .x28 = 37#64 →
      (P ⊢
        (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
        bytesAt false usedPtr (baseKeyEntry x.signedId x.baseKey) ∗
        vecU8Tail A.repAlloc usedCap usedPtr (baseKeyEntry x.signedId x.baseKey) ∗
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        epiloguePre s0 x ∗ A.pool lim st s ∗ F) →
      SepWPp (lsProg_578 H) (s0.readReg64 .lr) s P Q Qp :=
  kpk_bcmp_loop_20c_placed_fd hFsAlloc hP hBcmp hPut x st s0 wR0 wR7
    usedCap usedPtr seenCap seenPtr seenBs fileCap filePtr F
    hhi hsp_align hSeenOk hlr_chg hget1 hget2
    (KpkBcmpLoopEnv.fits_reused hfit)
    (KpkBcmpLoopEnv.fits_reserve hfit)
    (KpkBcmpLoopEnv.fits_put hfit)
    hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr hk_res

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudgetFd
