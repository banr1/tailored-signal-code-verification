/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.Branches -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip

/-!
# Budget-Threaded Relocatable Symbolic Verification of `save_identity::{closure#0}`

Proves budget-threaded `Ok []` and `Ok (some k)` branches and main entry contracts on Block `565`
(`lsProg_565 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (IdentityKey PublicKey)
open CryptoGames.LibsignalSessionApi (IdentityChange)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Getters (publicKeyEqSpec)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec protocolAddressAt vecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles LibsignalCodeRoLoaded sepWPp_seq_lscro withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs (decodeIdentityKey decodeIdentityKey_serialize)
open CryptoVerification.RecordCodecsBinary (identityKeyResultAt)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdFileWf IdPeerAns IdPollGhost ReadRule dirAt getResultAt idSaveBoxAt idSaveOf pathOf)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_565 blkPl_565)
open CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
  (calleeSavedVRegs_writeVReg128_0 decStk_le_saveSubMax eor_publicKey_eq_idSaveOf
   eqStk_le_saveSubMax fs_advancePC fs_applyWriteback fs_setMem fs_setPC fs_setPState fs_writeReg
   fs_writeReg32 fs_writeReg64 fs_writeVReg128 getResultAt_ok_unpack getStk_le_saveSubMax
   hookStk_le_saveSubMax ispoll_sp_eqs layoutOk_u8_of_ne_zero memRegion_32_eq_pkChunksAt
   memRegion_bound_of_pointsTo64 offAfterDecode offAfterDealloc offAfterEq offAfterGet offOkTail
   overlap7View1 pkChunksAt pk_pack_hi8 pk_pack_lo32 pk_pack_mid16 pointsToBytes_32_exists_pkChunksAt
   protocolAddressAt_borrow s48_byte7_entails_memRegion16 s48_split_byte7 saveMinStk
   savePollFrameSlots saveSubMax savedCalleeSlots sepWPp_conseq slot90_bytes32_16_collapse
   slot90_pk88_to_32_16 slot90_words4_collapse spAligned_sub_d0 stackAt_savePoll_eq
   stackAt_sub_split vecU8Tail vecU8_free_ne vecU8_free_zero)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget
   RustLayoutOk rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents publicKeySerializeSpecX)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodeRawSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced dirGetSpecPlaced dirPutStrSpecPlaced idSavePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (CliIdSavePollEnv CliIdSaveTailEnv ispoll_branch_err_placed ispoll_call_dealloc_placed
   ispoll_call_decode_placed ispoll_call_dirGet_placed ispoll_call_publicKeyEq_placed
   ispoll_ok_tail_190_placed)

export LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (CliIdSaveTailEnv CliIdSavePollEnv)

section Placed

attribute [local irreducible] Program.fetch Program.externAt? FitsEvents
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] calleeSavedVRegs_writeVReg128_0
  offAfterGet offAfterDecode offAfterDealloc offAfterEq offOkTail

private theorem rustLayoutOk_u8_of_ne_zero {cap : BitVec 64}
    (hc : cap ≠ 0#64) (hlt : cap.toNat < 2 ^ 63) :
    RustLayoutOk cap.toNat 1 :=
  ⟨layoutOk_u8_of_ne_zero hc hlt, by decide⟩

private theorem vecU8_free_ne_budget {M : AllocCostModel} (A : RustCliAllocBudget M)
    {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    (hc : cap ≠ 0#64) (hlen : bs.length ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    (bytesAt false ptr bs ∗ vecU8Tail A.repAlloc cap ptr bs) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  rw [← A.repAlloc_live_norm]
  exact vecU8_free_ne A.repAlloc hc hlen hcap

/-! ## 1. `Ok []` Branch on Block `565` -/

theorem ispoll_branch_ok_nil_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hSer : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hPut : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost) (st0 : M.σ) (evsGet : List AllocEvent)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s48 s56w : BitVec 64)
    (hpc : s.pc = (blkPl_565).base + offAfterGet)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hgr : Except.ok [] = x.peers.get rd s0.fs.files x.call.call.addr.val.name)
    (hFitSer : ∀ evsFree, FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents (evsGet ++ evsFree) st0) PublicKeySerializeEnv)
    (hFitPut : ∀ evsFree, FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents ((evsGet ++ evsFree) ++ publicKeySerializeEvents) st0)
        (PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize))
    (hSaveEvs : ∀ evsFree evsPut, FreeOnlyEvs evsFree →
      PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize evsPut →
      SaveEnv s0.fs.files x ((evsGet ++ evsFree) ++ publicKeySerializeEvents ++ evsPut)) :
    SepWPp ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (getResultAt A.repAlloc (s0.sp - 0x90#64) (.ok []) ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evsGet st0) s ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
        ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk).post (x, st0) s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk).onPanic (x, st0) s0 sf) := by
  have hDealloc := dealloc_lscro_of_cli (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hC (by decide)
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  dsimp only [offAfterGet] at hpc
  conv =>
    arg 4
    rw [getResultAt_ok_unpack A.repAlloc s0.sp []]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  refine SepWPp.pure_elim fun ⟨hlen, hcap_lt, hptr⟩ => ?_
  ispoll_rw_pre (s48_split_byte7 s0.sp s48 s56w)
  conv => arg 4; simp only [sepConj_assoc]
  by_cases hcap0 : cap = 0#64
  · subst hcap0
    ispoll_fold_pre (vecU8_free_zero A.repAlloc ptr hlen)
    conv => arg 4; simp only [emp_sepConj, sepConj_assoc]
    apply sepWPp_seq_lscro (mid := (blkPl_565).base + offOkTail) hinv
    wp_steps_sync_pool ((blkPl_565).base + offOkTail)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_tail
    ispoll_fold_pre (slot90_words4_collapse s0.sp okTagVec 0#64 ptr (BitVec.ofNat 64 ([] : List (BitVec 8)).length))
    ispoll_fold_pre (s48_byte7_entails_memRegion16 s0.sp s48 (s56w.extractLsb' 0 8)
      (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8) (s56w.extractLsb' 24 8)
      (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8) (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8))
    have hFitSer0 : FitsEnv M lim (M.stepEvents evsGet st0) PublicKeySerializeEnv := by
      simpa only [List.append_nil] using hFitSer [] FreeOnlyEvs.nil
    have hFitPut0 :
        FitsEnv M lim (M.stepEvents (evsGet ++ publicKeySerializeEvents) st0)
          (PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize) := by
      simpa only [List.append_nil] using hFitPut [] FreeOnlyEvs.nil
    have hSave0 : ∀ evsPut,
        PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize evsPut →
        SaveEnv s0.fs.files x (evsGet ++ publicKeySerializeEvents ++ evsPut) := by
      intro evsPut hPutEv
      simpa only [List.append_nil] using hSaveEvs [] evsPut FreeOnlyEvs.nil hPutEv
    refine sepWPp_conseq ?_
      (ispoll_ok_tail_190_placed (pathOk := pathOk) hSer hPut hstk hhi x st0 evsGet
        (.ok []) none .newOrUnchanged
        c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s48 (s56w.extractLsb' 0 8)
        (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, hvregs])
        (by wp_norm_goal) hinv_tail
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm]; rfl)
        (by wp_norm_goal) rfl hnlen hclen hgr rfl hFitSer0 hFitPut0 hSave0)
    exact Entails.of_eq (by sep_ac_rfl)
  · ispoll_fold_pre (vecU8_free_ne_budget A (ptr := ptr) hcap0 hlen hcap_lt)
    conv => arg 4; simp only [sepConj_assoc]
    apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_dealloc
    conv =>
      arg 4
      rw [stackAt_sub_split (s0.sp - 0xd0#64) (hookStk_le_saveSubMax getStk putStk) hsub_hi]
      simp only [sepConj_assoc]
    refine ispoll_call_dealloc_placed (ret_pc := (blkPl_565).base + offAfterDealloc)
      hDealloc ptr cap.toNat (M.stepEvents evsGet st0) ?ispollF
      (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
      hinv_dealloc
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
      (rustLayoutOk_u8_of_ne_zero hcap0 hcap_lt)
      ?ispollPre ?_
    case ispollPre => ispoll_close_frame
    intro sm1 hpc1 hrun1 hsp1 hcs1 hinv1 htr1
    simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
      hsp, htr, hx19, hx20, hx24, hx29, hvregs] at hpc1 hsp1 htr1 hcs1
    rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, hx24_1, hx25_1, hx26_1, _, _, hx29_1, hvregs_1⟩
    have hsp_al1 : sm1.spAligned = true := by
      simp only [State.spAligned] at hsp_align ⊢
      rwa [hsp1, ← hsp]
    rw [← M.stepEvents_append]
    conv => arg 4; simp only [wp_norm, arm64_norm, hsp, hsp1]
    ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (hookStk_le_saveSubMax getStk putStk) hsub_hi).symm
    apply sepWPp_seq_lscro (mid := (blkPl_565).base + offOkTail) hinv1
    wp_steps_sync_pool ((blkPl_565).base + offOkTail)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_tail
    ispoll_fold_pre (slot90_words4_collapse s0.sp okTagVec cap ptr (BitVec.ofNat 64 ([] : List (BitVec 8)).length))
    ispoll_fold_pre (s48_byte7_entails_memRegion16 s0.sp s48 (s56w.extractLsb' 0 8)
      (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8) (s56w.extractLsb' 24 8)
      (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8) (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8))
    have hfo : FreeOnlyEvs (rustDeallocEvents cap.toNat 1) := FreeOnlyEvs.singleton 1 cap.toNat
    refine sepWPp_conseq ?_
      (ispoll_ok_tail_190_placed (pathOk := pathOk) hSer hPut hstk hhi x st0
        (evsGet ++ rustDeallocEvents cap.toNat 1) (.ok []) none .newOrUnchanged
        c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s48 (s56w.extractLsb' 0 8)
        (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_goal) (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, hvregs_1])
        (by wp_norm_goal) hinv_tail
        (by wp_norm_goal) (by wp_norm_goal) (by wp_norm_goal)
        (by simp only [wp_norm, arm64_norm]; rfl)
        (by wp_norm_goal) rfl hnlen hclen hgr rfl
        (hFitSer _ hfo) (hFitPut _ hfo) (hSaveEvs _ · hfo))
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## 2. `Ok (some k)` Branch and Entry Theorems on Block `565` -/

private theorem pk_hh16_p (h1 : BitVec 16) (b2 : BitVec 8) :
    (h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32 =
      h1.zeroExtend 32 ||| (b2.zeroExtend 32 <<< 16) := by
  ext i hi; interval_cases i <;> simp

private theorem bv_shr32_tr32_tr16_p (v : BitVec 64) :
    ((v >>> 32).truncate 32).truncate 16 = (v >>> 32).truncate 16 := by
  ext i hi; interval_cases i <;> simp

private theorem abstract_state_p {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (k : ∀ s' : State, s' = s → SepWPp prog ret s' P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  k s rfl

private theorem ispoll_branch_ok_some_220_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hSer : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hPut : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hEq : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 212)
      (withLsCodeRoLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost) (st0 : M.σ) (evsPre : List AllocEvent) (k : IdentityKey)
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s56w : BitVec 64)
    (w0 : BitVec 32) (h1 : BitVec 16) (b2 : BitVec 8) (d3 d4 d5 : BitVec 64) (b6 : BitVec 8)
    (hpk_eq : ∀ a : BitVec 64, (a ↦ₛ k.publicKey.bytes.toList) = pkChunksAt a w0 h1 b2 d3 d4 d5 b6)
    (hpc : s.pc = (blkPl_565).base + offAfterDealloc)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx22 : s.readReg64 .x22 = d4)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx25 : s.readReg64 .x25 = okTagVec)
    (hx26 : s.readReg64 .x26 = 1#64)
    (hx27 : s.readReg64 .x27 =
      w0.zeroExtend 64 ||| ((h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32).zeroExtend 64 <<< 32)
    (hx28 : s.readReg64 .x28 = d3)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hgr : Except.ok k.serialize = x.peers.get rd s0.fs.files x.call.call.addr.val.name)
    (hans : IdPeerAns (.ok k.serialize) (.ok (some k)))
    (hFitSer : FitsEnv M lim (M.stepEvents evsPre st0) PublicKeySerializeEnv)
    (hFitPut : FitsEnv M lim (M.stepEvents (evsPre ++ publicKeySerializeEvents) st0)
      (PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize))
    (hSaveEvs : ∀ evsPut,
      PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize evsPut →
      SaveEnv s0.fs.files x (evsPre ++ publicKeySerializeEvents ++ evsPut)) :
    SepWPp ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0x90#64) 32 ∗
        memRegion (s0.sp - 0x70#64) 16 ∗
        A.pool lim (M.stepEvents evsPre st0) s ∗
        ((s0.sp - 0xa0#64) ↦₆₄ d5) ∗
        ((s0.sp - 0x98#64) ↦₈ b6) ∗
        overlap7View1 (s0.sp - 0x97#64)
          (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8) (s56w.extractLsb' 24 8)
          (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8) (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8) ∗
        lsLogOff ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk).post (x, st0) s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk).onPanic (x, st0) s0 sf) := by
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  dsimp only [offAfterDealloc] at hpc
  ispoll_rw_pre (memRegion_32_eq_pkChunksAt (s0.sp - 0x90#64))
  conv =>
    arg 4
    unfold pkChunksAt idSaveBoxAt
    simp only [ispoll_sp_eqs, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro u0
  apply SepWPp.exists_elim; intro u1
  apply SepWPp.exists_elim; intro u2
  apply SepWPp.exists_elim; intro u3
  apply SepWPp.exists_elim; intro u4
  apply SepWPp.exists_elim; intro u5
  apply SepWPp.exists_elim; intro u6
  apply sepWPp_seq_lscro (mid := lsmpl.base 212) hinv
  wp_steps_sync_pool (lsmpl.base 212)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_eq
  have hrew_pk :
      (((s0.sp - 0x90#64) ↦₃₂ (w0.zeroExtend 64 ||| ((h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32).zeroExtend 64 <<< 32).truncate 32) ∗
        ((s0.sp - 0x8c#64) ↦₁₆ ((((w0.zeroExtend 64 ||| ((h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32).zeroExtend 64 <<< 32) >>> 32)).truncate 32).truncate 16) ∗
        ((s0.sp - 0x8a#64) ↦₈ (((w0.zeroExtend 64 ||| ((h1.zeroExtend 64 ||| (b2.zeroExtend 32 <<< 16).zeroExtend 64).truncate 32).zeroExtend 64 <<< 32) >>> 48)).truncate 8) ∗
        ((s0.sp - 0x89#64) ↦₆₄ d3) ∗ ((s0.sp - 0x81#64) ↦₆₄ d4) ∗ ((s0.sp - 0x79#64) ↦₆₄ d5) ∗
        ((s0.sp - 0x71#64) ↦₈ b6)) =
      ((s0.sp - 0x90#64) ↦ₛ k.publicKey.bytes.toList) := by
    rw [pk_hh16_p h1 b2, bv_shr32_tr32_tr16_p, pk_pack_lo32 w0 h1 b2, pk_pack_mid16 w0 h1 b2,
      pk_pack_hi8 w0 h1 b2, hpk_eq (s0.sp - 0x90#64)]
    unfold pkChunksAt
    simp only [ispoll_sp_eqs]
  ispoll_rw_pre hrew_pk
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (eqStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_publicKeyEq_placed (A := A) (lim := lim)
    (ret_pc := (blkPl_565).base + offAfterEq)
    hEq (s0.sp - 0x90#64) k.publicKey x.call.call.keyA x.call.call.key.publicKey
    (M.stepEvents evsPre st0) ?ispollF3
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    hinv_eq
    (by wp_norm_goal) (by wp_norm_goal)
    ?ispollPre3 ?_
  case ispollPre3 => ispoll_close_frame
  intro sm3 hpc3 hrun3 hsp3 hcs3 hinv3 hx0_3 htr3
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp, htr, hx19, hx20, hx22, hx24, hx25, hx26, hx27, hx28, hx29, hvregs]
    at hpc3 hsp3 htr3 hx0_3 hcs3
  rcases hcs3 with ⟨hx19_3, hx20_3, _, _, _, hx24_3, _, _, _, _, hx29_3, hvregs_3⟩
  have hsp_al3 : sm3.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp3, ← hsp]
  conv => arg 4; simp only [State.sp, wp_norm, arm64_norm, hsp, hsp3]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (eqStk_le_saveSubMax getStk putStk) hsub_hi).symm
  ispoll_fold_pre (slot90_bytes32_16_collapse s0.sp k.publicKey.bytes.toList_length)
  ispoll_fold_pre (s48_byte7_entails_memRegion16 s0.sp d5 b6
    (s56w.extractLsb' 8 8) (s56w.extractLsb' 16 8) (s56w.extractLsb' 24 8)
    (s56w.extractLsb' 32 8) (s56w.extractLsb' 40 8) (s56w.extractLsb' 48 8) (s56w.extractLsb' 56 8))
  apply sepWPp_seq_lscro (mid := (blkPl_565).base + offOkTail) hinv3
  wp_steps_sync_pool ((blkPl_565).base + offOkTail)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_tail
  apply abstract_state_p; intro s4 hs4
  conv => arg 4; rw [← hs4]
  let chg : IdentityChange := if k = x.call.call.key then .newOrUnchanged else .replacedExisting
  have hpc4 : s4.pc = (blkPl_565).base + offOkTail := by rw [hs4]; wp_norm_goal
  have hrun4 : s4.status = .Running := by rw [hs4]; wp_norm_lhs
  have hsp4 : s4.sp = s0.sp - 0xd0#64 := by rw [hs4]; wp_norm_goal
  have hsp_al4 : s4.spAligned = true := by rw [hs4]; wp_norm_lhs
  have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
    rw [hs4]; simp only [wp_norm, arm64_norm, hvregs_3]
  have htr4 : s4.trace = s0.trace := by rw [hs4]; wp_norm_goal
  have hinv4 : LibsignalCodeRoLoaded lsmpl s4.mem := by rw [hs4]; exact hinv_tail
  have hx19_4 : s4.readReg64 .x19 = x.call.fut := by rw [hs4]; wp_norm_goal
  have hx20_4 : s4.readReg64 .x20 = x.call.out := by rw [hs4]; wp_norm_goal
  have hx24_4 : s4.readReg64 .x24 = x.self := by rw [hs4]; wp_norm_goal
  have hx26_4 : (s4.readReg64 .x26).truncate 32 =
      (if chg == .replacedExisting then 1#32 else 0#32) := by
    have htr_xor : ∀ (P : Prop) [Decidable P],
        BitVec.truncate 32 ((if P then 1#64 else 0#64) ^^^ 4294967297#64) =
          BitVec.truncate 32 (if P then 1#64 else 0#64) ^^^ 1#32 := by
      intro P _; split_ifs <;> rfl
    rw [hs4]; simp only [chg, wp_norm, arm64_norm]
    rw [htr_xor]
    exact eor_publicKey_eq_idSaveOf k x.call.call.key
  have hx29_4 : s4.readReg64 .x29 = s0.sp - 0x60#64 := by rw [hs4]; wp_norm_goal
  have hc4 : idSaveOf (.ok (some k)) x.call.call.key = .ok chg := by
    by_cases h : k = x.call.call.key <;> simp [idSaveOf, chg, h]
  clear hs4 hinv_tail
  refine sepWPp_conseq ?_
    (ispoll_ok_tail_190_placed (pathOk := pathOk) hSer hPut hstk hhi x st0 evsPre
      (.ok k.serialize) (some k) chg
      c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 d5 b6
      hpc4 hrun4 hsp4 hsp_al4 hvregs4 htr4 hinv4
      hx19_4 hx20_4 hx24_4 hx26_4 hx29_4 hc4 hnlen hclen hgr hans
      hFitSer hFitPut hSaveEvs)
  exact Entails.of_eq (by unfold idSaveBoxAt; ispoll_ac_rfl)

theorem ispoll_branch_ok_some_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hSer : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hPut : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hDec : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 18)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (identityKeyDecodeRawSpec A))))
    (hEq : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 212)
      (withLsCodeRoLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hstk : saveMinStk getStk putStk ≤ stk)
    (hhi : stk ≤ 2 ^ 64)
    {s0 s : State} (x : IdPollGhost) (st0 : M.σ) (evsGet : List AllocEvent)
    (k : IdentityKey) {bs : List (BitVec 8)}
    (c1 c2 c3 c4 c5 c6 c7 c15 : BitVec 8)
    (s16 : BitVec 64) (s24 : BitVec 8) (s32 : BitVec 64) (s40 : BitVec 8)
    (s48 s56w : BitVec 64)
    (hpc : s.pc = (blkPl_565).base + offAfterGet)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xd0#64)
    (hsp_align : s.spAligned = true)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (htr : s.trace = s0.trace)
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = x.call.fut)
    (hx20 : s.readReg64 .x20 = x.call.out)
    (hx24 : s.readReg64 .x24 = x.self)
    (hx29 : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32)
    (hclen : x.peers.changed.length < 2 ^ 32)
    (hser : k.serialize = bs)
    (hgr : Except.ok bs = x.peers.get rd s0.fs.files x.call.call.addr.val.name)
    (hFitSer : ∀ evsFree, FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents (evsGet ++ evsFree) st0) PublicKeySerializeEnv)
    (hFitPut : ∀ evsFree, FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents ((evsGet ++ evsFree) ++ publicKeySerializeEvents) st0)
        (PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize))
    (hSaveEvs : ∀ evsFree evsPut, FreeOnlyEvs evsFree →
      PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize evsPut →
      SaveEnv s0.fs.files x ((evsGet ++ evsFree) ++ publicKeySerializeEvents ++ evsPut)) :
    SepWPp ((blkPC_565).rebase (blkPl_565).base H) (s0.readReg64 .lr) s
      (getResultAt A.repAlloc (s0.sp - 0x90#64) (.ok bs) ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.peers ∗
        memRegion x.call.out 48 ∗
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evsGet st0) s ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
        stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
        memRegion (s0.sp - 0xd0#64) 8 ∗
        overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
        ((s0.sp - 0xc1#64) ↦₈ c15) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
        ((s0.sp - 0xb8#64) ↦₈ s24) ∗
        memRegion (s0.sp - 0xb7#64) 7 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
        ((s0.sp - 0xa8#64) ↦₈ s40) ∗
        memRegion (s0.sp - 0xa7#64) 7 ∗
        ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
        ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
        savedCalleeSlots s0)
      (fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk).post (x, st0) s0 sf))
      (fun sf P_f => P_f ⊢ (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk).onPanic (x, st0) s0 sf) := by
  subst hser
  have hDealloc := dealloc_lscro_of_cli (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hC (by decide)
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    have : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
    unfold saveMinStk at this; omega
  have hlen33 : k.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize]
  have hans : IdPeerAns (.ok k.serialize) (.ok (some k)) := by
    cases hcons : k.serialize with
    | nil => simp [hcons] at hlen33
    | cons b rest => exact ⟨k, rfl, hcons⟩
  dsimp only [offAfterGet] at hpc
  conv =>
    arg 4
    rw [getResultAt_ok_unpack A.repAlloc s0.sp k.serialize]
    simp only [bytesAt, Bool.false_eq_true, ite_false,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  refine SepWPp.pure_elim fun ⟨hlen, hcap_lt, hptr⟩ => ?_
  have hcap_ne : cap ≠ 0#64 := by
    intro hc0; subst hc0; simp [hlen33] at hlen
  have hb33 : BitVec.ofNat 64 k.serialize.length = 33#64 := by rw [hlen33]
  conv => arg 4; simp only [hb33]
  apply sepWPp_seq_lscro (mid := lsmpl.base 18) hinv
  wp_steps_sync_pool (lsmpl.base 18)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_dec
  ispoll_fold_pre (slot90_words4_collapse s0.sp okTagVec cap ptr 33#64)
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (decStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_decode_placed (lim := lim) (ret_pc := (blkPl_565).base + offAfterDecode)
    hDec { bytesA := ptr, bytes := k.serialize, ret := s0.sp - 0x90#64 }
    (M.stepEvents evsGet st0) ?ispollF1
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    hinv_dec
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, hlen33]) (by wp_norm_goal)
    ?ispollPre1 ?_
  case ispollPre1 => ispoll_close_frame
  intro sm1 hpc1 hrun1 hsp1 hcs1 hinv1 htr1
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp, htr, hx19, hx20, hx24, hx29, hvregs] at hpc1 hsp1 htr1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, _, hx23_1, hx24_1, _, _, _, _, hx29_1, hvregs_1⟩
  have hsp_al1 : sm1.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp1, ← hsp]
  obtain ⟨w0, h1, b2, d3, d4, d5, b6, hpk_eq⟩ :=
    pointsToBytes_32_exists_pkChunksAt k.publicKey.bytes.toList_length
  conv => arg 4; simp only [State.sp, wp_norm, arm64_norm, hsp, hsp1]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (decStk_le_saveSubMax getStk putStk) hsub_hi).symm
  conv =>
    arg 4
    rw [decodeIdentityKey_serialize k]
    dsimp only [identityKeyResultAt, vecResultAt]
    simp only [ispoll_sp_eqs, hpk_eq, pkChunksAt, sepConj_assoc]
  ispoll_rw_pre (s48_split_byte7 s0.sp s48 s56w)
  conv => arg 4; simp only [sepConj_assoc]
  apply sepWPp_seq_lscro (mid := lsρ lsRustDeallocSymCli) hinv1
  wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_dealloc
  have hfree_vec : ((ptr ↦ₛ k.serialize) ∗ vecU8Tail A.repAlloc cap ptr k.serialize) ⊢
      A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
    simpa only [bytesAt, Bool.false_eq_true, ite_false] using
      vecU8_free_ne_budget A (ptr := ptr) hcap_ne hlen hcap_lt
  ispoll_fold_pre hfree_vec
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (hookStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  refine ispoll_call_dealloc_placed (ret_pc := (blkPl_565).base + offAfterDealloc)
    hDealloc ptr cap.toNat (M.stepEvents evsGet st0) ?ispollF2
    (by wp_norm_goal) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_goal)
    hinv_dealloc
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm])
    (rustLayoutOk_u8_of_ne_zero hcap_ne hcap_lt)
    ?ispollPre2 ?_
  case ispollPre2 => ispoll_close_frame
  intro sm2 hpc2 hrun2 hsp2 hcs2 hinv2 htr2
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm,
    hsp1, htr1, hx19_1, hx20_1, hx21_1, hx23_1, hx24_1, hx29_1, hvregs_1] at hpc2 hsp2 htr2 hcs2
  rcases hcs2 with ⟨hx19_2, hx20_2, _, hx22_2, _, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  have hsp_al2 : sm2.spAligned = true := by
    simp only [State.spAligned] at hsp_align ⊢
    rwa [hsp2, ← hsp]
  rw [← M.stepEvents_append]
  conv => arg 4; simp only [State.sp, wp_norm, arm64_norm, hsp, hsp1, hsp2]
  have hpk88_fold :
      (((s0.sp - 0x90#64) ↦₆₄ okTagVec) ∗
        ((s0.sp - 0x88#64) ↦₃₂ w0) ∗ ((s0.sp - 0x84#64) ↦₁₆ h1) ∗ ((s0.sp - 0x82#64) ↦₈ b2) ∗
        ((s0.sp - 0x81#64) ↦₆₄ d3) ∗ ((s0.sp - 0x79#64) ↦₆₄ d4) ∗ ((s0.sp - 0x71#64) ↦₆₄ d5) ∗
        ((s0.sp - 0x69#64) ↦₈ b6) ∗ memRegion (s0.sp - 0x68#64) 8) ⊢
      memRegion (s0.sp - 0x90#64) 32 ∗ memRegion (s0.sp - 0x70#64) 16 := by
    have h := slot90_pk88_to_32_16 s0.sp okTagVec w0 h1 b2 d3 d4 d5 b6
    unfold pkChunksAt at h
    simpa only [ispoll_sp_eqs, sepConj_assoc] using h
  ispoll_fold_pre hpk88_fold
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (hookStk_le_saveSubMax getStk putStk) hsub_hi).symm
  have hfo : FreeOnlyEvs (rustDeallocEvents cap.toNat 1) := FreeOnlyEvs.singleton 1 cap.toNat
  refine sepWPp_conseq ?_
    (ispoll_branch_ok_some_220_placed (rd := rd) (pathOk := pathOk) hSer hPut hEq hstk hhi x st0
      (evsGet ++ rustDeallocEvents cap.toNat 1) k
      c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s56w
      w0 h1 b2 d3 d4 d5 b6 hpk_eq
      hpc2 hrun2 hsp2 hsp_al2 hvregs_2 htr2 hinv2
      hx19_2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
      hnlen hclen hgr hans
      (hFitSer _ hfo) (hFitPut _ hfo) (hSaveEvs _ · hfo))
  exact Entails.of_eq (by ispoll_ac_rfl)

private theorem sepWPp_post_mono_p {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q1 Q2 Qp1 Qp2 : State → SepProp → Prop}
    (hQ : ∀ sf P_f, Q1 sf P_f → Q2 sf P_f)
    (hQp : ∀ sf P_f, Qp1 sf P_f → Qp2 sf P_f)
    (hw : SepWPp prog ret s P Q1 Qp1) :
    SepWPp prog ret s P Q2 Qp2 := fun R hm hL => by
  rcases hw R hm hL with ⟨sf, hsteps, ⟨hpc_f, hrun_f, P_f, hm_f, hq⟩ | ⟨hst, P_f, hm_f, hqp⟩ | hoom⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc_f, hrun_f, P_f, hm_f, hQ sf P_f hq⟩⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inl ⟨hst, P_f, hm_f, hQp sf P_f hqp⟩)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

/-- Generic-envelope relocatable `[LibsignalPlacement]` verification of `save_identity::{closure#0}`
(Block `565`). -/
theorem idSavePoll_placed_ok_of_deps_core_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hSer : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hGet : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hPut : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hDec : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 18)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (identityKeyDecodeRawSpec A))))
    (hEq : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 212)
      (withLsCodeRoLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hFitGet : ∀ F0 x st0, FitsEnv M lim st0 (SaveEnv F0 x) →
      FitsEnv M lim st0 (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hSaveErr : ∀ F0 x evsGet,
      x.peers.get rd F0 x.call.call.addr.val.name = .error () →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      SaveEnv F0 x evsGet)
    (hFitSer : ∀ F0 x bs st0 evsGet evsFree,
      FitsEnv M lim st0 (SaveEnv F0 x) →
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents (evsGet ++ evsFree) st0) PublicKeySerializeEnv)
    (hFitPut : ∀ F0 x bs st0 evsGet evsFree,
      FitsEnv M lim st0 (SaveEnv F0 x) →
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents ((evsGet ++ evsFree) ++ publicKeySerializeEvents) st0)
        (PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize))
    (hSaveOk : ∀ F0 x bs evsGet evsFree evsPut,
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize evsPut →
      SaveEnv F0 x ((evsGet ++ evsFree) ++ publicKeySerializeEvents ++ evsPut))
    (hstk : saveMinStk getStk putStk ≤ stk) :
    subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (blkPl_565).base
      (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk) := by
  dsimp only [idSavePollSpecPlaced, withLsCodeRoLoaded]
  wpp_init xs s0
  rcases xs with ⟨x, st0⟩
  dsimp only at *
  have hinv0 : LibsignalCodeRoLoaded lsmpl s0.mem := by assumption
  have hnlen : x.call.call.addr.name.bytes.length < 2 ^ 32 := by omega
  have hdlen : x.peers.path.length < 2 ^ 32 := by omega
  have hclen : x.peers.changed.length < 2 ^ 32 := by omega
  have hpOk : pathOk (pathOf x.peers.path x.call.call.addr.val.name) := by assumption
  have hwf : ∀ (bs : List (BitVec 8)),
      DirGhost.get rd s0.fs.files x.peers x.call.call.addr.val.name = Except.ok bs → IdFileWf bs := by
    assumption
  have hFit0 : FitsEnv M lim st0 (SaveEnv s0.fs.files x) := by assumption
  refine sepWPp_post_mono_p
    (Q1 := fun sf P_f => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (P_f ⊢ (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk).post (x, st0) s0 sf))
    (Qp1 := fun sf P_f => P_f ⊢ (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk).onPanic (x, st0) s0 sf)
    (fun sf P_f ⟨hsp_f, hcs_f, hent⟩ =>
      ⟨fun hm => Satisfies.mono (sepConj_mono_left hent) hm, hsp_f, hcs_f⟩)
    (fun sf P_f hent hm => Satisfies.mono (sepConj_mono_left hent) hm) ?_
  have hhi : stk ≤ 2 ^ 64 := by
    have hfoc : ∃ Rest : SepProp,
        idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
        dirAt A.repAlloc (x.self + 40#64) x.peers ∗
        memRegion x.call.out 48 ∗
        protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
        x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList ∗
        lsLogOff ∗ A.pool lim st0 s0 ∗ stackAt s0.sp stk ∗ R ⊢
        (stackAt s0.sp stk ∗ (x.call.fut ↦₆₄ x.self)) ∗ Rest := by
      refine ⟨?Rest, ?hfoc⟩
      case hfoc => unfold idSaveBoxAt; ispoll_close_frame
    rcases hfoc with ⟨Rest, hfoc⟩
    have h1 := Satisfies.mono hfoc hpre
    exact memRegion_bound_of_pointsTo64 (by simpa only [stackAt, sepConj_assoc] using h1)
  have hmin : saveMinStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi
  have hsub_hi : saveSubMax getStk putStk ≤ 2 ^ 64 := by
    unfold saveMinStk at hmin; omega
  conv =>
    arg 4
    rw [stackAt_sub_split s0.sp hstk hhi, stackAt_savePoll_eq s0.sp hmin,
        protocolAddressAt_borrow A.repAlloc x.call.call.addr x.call.call.addrA]
    unfold savePollFrameSlots idSaveBoxAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWPp.exists_elim; intro c1
  apply SepWPp.exists_elim; intro c2
  apply SepWPp.exists_elim; intro c3
  apply SepWPp.exists_elim; intro c4
  apply SepWPp.exists_elim; intro c5
  apply SepWPp.exists_elim; intro c6
  apply SepWPp.exists_elim; intro c7
  apply SepWPp.exists_elim; intro c15
  apply SepWPp.exists_elim; intro s16
  apply SepWPp.exists_elim; intro s24
  apply SepWPp.exists_elim; intro s32
  apply SepWPp.exists_elim; intro s40
  apply SepWPp.exists_elim; intro s48
  apply SepWPp.exists_elim; intro s56w
  repeat' (apply SepWPp.exists_elim; intro _)
  apply sepWPp_seq_lscro (mid := lsmpl.base 589) hinv0
  wp_steps_sync_pool (lsmpl.base 589)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_get
  conv =>
    arg 4
    rw [stackAt_sub_split (s0.sp - 0xd0#64) (getStk_le_saveSubMax getStk putStk) hsub_hi]
    simp only [sepConj_assoc]
  have hx3_len : (BitVec.ofNat 64 x.call.call.addr.name.bytes.length).toNat =
      x.call.call.addr.name.bytes.length := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ispoll_call_dirGet_placed (ret_pc := (blkPl_565).base + offAfterGet)
    hGet
    { ret := s0.sp - 0x90#64
      self := x.self + 0x28#64
      dir := x.peers
      nameRo := false
      nameA := x.call.call.addr.name.ptr
      name := x.call.call.addr.name.bytes } st0 ?ispollF
    (by wp_norm_goal) (by wp_norm_lhs)
    (spAligned_sub_d0 (by simpa only [State.spAligned, beq_iff_eq] using hsp_align) (by wp_norm_goal))
    (by wp_norm_goal)
    hinv_get
    (by wp_norm_goal)
    (by wp_norm_goal)
    (by wp_norm_goal)
    (by simp only [wp_norm, arm64_norm, hx3_len])
    hnlen hdlen hpOk
    (by simpa only [fs_setPC, fs_setMem, fs_writeReg64, fs_writeReg, fs_writeReg32,
      fs_writeVReg128, fs_applyWriteback, fs_advancePC, fs_setPState, wp_norm, arm64_norm]
      using hFitGet s0.fs.files x st0 hFit0)
    ?ispollPre ?_
  case ispollPre => ispoll_close_frame
  intro sm1 evsGet gr hpc1 hrun1 hsp1 hcs1 hinv1 hgr
  simp (config := { decide := true }) only [CalleeSavedPreserved, wp_norm, arm64_norm] at hsp1 hcs1
  rcases hcs1 with ⟨hx19_1, hx20_1, _, _, _, hx24_1, _, _, _, _, hx29_1, hvregs_1⟩
  have hsp_al1 : sm1.spAligned = true :=
    spAligned_sub_d0 (by simpa only [State.spAligned, beq_iff_eq] using hsp_align) hsp1
  simp only [fs_setPC, fs_setMem, fs_writeReg64, wp_norm, arm64_norm] at hgr
  conv => arg 4; simp only [wp_norm, arm64_norm, hsp1]
  ispoll_rw_pre (stackAt_sub_split (s0.sp - 0xd0#64) (getStk_le_saveSubMax getStk putStk) hsub_hi).symm
  refine sepWPp_conseq (P' :=
      getResultAt A.repAlloc (s0.sp - 0x90#64) gr ∗
      dirAt A.repAlloc (x.self + 0x28#64) x.peers ∗
      memRegion x.call.out 48 ∗
      idSaveBoxAt x.call.fut x.self x.call.call.addrA x.call.call.keyA 0#8 ∗
      protocolAddressAt A.repAlloc x.call.call.addr x.call.call.addrA ∗
      (x.call.call.keyA ↦ₛ x.call.call.key.publicKey.bytes.toList) ∗
      lsLogOff ∗ A.pool lim (M.stepEvents evsGet st0) sm1 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - saveMinStk getStk putStk) ∗
      stackAt (s0.sp - 0xd0#64) (saveSubMax getStk putStk) ∗
      memRegion (s0.sp - 0xd0#64) 8 ∗
      overlap7View1 (s0.sp - 0xc8#64) c1 c2 c3 c4 c5 c6 c7 ∗
      ((s0.sp - 0xc1#64) ↦₈ c15) ∗
      ((s0.sp - 0xc0#64) ↦₆₄ s16) ∗
      ((s0.sp - 0xb8#64) ↦₈ s24) ∗
      memRegion (s0.sp - 0xb7#64) 7 ∗
      ((s0.sp - 0xb0#64) ↦₆₄ s32) ∗
      ((s0.sp - 0xa8#64) ↦₈ s40) ∗
      memRegion (s0.sp - 0xa7#64) 7 ∗
      ((s0.sp - 0xa0#64) ↦₆₄ s48) ∗
      ((s0.sp - 0x98#64) ↦₆₄ s56w) ∗
      savedCalleeSlots s0) (Entails.of_eq ?_) ?_
  · rw [protocolAddressAt_borrow A.repAlloc x.call.call.addr x.call.call.addrA]
    unfold idSaveBoxAt savedCalleeSlots
    dsimp only [lsLogOff, CryptoVerification.LibsignalTripleRatchet.lsLogOff]
    simp only [wp_norm, arm64_norm]
    ispoll_ac_rfl
  rcases hgr with ⟨hgr_eq, htr1, hGetEvs⟩
  rcases gr with ⟨⟩ | bs
  · exact ispoll_branch_err_placed (rd := rd) (pathOk := pathOk) hstk hhi x st0 evsGet
      c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s48 s56w
      hpc1 hrun1 hsp1 hsp_al1 hvregs_1 hx19_1 hx20_1 hx29_1 ⟨hgr_eq.symm, htr1⟩
      (hSaveErr s0.fs.files x evsGet hgr_eq.symm hGetEvs)
  · rcases hwf bs hgr_eq.symm with rfl | ⟨k, hser⟩
    · exact ispoll_branch_ok_nil_placed (pathOk := pathOk) hC hSer hPut hstk hhi x st0 evsGet
        c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s48 s56w
        hpc1 hrun1 hsp1 hsp_al1 hvregs_1 htr1 hinv1 hx19_1 hx20_1 hx24_1 hx29_1
        hnlen hclen hgr_eq
        (fun evsFree hfo => hFitSer s0.fs.files x [] st0 evsGet evsFree hFit0 hgr_eq.symm hGetEvs hfo)
        (fun evsFree hfo => by
          simpa only [List.append_assoc] using
            hFitPut s0.fs.files x [] st0 evsGet evsFree hFit0 hgr_eq.symm hGetEvs hfo)
        (fun evsFree evsPut hfo hPutEv => by
          simpa only [List.append_assoc] using
            hSaveOk s0.fs.files x [] evsGet evsFree evsPut hgr_eq.symm hGetEvs hfo hPutEv)
    · exact ispoll_branch_ok_some_placed (pathOk := pathOk) hC hSer hPut hDec hEq hstk hhi x st0 evsGet k
        c1 c2 c3 c4 c5 c6 c7 c15 s16 s24 s32 s40 s48 s56w
        hpc1 hrun1 hsp1 hsp_al1 hvregs_1 htr1 hinv1 hx19_1 hx20_1 hx24_1 hx29_1
        hnlen hclen hser hgr_eq
        (fun evsFree hfo => hFitSer s0.fs.files x bs st0 evsGet evsFree hFit0 hgr_eq.symm hGetEvs hfo)
        (fun evsFree hfo => by
          simpa only [List.append_assoc] using
            hFitPut s0.fs.files x bs st0 evsGet evsFree hFit0 hgr_eq.symm hGetEvs hfo)
        (fun evsFree evsPut hfo hPutEv => by
          simpa only [List.append_assoc] using
            hSaveOk s0.fs.files x bs evsGet evsFree evsPut hgr_eq.symm hGetEvs hfo hPutEv)

/-- Core relocatable `[LibsignalPlacement]` verification of `save_identity::{closure#0}` (Block `565`)
under the canonical composite envelope `CliIdSavePollEnv rd GetEnv PutStrEnv`. -/
theorem idSavePoll_placed_ok_of_deps_core [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hSer : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hGet : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hPut : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hDec : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 18)
      (withLsCodeRoLoaded lsmpl (withVmPreserved (identityKeyDecodeRawSpec A))))
    (hEq : subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (lsmpl.base 212)
      (withLsCodeRoLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hstk : saveMinStk getStk putStk ≤ stk) :
    subroutine_ok ((blkPC_565).rebase (blkPl_565).base H) (blkPl_565).base
      (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk) :=
  idSavePoll_placed_ok_of_deps_core_gen hC hSer hGet hPut hDec hEq
    (fun _ _ _ hFit => hFit.seq_left)
    (fun _ _ _ _ hGetEv => CliIdSavePollEnv.of_get_err hGetEv)
    (fun _ _ _ _ _ _ => CliIdSavePollEnv.fits_ser_of_freeOnly)
    (fun _ _ _ _ _ _ => CliIdSavePollEnv.fits_put_of_freeOnly)
    (fun _ _ _ _ _ _ => CliIdSavePollEnv.of_get_ser_put)
    hstk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget
