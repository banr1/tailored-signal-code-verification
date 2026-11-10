/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGet
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErr
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Post-`last_resort.get` Continuation for `KpkMarkPoll`

Proves `kpk_after_lr_get_174_core_placed` and `kpk_after_lr_get_174_placed` (`+372 ..`) on
Block `578` (`lsProg_578 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchetRepr (okTagVec speAt speWord)
open CryptoVerification.LibsignalTripleRatchet (doReserveStackX extHookStack finishGrowStackX)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  FsFiles LibsignalCodeRoLoaded sepWP_seq_lscro withLsCodeRoLoaded
)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SignalSession (lsRustDeallocSymCli)
open CryptoVerification.SignalSession.Cli (
  DirGhost KpkMarkAns KpkMarkPollGhost KpkSeenOk KyberGhost ReadRule baseKeyEntry baseKeysName
  cliBcmpName cliBcmpSpec dirAt getResultAt hasChunk keyName kpkMarkBoxAt kpkMarkOf kpkMarkOutAt
  le32 utf8
)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_578 blkPl_578 lsProg_578)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon (ls_transfer_lscro)
open CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers (
  Concat2PosCall baseKeyEntry_length bind_sepWPp_state_mark cs_vregs cs_x19 cs_x20 cs_x21 cs_x22
  cs_x23 cs_x24 cs_x25 cs_x26 cs_x27 cs_x29 dotBaseKeAddrPlaced epiloguePre getResultAt_b0_ok_unpack
  hasChunk_nil header3_entails_memRegion24 kpkMarkRoBundlePlaced kpkMinStk kpkSubMax le32_length
  malformedStrAddrPlaced pointsTo32_eq_le32 publicKey_serialize_length reusedStrAddrPlaced
  sepWPp_conseq sepWPp_of_sepWP_lscro setWidth_32_setWidth_64 slot_b0_err_collapse
  slot_b0_ok_collapse spAligned_sub_f0 speAt_read_invalidState_eq_words subStack_merge_rev_adj
  subStack_split udiv_msub_37_beq_zero_false udiv_msub_37_beq_zero_true vecU8Tail
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget RustLayoutOk rustAllocEvents
  rustCliDeallocBudgetExternSpecWithStack rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  publicKeySerializeEvents publicKeySerializeSpecX publicKeySerializeStackX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (rustDeallocExternSpecWithStack)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (
  AllocContractsXCliPlaced dirPutSpecPlaced kpkMarkPollSpecPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlacedBudget (dealloc_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget (
  publicKeySerialize_lscro_of_cli
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CalleesBudget (
  KpkConcat2PosEnv kpkConcat2PosEvents
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.CallsPlacedBudget (
  kpk_call_serialize_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget (
  kpk_read_err_278_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErrPlacedBudget (
  kpkAppendPrePutEvents kpkMalformedEvents kpk_append_37c_placed kpk_malformed_2a4_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoopPlacedBudget (
  KpkBcmpLoopEnv kpkMark_post_entails_placed kpk_bcmp_loop_20c_env_placed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux (
  KpkAfterLrGetBranchEnv KpkAfterLrGetOkEnv concat_out_37_eq kpkAfterLrGetPreEvents
  kpkConcat2PosAtSpec kpkConcat2_pos_at_placed_ok kpkMark_core_ext_placed kpkMark_core_sub_placed
  kpk_call_concat2_at_placed
)

export LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux (
  kpkAfterLrGetPreEvents KpkAfterLrGetBranchEnv KpkAfterLrGetOkEnv
  kpkMark_core_ext_placed kpkMark_core_sub_placed
)

private theorem bv_sub_add_lit_kpk (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit_kpk BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

local macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

/-! ## Post-`last_resort.get` Continuation (`+372 ..`, `kpk_after_lr_get_174_placed`) -/

set_option maxHeartbeats 1600000 in
/-- Core post-`last_resort.get` continuation starting at `+372` over any incoming budget state
`st : M.σ` (`A.pool lim st s4`), restoring `stackAt s0.sp stk` and handing the exact stepped
budget state to `hk_err` (`gr = .error ()`) or `hk_ok` (`gr = .ok seenBs`). -/
theorem kpk_after_lr_get_174_core_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {rd : ReadRule}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542) (dirPutSpecPlaced A lim PutEnv putStk))
    (x : KpkMarkPollGhost) (st : M.σ) (s0 s4 : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 filePtr fileCap : BitVec 64) (tmp32 : BitVec 32)
    (gr : Except Unit (List (BitVec 8)))
    {Q Qp : State → SepProp → Prop}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk)
    (hhi_stk : stk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok [])
    (hgr : gr = x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) ∧ s4.trace = s0.trace)
    (hfit_ok : ∀ (seenBs : List (BitVec 8)) (seenCap : BitVec 64),
      gr = .ok seenBs → seenBs.length ≤ seenCap.toNat → seenCap.toNat < 2 ^ 63 →
      FitsEnv M lim st (KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs))
    (hf_len : (baseKeysName x.id).length ≤ fileCap.toNat)
    (hf_lt : fileCap.toNat < 2 ^ 63) (hf_ptr : filePtr ≠ 0#64)
    (hpc : s4.pc = (blkPl_578).base + 372#64)
    (hrun : s4.status = .Running)
    (hsp : s4.sp = s0.sp - 0xf0#64)
    (hfp : s4.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s4.mem)
    (hvregs : calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx19 : s4.readReg64 .x19 = x.fut)
    (hx20 : s4.readReg64 .x20 = x.out)
    (hx24 : s4.readReg64 .x24 = BitVec.ofNat 64 (baseKeysName x.id).length)
    (hx26 : s4.readReg64 .x26 = x.self)
    (hx28 : s4.readReg64 .x28 = x.signedId.setWidth 64)
    (hk_err : gr = .error () → ∀ (sf : State) (P_f : SepProp),
      (.readErr, x.kg) = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey →
      sf.trace = s0.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkOutAt A.repAlloc x.out .readErr ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          A.pool lim (M.stepEvents (optDeallocBufEvents fileCap) st) sf ∗
          stackAt s0.sp stk)) →
      Q sf P_f)
    (hk_ok : ∀ (seenBs : List (BitVec 8)) (seenCap : BitVec 64) (sf : State)
        (evs_after : List AllocEvent) (P_f : SepProp) (res : KpkMarkAns × KyberGhost),
      gr = .ok seenBs →
      seenBs.length ≤ seenCap.toNat →
      seenCap.toNat < 2 ^ 63 →
      res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey →
      sf.trace = s0.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs evs_after →
      (P_f ⊢ kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkOutAt A.repAlloc x.out res.1 ∗
          dirAt A.repAlloc x.self res.2.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) res.2.lastResort ∗
          kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          A.pool lim (M.stepEvents evs_after st) sf ∗
          stackAt s0.sp stk)) →
      Q sf P_f) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) s4
      (getResultAt A.repAlloc (s0.sp - 0xb0#64) gr ∗
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool lim st s4)
      Q Qp := by
  have hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hser_le : publicKeySerializeStackX ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX publicKeySerializeStackX
      CryptoVerification.LibsignalTripleRatchet.publicKeySerializeStackX
    omega
  have hcat_le : 96 + extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hsp_al : s4.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hser : subroutine_ok (lsProg_578 H) (lsmpl.base 205)
      (withLsCodeRoLoaded lsmpl (publicKeySerializeSpecX M A lim)) :=
    publicKeySerialize_lscro_of_cli (callerProg := lsProg_578 H) hC
  have hcat : subroutine_ok (lsProg_578 H) (lsmpl.base 598)
      (withLsCodeRoLoaded lsmpl (kpkConcat2PosAtSpec A lim (96 + extHookStack))) :=
    ls_transfer_lscro (callerProg := lsProg_578 H) (j := 598)
      (kpkConcat2_pos_at_placed_ok hC (96 + extHookStack) (Nat.le_refl _)
        (le_trans hcat_le (by unfold kpkMinStk at hhi; omega)))
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_578 H) hC
  have herr278 := @kpk_read_err_278_placed _ M A lim H hC
  have hmal := @kpk_malformed_2a4_placed _ M A lim H hC
  have happend := @kpk_append_37c_placed _ M A lim H PutEnv decStk getStk putStk hC hPut
  have hloop := @kpk_bcmp_loop_20c_env_placed _ M A lim H rd PutEnv decStk getStk putStk hC hBcmp hPut
  dsimp only [withLsCodeRoLoaded, rustDeallocExternSpecWithStack,
    rustCliDeallocBudgetExternSpecWithStack, lsProg_578] at hdealloc
  dsimp only [lsProg_578] at hser hcat herr278 hmal happend hloop
  clear hC hBcmp hPut
  change SepWPp ((blkPC_578).rebase (blkPl_578).base H) (s0.readReg64 .lr) s4 _ Q Qp
  rcases gr with ⟨⟩ | seenBs
  · have hne : (speWord 1 + 2#64 != 0#64) = true := rfl
    change SepWPp _ _ _ (speAt A.repAlloc (utf8 "read") (s0.sp - 0xb0#64) .invalidState ∗ _) _ _
    rw [speAt_read_invalidState_eq_words A.repAlloc (s0.sp - 0xb0#64) (s0.sp - 0xa8#64)
          (s0.sp - 0xa0#64) (s0.sp - 0x98#64) (s0.sp - 0x90#64) (s0.sp - 0x88#64)
          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega),
        subStack_split s0.sp hext_le hhi]
    kpk_sep_norm
    refine SepWPp.exists_elim fun errBs => SepWPp.exists_elim fun errCap =>
      SepWPp.exists_elim fun errPtr => SepWPp.exists_elim fun fnPtr => ?_
    apply SepWPp.of_sepWP_ret
    apply sepWP_seq_lscro hcrl (mid := (blkPl_578).base + 632#64)
    wp_steps_sync_pool ((blkPl_578).base + 632#64)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hcrl_278
    refine herr278 x st s0 _ fileCap filePtr (baseKeysName x.id)
      errBs errCap errPtr fnPtr _
      (kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa8#64) ↦₆₄ errCap) ∗
        ((s0.sp - 0xa0#64) ↦₆₄ errPtr) ∗ ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
      hf_len hf_lt hf_ptr
      (by kpk_norm) (by kpk_norm) hsp_align (by kpk_norm) hcrl_278
      (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by unfold epiloguePre; kpk_sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf => by
        rcases hgr with ⟨hget2_err, hs4_tr⟩
        have htr_eq : sf.trace = s4.trace := htr_f.trans (by kpk_norm)
        have hans_err :
            ((.readErr : KpkMarkAns), x.kg) =
              kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
          unfold kpkMarkOf
          rw [hget1, ← hget2_err]
        refine hk_err rfl sf P_f hans_err (htr_eq.trans hs4_tr) hsp_f hcs_f ?_
        refine Entails.trans hPf ?_
        have hb0 := slot_b0_err_collapse s0.sp (speWord 1) errCap errPtr
          (BitVec.ofNat 64 errBs.length) (BitVec.ofNat 64 (utf8 "read").length)
          (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
          (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8)
        refine Entails.trans ?_
          (kpkMark_core_ext_placed hstk hhi_stk x
            (M.stepEvents (optDeallocBufEvents fileCap) st) s0 sf wDot wR0 wR7 wM0 wM6
            f0 f1 filePtr fileCap tmp32 (.readErr, x.kg))
        kpk_sep_norm
        refine Entails.trans ?_
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_left hb0)))))))))))))))))
        sep_focus
  · rcases hgr with ⟨hget2_symm, hs4_tr⟩
    have hget2 : x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) = .ok seenBs :=
      hget2_symm.symm
    have heq0 : (okTagVec + 2#64 != 0#64) = false := rfl
    rw [getResultAt_b0_ok_unpack A.repAlloc s0.sp seenBs,
        ProofLib.memRegion_split' (b := s0.sp - 0xc8#64) (n := 8) (k := 16)
          (b' := s0.sp - 0xc0#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 0xc0#64) (n := 8) (k := 8)
          (b' := s0.sp - 0xb8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (s0.sp - 0xc8#64),
        ProofLib.memRegion_eight (s0.sp - 0xc0#64),
        ProofLib.memRegion_eight (s0.sp - 0xb8#64)]
    unfold epiloguePre kpkMarkBoxAt
    kpk_sep_norm
    refine SepWPp.exists_elim fun seenCap => SepWPp.exists_elim fun seenPtr =>
      SepWPp.exists_elim fun c8_0 => SepWPp.exists_elim fun c0_0 =>
      SepWPp.exists_elim fun b8_0 => ?_
    refine SepWPp.pure_elim fun ⟨hs_len, hs_lt, hs_ptr⟩ => ?_
    have hfit := hfit_ok seenBs seenCap rfl hs_len hs_lt
    let st_ser : M.σ := M.stepEvents publicKeySerializeEvents st
    let st_cat : M.σ := M.stepEvents (rustAllocEvents 37 1) st_ser
    let st_pre : M.σ := M.stepEvents kpkAfterLrGetPreEvents st
    have hst_pre_eq : M.stepEvents (rustDeallocEvents 33 1) st_cat = st_pre := by
      simp only [st_ser, st_cat, st_pre, kpkAfterLrGetPreEvents, List.append_assoc,
        M.stepEvents_append]
    apply sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 205)
    wp_steps_sync_pool (lsmpl.base 205)
    apply SepWP.done
      (by kpk_norm)
      (by wp_norm_lhs)
    intro hcrl_ser
    apply bind_sepWPp_state_mark; intro s_ser
    have hsp_ser : s_ser.sp = s0.sp - 0xf0#64 := by dsimp only [s_ser]; (try kpk_norm)
    dsimp only [s_ser] at *
    refine kpk_call_serialize_placed hser ⟨x.baseKeyA, x.baseKey⟩ st
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - publicKeySerializeStackX) ∗
        ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xa0#64) ↦₆₄ seenPtr) ∗ ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        memRegion (s0.sp - 0x90#64) 16 ∗
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        epiloguePre s0 x)
      (ret_pc := (blkPl_578).base + 408#64)
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_ser)
      (by kpk_norm)
      hcrl_ser
      (by kpk_norm)
      (KpkAfterLrGetOkEnv.fits_ser hfit)
      (by
        rw [hsp_ser, subStack_split s0.sp hser_le hhi]
        unfold epiloguePre kpkMarkBoxAt
        kpk_sep_norm
        sep_focus)
      fun s5 hpc5 hrun5 hsp5 hcs5 hcrl5 hser_ne0 hser_33 htr5 => ?_
    have hs5_sp : s5.sp = s0.sp - 0xf0#64 := hsp5.trans hsp_ser
    have hs5_fp : s5.readReg64 .x29 = s0.sp - 0x60#64 := by rw [(cs_x29 hcs5)]; kpk_norm
    have hs5_tr : s5.trace = s0.trace := by
      rw [htr5]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs4_tr))
    kpk_sep_norm
    rw [hsp_ser, subStack_merge_rev_adj s0.sp hser_le hhi,
        pointsTo32_eq_le32 (s0.sp - 0x64#64) x.signedId]
    apply sepWPp_of_sepWP_lscro hcrl5 (mid := lsmpl.base 598)
    wp_steps_sync_pool (lsmpl.base 598)
    apply SepWP.done
      (by kpk_norm)
      (by wp_norm_lhs)
    intro hcrl_cat
    apply bind_sepWPp_state_mark; intro s_cat
    have hsp_cat : s_cat.sp = s0.sp - 0xf0#64 := by dsimp only [s_cat]; (try kpk_norm)
    dsimp only [s_cat] at *
    let catCall : Concat2PosCall :=
      ⟨s0.sp - 0x80#64, s0.sp - 0xb0#64, s0.sp - 0x64#64, le32 x.signedId,
        s5.readReg64 .x0, x.baseKey.serialize⟩
    have hcat_evs : kpkConcat2PosEvents catCall = rustAllocEvents 37 1 := by
      simp only [kpkConcat2PosEvents, catCall, le32_length, publicKey_serialize_length]
    have hfit_cat : FitsEnv M lim st_ser (KpkConcat2PosEnv catCall) := by
      intro evs hevs
      rw [KpkConcat2PosEnv, hcat_evs] at hevs
      subst hevs
      exact KpkAfterLrGetOkEnv.fits_cat37 hfit
    refine kpk_call_concat2_at_placed hcat catCall st_ser
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
        A.live (s5.readReg64 .x0) 33 1 ∗
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        memRegion (s0.sp - 0x90#64) 16 ∗
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x)
      (ret_pc := (blkPl_578).base + 448#64)
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_cat)
      (by kpk_norm)
      hcrl_cat
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by dsimp only [catCall]; rw [le32_length]; decide)
      (by dsimp only [catCall]; rw [publicKey_serialize_length]; decide)
      (by dsimp only [catCall]; rw [le32_length, publicKey_serialize_length]; decide)
      hfit_cat
      (by
        dsimp only [catCall]
        rw [hsp_cat, subStack_split s0.sp hcat_le hhi, le32_length,
            publicKey_serialize_length x.baseKey]
        have e_a8 : s0.sp - 0xb0#64 + 8#64 = s0.sp - 0xa8#64 := by bv_omega
        have e_a0 : s0.sp - 0xb0#64 + 16#64 = s0.sp - 0xa0#64 := by bv_omega
        have e_98 : s0.sp - 0xb0#64 + 24#64 = s0.sp - 0x98#64 := by bv_omega
        rw [e_a8, e_a0, e_98]
        unfold epiloguePre
        kpk_sep_norm
        sep_focus)
      fun s6 usedPtr hpc6 hrun6 hsp6 hcs6 hcrl6 htr6 hu_ptr => ?_
    have hs6_sp : s6.sp = s0.sp - 0xf0#64 := hsp6.trans hsp_cat
    have hs6_al : s6.spAligned = true := spAligned_sub_f0 hsp_align hs6_sp
    have hs6_tr : s6.trace = s0.trace := by
      rw [htr6]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs5_tr))
    have hs6_21 : s6.readReg64 .x21 = 33#64 := by rw [(cs_x21 hcs6)]; kpk_norm
    have hs6_23 : s6.readReg64 .x23 = s5.readReg64 .x0 := by rw [(cs_x23 hcs6)]; kpk_norm
    have hpos33 : 0 < 33 := by decide
    have hpow33 : ∃ k : Nat, 1 = 2 ^ k := ⟨0, rfl⟩
    have hhi33 : 33 + 1 ≤ 2 ^ 63 := by decide
    have hrlay33 : RustLayoutOk 33 1 := ⟨⟨hpos33, hpow33, hhi33⟩, by decide⟩
    let usedBs := baseKeyEntry x.signedId x.baseKey
    have hused37 : usedBs.length = 37 := baseKeyEntry_length x.signedId x.baseKey
    have hu_len : usedBs.length ≤ (37#64 : BitVec 64).toNat := by rw [hused37]; decide
    have hu_lt : (37#64 : BitVec 64).toNat < 2 ^ 63 := by decide
    dsimp only [catCall]
    rw [hcat_evs]
    change SepWPp _ _ _ (_ ∗ _) _ _
    have hfold_b0 :
        (((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
          ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
          ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
          ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length)) ⊢
        (((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
          ((s0.sp - 0xa8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
          ((s0.sp - 0xa0#64) ↦₆₄ s5.readReg64 .x0) ∗
          ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length)) := by
      have e_a8 : s0.sp - 0xb0#64 + 8#64 = s0.sp - 0xa8#64 := by bv_omega
      have e_a0 : s0.sp - 0xb0#64 + 16#64 = s0.sp - 0xa0#64 := by bv_omega
      have e_98 : s0.sp - 0xb0#64 + 24#64 = s0.sp - 0x98#64 := by bv_omega
      rw [e_a8, e_a0, e_98]
      exact Entails.refl _
    have hser_mem : ((s5.readReg64 .x0) ↦ₛ x.baseKey.serialize) ⊢ memRegion (s5.readReg64 .x0) 33 := by
      have hl := publicKey_serialize_length x.baseKey
      exact hl ▸ pointsToBytes_entails_memRegion (s5.readReg64 .x0) x.baseKey.serialize
    rw [hsp_cat, ← pointsTo32_eq_le32 (s0.sp - 0x64#64) x.signedId]
    have hprep_448 :
        ((((s0.sp - 0x80#64) ↦₆₄ BitVec.ofNat 64 ((le32 x.signedId).length + x.baseKey.serialize.length)) ∗
          ((s0.sp - 0x80#64 + 8#64) ↦₆₄ usedPtr) ∗
          ((s0.sp - 0x80#64 + 16#64) ↦₆₄ BitVec.ofNat 64 ((le32 x.signedId).length + x.baseKey.serialize.length)) ∗
          A.live usedPtr ((le32 x.signedId).length + x.baseKey.serialize.length) 1 ∗
          (usedPtr ↦ₛ (le32 x.signedId ++ x.baseKey.serialize)) ∗
          ((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
          ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
          ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
          ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length) ∗
          ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
          ((s5.readReg64 .x0) ↦ₛ x.baseKey.serialize) ∗
          A.pool lim st_cat s6 ∗ stackAt (s0.sp - 0xf0#64) (96 + extHookStack)) ∗
        memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
        A.live (s5.readReg64 .x0) 33 1 ∗
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        memRegion (s0.sp - 0x90#64) 16 ∗
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x) ⊢
        A.repAlloc.live (s5.readReg64 .x0) 33 1 ∗ memRegion (s5.readReg64 .x0) 33 ∗
        ((s0.sp - 0x80#64) ↦₆₄ 37#64) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
        bytesAt false usedPtr usedBs ∗
        vecU8Tail A.repAlloc 37#64 usedPtr usedBs ∗
        memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
        bytesAt false seenPtr seenBs ∗
        vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool lim st_cat s6 := by
      have hsub96 :
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
              (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
            stackAt (s0.sp - 0xf0#64) (96 + extHookStack) =
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
              (kpkSubMax decStk getStk putStk - extHookStack) ∗
            stackAt (s0.sp - 0xf0#64) extHookStack := by
        rw [← subStack_split s0.sp hcat_le hhi, subStack_split s0.sp hext_le hhi]
      have hb0_col := Entails.trans (sepConj_mono_left hfold_b0)
        (by
          simpa only [sepConj_assoc] using
            slot_b0_ok_collapse s0.sp (s0.sp - 0x64#64)
              (BitVec.ofNat 64 (le32 x.signedId).length)
              (s5.readReg64 .x0)
              (BitVec.ofNat 64 x.baseKey.serialize.length))
      have h1 :
          (((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
            ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
            ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
            ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length) ∗
            memRegion (s0.sp - 0x90#64) 16) ⊢ memRegion (s0.sp - 0xb0#64) 48 := by
        simpa only [sepConj_assoc] using hb0_col
      dsimp only [RustCliAllocBudget.repAlloc_live, usedBs]
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono hser_mem (Entails.refl _)))
      have hswap :
          ((((s0.sp - 0x80#64) ↦₆₄ BitVec.ofNat 64 ((le32 x.signedId).length + x.baseKey.serialize.length)) ∗
              ((s0.sp - 0x80#64 + 8#64) ↦₆₄ usedPtr) ∗
              ((s0.sp - 0x80#64 + 16#64) ↦₆₄ BitVec.ofNat 64 ((le32 x.signedId).length + x.baseKey.serialize.length)) ∗
              A.live usedPtr ((le32 x.signedId).length + x.baseKey.serialize.length) 1 ∗
              (usedPtr ↦ₛ (le32 x.signedId ++ x.baseKey.serialize)) ∗
              ((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
              ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
              ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
              ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length) ∗
              ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
              ((s5.readReg64 .x0) ↦ₛ x.baseKey.serialize) ∗
              A.pool lim st_cat s6 ∗ stackAt (s0.sp - 0xf0#64) (96 + extHookStack)) ∗
            memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
              (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
            A.live (s5.readReg64 .x0) 33 1 ∗
            bytesAt false seenPtr seenBs ∗
            vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
            memRegion (s0.sp - 0x90#64) 16 ∗
            kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
            memRegion (s0.sp - 0xf0#64) 8 ∗
            ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
            ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
            ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
            ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
            memRegion (s0.sp - 0x68#64) 4 ∗
            bytesAt false filePtr (baseKeysName x.id) ∗
            vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
            dirAt A.repAlloc x.self x.kg.oneTime ∗
            dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
            epiloguePre s0 x) =
          ((((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
              ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
              ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
              ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length) ∗
              memRegion (s0.sp - 0x90#64) 16) ∗
            (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
              stackAt (s0.sp - 0xf0#64) (96 + extHookStack)) ∗
            (((s0.sp - 0x80#64) ↦₆₄ BitVec.ofNat 64 ((le32 x.signedId).length + x.baseKey.serialize.length)) ∗
              ((s0.sp - 0x80#64 + 8#64) ↦₆₄ usedPtr) ∗
              ((s0.sp - 0x80#64 + 16#64) ↦₆₄ BitVec.ofNat 64 ((le32 x.signedId).length + x.baseKey.serialize.length)) ∗
              A.live usedPtr ((le32 x.signedId).length + x.baseKey.serialize.length) 1 ∗
              (usedPtr ↦ₛ (le32 x.signedId ++ x.baseKey.serialize))) ∗
            A.live (s5.readReg64 .x0) 33 1 ∗ ((s5.readReg64 .x0) ↦ₛ x.baseKey.serialize) ∗
            kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
            memRegion (s0.sp - 0xf0#64) 8 ∗
            ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
            ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
            ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
            ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
            memRegion (s0.sp - 0x68#64) 4 ∗
            ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
            bytesAt false seenPtr seenBs ∗
            vecU8Tail A.repAlloc seenCap seenPtr seenBs ∗
            bytesAt false filePtr (baseKeysName x.id) ∗
            vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
            dirAt A.repAlloc x.self x.kg.oneTime ∗
            dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
            epiloguePre s0 x ∗ A.pool lim st_cat s6) := by
        sep_ac_rfl
      rw [hswap, hsub96, concat_out_37_eq A s0.sp usedPtr x.signedId x.baseKey]
      refine Entails.trans (sepConj_mono_left h1) ?_
      kpk_sep_norm
      sep_focus
    refine sepWPp_conseq hprep_448 ?_
    apply sepWPp_of_sepWP_lscro
      (mid := (blkPl_578).base + 468#64) hcrl6
    have h21_f : (s6.readReg64 .x21 == 0#64) = false := by rw [hs6_21]; rfl
    have h33_ne0 : (33#64 == 0#64) = false := rfl
    apply sepWP_seq_lscro hcrl6 (mid := lsρ lsRustDeallocSymCli)
    wp_steps_sync_pool (lsρ lsRustDeallocSymCli)
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    rintro ⟨hcl_da, hro_da⟩
    rw [← hs6_sp]
    wp_call hdealloc (s5.readReg64 .x0, 33, 1, st_cat)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_468
    apply bind_sepWPp_state_mark; intro s7
    rw [hs6_sp, hs5_sp]
    have hs7_pc : s7.pc = (blkPl_578).base + 468#64 := by
      (try dsimp only [s7]); kpk_norm
    have hs7_run : s7.status = .Running := by
      (try dsimp only [s7]); kpk_norm
    have hs7_sp : s7.sp = s0.sp - 0xf0#64 := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs6_sp))
    have hs7_fp : s7.readReg64 .x29 = s0.sp - 0x60#64 := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcs5)]; kpk_norm)
    have hs7_22 : s7.readReg64 .x22 = BitVec.ofNat 64 seenBs.length := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x22 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x22 hcs5)]; kpk_norm)
    have hs7_24 : s7.readReg64 .x24 = BitVec.ofNat 64 (baseKeysName x.id).length := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcs5)]; kpk_norm)
    have hs7_25 : s7.readReg64 .x25 = seenPtr := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x25 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x25 hcs5)]; kpk_norm)
    have hs7_26 : s7.readReg64 .x26 = x.self := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcs5)]; kpk_norm)
    have hs7_27 : s7.readReg64 .x27 = seenCap := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcs5)]; kpk_norm)
    have hs7_19 : s7.readReg64 .x19 = x.fut := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcs5)]; kpk_norm)
    have hs7_20 : s7.readReg64 .x20 = x.out := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcs5)]; kpk_norm)
    have hs7_v : calleeSavedVRegs s7 = calleeSavedVRegs s0 := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcs5)]; kpk_norm)
    have hs7_tr : s7.trace = s0.trace := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs6_tr))
    have hs7_al : s7.spAligned = true :=
      spAligned_sub_f0 hsp_align hs7_sp
    have hcrl_s7 : LibsignalCodeRoLoaded lsmpl s7.mem := hcrl_468
    rw [hst_pre_eq]
    refine sepWPp_conseq (Entails.of_eq (show _ = A.pool lim st_pre s7 ∗ _ from rfl)) ?_
    clear_value s7
    have h37_ne0 : (37#64 == 0#64) = false := rfl
    by_cases hmod : seenBs.length % 37 ≠ 0
    · have hrem_ne := udiv_msub_37_beq_zero_false (by omega : seenBs.length < 2 ^ 64) hmod
      have hans_m : (KpkMarkAns.malformed, x.kg) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1, hget2]
        dsimp only
        rw [baseKeyEntry_length x.signedId x.baseKey]
        split
        · rfl
        · contradiction
      unfold kpkMarkRoBundlePlaced
      kpk_sep_norm
      apply sepWPp_of_sepWP_lscro
        (mid := (blkPl_578).base + 676#64) hcrl_s7
      wp_steps_sync_pool ((blkPl_578).base + 676#64)
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_2a4
      refine hmal x st_pre s0 _ wM0 wM6
        37#64 usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr (baseKeysName x.id) _
        ((dotBaseKeAddrPlaced ↦₆₄ᵣ wDot) ∗
          (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
          ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
          dirAt A.repAlloc x.self x.kg.oneTime ∗
          dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
        (KpkAfterLrGetOkEnv.fits_malformed hfit hmod)
        hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm) (by kpk_norm) hsp_align
        (by kpk_norm) (by kpk_norm) (by kpk_norm) hinv_2a4
        (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
        (by
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_m P_m htr_m hsp_m hcs_m hPm => by
          have hevs_m := KpkAfterLrGetOkEnv.of_malformed
            (PutEnv := PutEnv) (x := x) (seenCap := seenCap) (fileCap := fileCap) hmod
          have hst_m :
              M.stepEvents (kpkMalformedEvents 37#64 seenCap fileCap) st_pre =
                M.stepEvents (kpkAfterLrGetPreEvents ++ kpkMalformedEvents 37#64 seenCap fileCap) st := by
            simp only [st_pre, M.stepEvents_append]
          refine hk_ok seenBs seenCap sf_m
            (kpkAfterLrGetPreEvents ++ kpkMalformedEvents 37#64 seenCap fileCap)
            P_m (.malformed, x.kg) rfl hs_len hs_lt hans_m htr_m hsp_m hcs_m hevs_m ?_
          rw [hst_m] at hPm
          refine Entails.trans hPm ?_
          have hm_c8 := header3_entails_memRegion24 (s0.sp - 0xc8#64)
            (s0.sp - 0xc0#64) (s0.sp - 0xb8#64) seenCap seenPtr
            (BitVec.ofNat 64 seenBs.length) (by bv_omega) (by bv_omega)
          have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
            (s0.sp - 0x78#64) (s0.sp - 0x70#64) 37#64 usedPtr 37#64
            (by bv_omega) (by bv_omega)
          refine Entails.trans ?_
            (kpkMark_core_ext_placed hstk hhi_stk x
              (M.stepEvents (kpkAfterLrGetPreEvents ++ kpkMalformedEvents 37#64 seenCap fileCap) st)
              s0 sf_m wDot wR0 wR7 wM0 wM6 f0 f1 filePtr fileCap x.signedId (.malformed, x.kg))
          unfold kpkMarkRoBundlePlaced
          kpk_sep_norm
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                        (sepConj_mono_right
                          (sepConj_mono hm_c8
                            (sepConj_mono_right (sepConj_mono_left hm_80))))))))))))))))))))))
          sep_focus
    · have hmod0 : seenBs.length % 37 = 0 := by omega
      have hrem_eq := udiv_msub_37_beq_zero_true (by omega : seenBs.length < 2 ^ 64) hmod0
      have hfit_loop := KpkAfterLrGetOkEnv.fits_loop hfit hmod0
      rw [show ∀ (Pool S U1 U2 U3 U4 U5 MR Rest : SepProp),
            Pool ∗ S ∗ U1 ∗ U2 ∗ U3 ∗ U4 ∗ U5 ∗ MR ∗ Rest =
            (MR ∗ S) ∗ Pool ∗ U1 ∗ U2 ∗ U3 ∗ U4 ∗ U5 ∗ Rest from
          fun _ _ _ _ _ _ _ _ _ => by sep_ac_rfl,
          ← subStack_split s0.sp hext_le hhi]
      unfold kpkMarkRoBundlePlaced
      kpk_sep_norm
      by_cases hseen_nil : seenBs = []
      · subst hseen_nil
        have hnil_beq : (BitVec.ofNat 64 ([] : List (BitVec 8)).length == 0#64) = true := rfl
        have hhas_nil : hasChunk [] usedBs = false := hasChunk_nil hused37
        have hans_nil :
            (KpkMarkAns.ok,
              { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) ([] ++ usedBs) }) =
            kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
          unfold kpkMarkOf
          rw [hget1, hget2]
          dsimp only
          rw [hasChunk_nil (baseKeyEntry_length x.signedId x.baseKey)]
          simp only [List.length_nil, Nat.zero_mod, ne_eq, not_true_eq_false,
            Bool.false_eq_true, ↓reduceIte, usedBs]
        apply sepWPp_of_sepWP_lscro
          (mid := (blkPl_578).base + 892#64) hcrl_s7
        wp_steps_sync_pool ((blkPl_578).base + 892#64)
        apply SepWP.done (by kpk_norm) (by kpk_norm)
        intro hinv_37c
        refine happend x st_pre s0 _
          37#64 usedPtr usedBs seenCap seenPtr [] fileCap filePtr (baseKeysName x.id) _
          ((dotBaseKeAddrPlaced ↦₆₄ᵣ wDot) ∗
            (reusedStrAddrPlaced ↦₆₄ᵣ wR0) ∗
            ((reusedStrAddrPlaced + 7#64) ↦₆₄ᵣ wR7) ∗
            (malformedStrAddrPlaced ↦₆₄ᵣ wM0) ∗
            ((malformedStrAddrPlaced + 6#64) ↦₆₄ᵣ wM6) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
            memRegion (s0.sp - 0xf0#64) 8 ∗
            ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
            memRegion (s0.sp - 0x68#64) 4 ∗
            ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
            dirAt A.repAlloc x.self x.kg.oneTime ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
          hhi hlr_chg
          (KpkBcmpLoopEnv.fits_reserve hfit_loop hhas_nil)
          (KpkBcmpLoopEnv.fits_put hfit_loop hhas_nil)
          hused37 hu_len hu_lt hu_ptr (by decide) hs_len hs_lt hs_ptr
          hf_len hf_lt hf_ptr
          (by kpk_norm) (by kpk_norm) hsp_align
          (by kpk_norm) (by kpk_norm) (by kpk_norm) hinv_37c
          (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm) (by kpk_norm)
          (by unfold epiloguePre; kpk_sep_focus)
          fun sf_a evs_put P_a htr_a hsp_a hcs_a hevs_put hPa => by
            let evs_br := kpkAppendPrePutEvents seenCap [] 37#64 ++ evs_put
            have hevs_ok := KpkAfterLrGetOkEnv.of_loop
              (PutEnv := PutEnv) (x := x) (seenCap := seenCap) (fileCap := fileCap)
              hmod0 (KpkBcmpLoopEnv.of_append hhas_nil hevs_put)
            have hst_a :
                M.stepEvents evs_br st_pre =
                  M.stepEvents (kpkAfterLrGetPreEvents ++ evs_br) st := by
              simp only [st_pre, M.stepEvents_append]
            refine hk_ok [] seenCap sf_a (kpkAfterLrGetPreEvents ++ evs_br) P_a
              (.ok, { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) ([] ++ usedBs) })
              rfl hs_len hs_lt hans_nil htr_a hsp_a hcs_a hevs_ok ?_
            change P_a ⊢ _
            rw [show M.stepEvents (kpkAppendPrePutEvents seenCap [] 37#64 ++ evs_put) st_pre =
              M.stepEvents (kpkAfterLrGetPreEvents ++ evs_br) st from hst_a] at hPa
            refine Entails.trans hPa ?_
            have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
              (s0.sp - 0x78#64) (s0.sp - 0x70#64) 37#64 usedPtr 37#64
              (by bv_omega) (by bv_omega)
            refine Entails.trans ?_
              (kpkMark_core_ext_placed hstk hhi_stk x
                (M.stepEvents (kpkAfterLrGetPreEvents ++ evs_br) st)
                s0 sf_a wDot wR0 wR7 wM0 wM6
                (BitVec.ofNat 64 (baseKeysName x.id).length) seenPtr filePtr fileCap x.signedId
                (.ok, { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) ([] ++ usedBs) }))
            rw [subStack_split s0.sp hext_le hhi]
            unfold kpkMarkRoBundlePlaced
            kpk_sep_norm
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                            (sepConj_mono_left hm_80))))))))))))))))))))))
            sep_focus
      · have hseen_pos : 0 < seenBs.length :=
          List.length_pos_iff.mpr hseen_nil
        have hseen_beq : (BitVec.ofNat 64 seenBs.length == 0#64) = false := by
          apply beq_false_of_ne
          intro h0
          have ht := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
          change seenBs.length = 0 at ht
          omega
        have hrem_ex : ∃ rem, seenBs.length = (rem + 1) * 37 := by
          refine ⟨seenBs.length / 37 - 1, ?_⟩
          omega
        apply sepWPp_of_sepWP_lscro
          (mid := (blkPl_578).base + 524#64) hcrl_s7
        wp_steps_sync_pool ((blkPl_578).base + 524#64)
        apply SepWP.done (by kpk_norm) (by kpk_norm)
        intro hinv_20c
        obtain ⟨rem, hrem_len⟩ := hrem_ex
        refine hloop x st_pre s0 wR0 wR7
          37#64 usedPtr seenCap seenPtr seenBs fileCap filePtr
          ((dotBaseKeAddrPlaced ↦₆₄ᵣ wDot) ∗
            (malformedStrAddrPlaced ↦₆₄ᵣ wM0) ∗
            ((malformedStrAddrPlaced + 6#64) ↦₆₄ᵣ wM6) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
            memRegion (s0.sp - 0xf0#64) 8 ∗
            memRegion (s0.sp - 0x68#64) 4 ∗
            ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
          hhi hsp_align hSeenOk hlr_chg hget1 hget2 hfit_loop
          hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
          (fun sf_l evs_loop P_l ans kg' hans_l htr_l hsp_l hcs_l hevs_loop hPl => by
            have hevs_ok := KpkAfterLrGetOkEnv.of_loop hmod0 hevs_loop
            have hst_l :
                M.stepEvents evs_loop st_pre =
                  M.stepEvents (kpkAfterLrGetPreEvents ++ evs_loop) st := by
              simp only [st_pre, M.stepEvents_append]
            refine hk_ok seenBs seenCap sf_l (kpkAfterLrGetPreEvents ++ evs_loop) P_l
              (ans, kg') rfl hs_len hs_lt hans_l htr_l hsp_l hcs_l hevs_ok ?_
            rw [hst_l] at hPl
            refine Entails.trans hPl ?_
            refine Entails.trans ?_
              (kpkMark_core_sub_placed hstk hhi_stk x
                (M.stepEvents (kpkAfterLrGetPreEvents ++ evs_loop) st)
                s0 sf_l wDot wR0 wR7 wM0 wM6 filePtr fileCap x.signedId (ans, kg'))
            unfold kpkMarkRoBundlePlaced
            kpk_sep_norm
            sep_focus)
          rem _ 0 [] seenBs _
          rfl rfl hrem_len (fun _ hj => absurd hj (Nat.not_lt_zero _))
          (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
          hinv_20c (by kpk_norm) (by kpk_norm) (by kpk_norm)
          (by dsimp only [List.length_nil]; rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]; kpk_norm)
          (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
          (by unfold epiloguePre; kpk_sep_focus)

/-- Budget-threaded `kpk_after_lr_get_174_placed`: steps from `+372` right after `last_resort.get`
returns `gr` with incoming pool `A.pool lim (M.stepEvents evsPre st0) s4` and establishes
`(kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk).post (x, st0) s0 sf`. -/
theorem kpk_after_lr_get_174_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {MarkEnv : FsFiles → KpkMarkPollGhost → List AllocEvent → Prop}
    {decStk getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hBcmp : HookSat H cliBcmpName (withVmPreserved cliBcmpSpec))
    (hPut : subroutine_ok (lsProg_578 H) (lsmpl.base 542) (dirPutSpecPlaced A lim PutEnv putStk))
    (x : KpkMarkPollGhost) (st0 : M.σ) (evsPre : List AllocEvent) (s0 s4 : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 filePtr fileCap : BitVec 64) (tmp32 : BitVec 32)
    (gr : Except Unit (List (BitVec 8)))
    {Q Qp : State → SepProp → Prop}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk)
    (hhi_stk : stk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok [])
    (hgr : gr = x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) ∧ s4.trace = s0.trace)
    (hfit_ok : ∀ (seenBs : List (BitVec 8)) (seenCap : BitVec 64),
      gr = .ok seenBs → seenBs.length ≤ seenCap.toNat → seenCap.toNat < 2 ^ 63 →
      FitsEnv M lim (M.stepEvents evsPre st0) (KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs))
    (hMarkErr : gr = .error () → MarkEnv s0.fs.files x (evsPre ++ optDeallocBufEvents fileCap))
    (hMarkOk : ∀ (seenBs : List (BitVec 8)) (seenCap : BitVec 64) (evs_after : List AllocEvent),
      gr = .ok seenBs → seenBs.length ≤ seenCap.toNat → seenCap.toNat < 2 ^ 63 →
      KpkAfterLrGetOkEnv PutEnv x seenCap fileCap seenBs evs_after →
      MarkEnv s0.fs.files x (evsPre ++ evs_after))
    (hf_len : (baseKeysName x.id).length ≤ fileCap.toNat)
    (hf_lt : fileCap.toNat < 2 ^ 63) (hf_ptr : filePtr ≠ 0#64)
    (hpc : s4.pc = (blkPl_578).base + 372#64)
    (hrun : s4.status = .Running)
    (hsp : s4.sp = s0.sp - 0xf0#64)
    (hfp : s4.readReg64 .x29 = s0.sp - 0x60#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s4.mem)
    (hvregs : calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx19 : s4.readReg64 .x19 = x.fut)
    (hx20 : s4.readReg64 .x20 = x.out)
    (hx24 : s4.readReg64 .x24 = BitVec.ofNat 64 (baseKeysName x.id).length)
    (hx26 : s4.readReg64 .x26 = x.self)
    (hx28 : s4.readReg64 .x28 = x.signedId.setWidth 64)
    (hk_final : ∀ (sf : State) (P_f : SepProp),
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkPollSpecPlaced rd pathOk A lim MarkEnv stk).post (x, st0) s0 sf) →
      Q sf P_f) :
    SepWPp (lsProg_578 H) (s0.readReg64 .lr) s4
      (getResultAt A.repAlloc (s0.sp - 0xb0#64) gr ∗
        kpkMarkRoBundlePlaced wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A.repAlloc fileCap filePtr (baseKeysName x.id) ∗
        dirAt A.repAlloc x.self x.kg.oneTime ∗
        dirAt A.repAlloc (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool lim (M.stepEvents evsPre st0) s4)
      Q Qp :=
  kpk_after_lr_get_174_core_placed hC hBcmp hPut x (M.stepEvents evsPre st0) s0 s4
    wDot wR0 wR7 wM0 wM6 f0 f1 filePtr fileCap tmp32 gr
    hstk hhi_stk hsp_align hSeenOk hlr_chg hget1 hgr hfit_ok hf_len hf_lt hf_ptr
    hpc hrun hsp hfp hcrl hvregs hx19 hx20 hx24 hx26 hx28
    (fun hgr_err sf P_f hans htr hsp_f hcs_f hPf =>
      hk_final sf P_f hsp_f hcs_f <| by
        rw [← M.stepEvents_append] at hPf
        exact Entails.trans hPf
          (sepConj_mono_right
            (kpkMark_post_entails_placed x st0 s0 sf (evsPre ++ optDeallocBufEvents fileCap)
              (.readErr, x.kg) ⟨hans, htr, hMarkErr hgr_err⟩)))
    (fun seenBs seenCap sf evs_after P_f res hgr_ok hs_len hs_lt hans htr hsp_f hcs_f hevs hPf =>
      hk_final sf P_f hsp_f hcs_f <| by
        rw [← M.stepEvents_append] at hPf
        exact Entails.trans hPf
          (sepConj_mono_right
            (kpkMark_post_entails_placed x st0 s0 sf (evsPre ++ evs_after) res
              ⟨hans, htr, hMarkOk seenBs seenCap evs_after hgr_ok hs_len hs_lt hevs⟩)))

end LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudget
