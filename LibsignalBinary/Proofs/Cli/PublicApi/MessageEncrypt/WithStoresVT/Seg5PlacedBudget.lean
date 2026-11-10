/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlacedBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPoll
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSome
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.SymWP
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs -- shake: keep

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Part 5): `SegLoad`

Proves `h45_segLoad_placed_okVT` under `EncEnvTFullBudget` on Block `464` (`lsProg_464 Hk`) under
`RustCliAllocBudget M` and `[LibsignalPlacement]`, re-exporting the `Seg5PlacedBudgetAux`
environment and `h45_segSignal_enc_to_ret_pf_placed` call seam.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudgetAux (
  h45_kitEnvF h45_encTailVBudget_kitF_placed h45_subroutineOutcome_budget_kitF_placed
  h45_segExitBudget_kitF_placed h45_fromCurEnv_mono h45_withStoresEncEnv_mono
  h45_segExitBudget_scopeMono h45_seamBudget_loadRem_of_prefix
  h45_curStateVBudget_of_false h45_curStateVBudget_of_scopeNone
  h45_loadOutRes_some_scopeNone_placed
  EncCalleesTFullBudget EncEnvTFullBudget h45_envF_budget h45_envNone_budget
  h45_q_otr_placed h45_segSignal_enc_to_ret_pf_placed
)
export LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudgetAux (
  h45_kitEnvF h45_encTailVBudget_kitF_placed h45_subroutineOutcome_budget_kitF_placed
  h45_segExitBudget_kitF_placed h45_fromCurEnv_mono h45_withStoresEncEnv_mono
  h45_segExitBudget_scopeMono h45_seamBudget_loadRem_of_prefix
  h45_curStateVBudget_of_false h45_curStateVBudget_of_scopeNone
  h45_loadOutRes_some_scopeNone_placed
  EncCalleesTFullBudget EncEnvTFullBudget h45_envF_budget h45_envNone_budget
  h45_q_otr_placed h45_segSignal_enc_to_ret_pf_placed
)

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  SeamBudget retagSessionStore retagIdentityStore BoxAllocEnv
  SpqrSendBudgetEnv SessionStoreBudgetEnv IdentityStoreBudgetEnv WithStoresEncEnv
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommonPlacedBudget (
  memcpy_budget_ok dealloc_budget_ok
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlacedBudget (
  LoadRemEnv seqEnv3_reassoc
  segLoad_shim_budget_wp_vm segLoad_pre_poll_budget_wp_vm
  segLoad_e1_to_memcpy_wp_vm segLoad_e1_to_drop_wp_vm
  segLoad_e1_to_dealloc_wp_vm segLoad_e1_tail_wp_vm
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchPlacedBudget (
  segLoad_dispatch_err_budget segLoad_dispatch_none_budget
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlacedBudget (
  segLoad_dispatch_some_to_memcpy_wp_vm segLoad_dispatch_some_cur_tail_wp_vm
  segLoad_dispatch_some_budget
)

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt hiding
  h45_segLoad_placed_okVT h45_q_otr_placed h45_segSignal_enc_to_ret_pf_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad hiding segLoad_placed_okV
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  LibsignalCodeRoLoaded withLsCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding
  ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced
  EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced
  SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced
  SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced
  SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName
  cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced
  encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym
  lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec
  otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced
  withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed
  withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding
  EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok
  tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok
  tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
private theorem cs_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x20 = s0.readReg64 .x20 := h.2.1
private theorem cs_x21 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x21 = s0.readReg64 .x21 := h.2.2.1
private theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
private theorem cs_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x23 = s0.readReg64 .x23 := h.2.2.2.2.1
private theorem cs_x24 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x24 = s0.readReg64 .x24 := h.2.2.2.2.2.1
private theorem cs_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x25 = s0.readReg64 .x25 := h.2.2.2.2.2.2.1
private theorem cs_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x26 = s0.readReg64 .x26 := h.2.2.2.2.2.2.2.1
private theorem cs_x27 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x27 = s0.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
private theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
private theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
private theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

/-! ## 1. `E0` + `loadShim` + `loadPoll` + `E1` to `+0x160` under `EncEnvTFullBudget` -/

set_option maxHeartbeats 1600000 in
private theorem h45_segLoad_to_dispatch_budget [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s0)
    (hpc0 : s0.pc = encEntryPlaced) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).pre
        (x, st_init) s0 ∗ R)
    (hcont : ∀ (s : State) (st3 : M.σ) (sp : BitVec 64)
      (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
      (w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
      (_hfit0 : FitsEnv M lim st_init (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x))
      (evs_shim evs_poll : List AllocEvent),
      BoxAllocEnv kit.loadBoxSize evs_shim →
      kitEnv.loadPollEnv st0 x.rem.val evs_poll →
      st3 = M.stepEvents (rustDeallocEvents kit.loadBoxSize 8)
        (M.stepEvents evs_poll (M.stepEvents evs_shim st_init)) →
      SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
        st_init st3 (LoadRemEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x) →
      sp = s0.sp - 0xbe0#64 →
      s.pc = encEntryPlaced + 0x160#64 →
      encMidMetaPlaced x s0 s →
      x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStackV kit ikit ≤ s0.sp.toNat →
      w0 ≠ 0xFFFFFFFFFFFFFFFD#64 → tail.length = 312 →
      kit.loadRel st0 x.rem.val ans →
      s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans →
      s.readReg64 .x24 = w0 → s.readReg64 .x27 = w1 →
      s.readReg64 .x21 = w2 → s.readReg64 .x23 = w3 →
      s.readReg64 .x25 = sp + 0x580#64 →
      s.readReg64 .x26 = sp + 0x9d0#64 →
      s.readReg64 .x28 = sp + 0x4a0#64 →
      s.pstate = addsPState64 w0 2#64 →
      (s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st3 s ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R s0 s
        (fun s' => ∃ st' r g sess,
          CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
            x st_init st' r g sess R s0 s')) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s0
      (fun s' => ∃ st' r g sess,
        CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r g sess R s0 s') := by
  let envF := h45_envF_budget hEnv
  obtain ⟨hcrl0, hm0⟩ := StoreKit.extract_withLsCodeRoLoaded hm0
  dsimp only [withStoresEncBudgetSpecV] at hm0
  rw [cliTapeAt_eq_pure_sep_cliTapeAfter_zero] at hm0
  have hpull0 :
      (⌜FitsEnv M lim st_init
            (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) ∧
          s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
          s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗
        (⌜x.rest.length < 2 ^ 63⌝ ∗ cliTapeAfter ctl x.cur x.rest 0) ∗
        FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
        A.pool lim st_init s0) ∗ R =
      ⌜FitsEnv M lim st_init
          (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) ∧
        s0.readReg64 .x0 = x.ptA ∧ (s0.readReg64 .x1).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧ s0.readReg64 .x2 = x.remA ∧ s0.readReg64 .x3 = x.locA ∧
        x.locA ≠ 0#64 ∧
        s0.readReg64 .x4 = x.ssA ∧ s0.readReg64 .x5 = kit.ss_vt ∧
        s0.readReg64 .x6 = x.idA ∧ s0.readReg64 .x7 = ikit.id_vt ∧
        x.now.tvNsec.toNat < 10 ^ 9 ∧ s0.readReg64 .x8 = x.ret ∧
        withStoresEncStackV kit ikit ≤ s0.sp.toNat ∧
        kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
      (⌜x.rest.length < 2 ^ 63⌝ ∗
      ((nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
        (protocolAddressAt A.repAlloc x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool lim st_init s0 ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗
            cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0))) ∗ R)) := by
    sep_ac_rfl
  rw [hpull0] at hm0
  obtain ⟨⟨hfit0, hx0, hx1_nat, hpt_lt, hx2, hx3, hloc_ne, hx4, hx5, hx6, hx7, hnsec, hx8,
    hsp_le, haddr_ss, _haddr_id⟩, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  obtain ⟨hrest_lt, hm0⟩ := (satisfies_pure_sepConj _ _ _).mp hm0
  have hbud0 :
      SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st_init
        (SeqEnv (BoxAllocEnv kit.loadBoxSize)
          (SeqEnv (kitEnv.loadPollEnv st0 x.rem.val)
            (SeqEnv (· = rustDeallocEvents kit.loadBoxSize 8)
              (LoadRemEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x)))) :=
    (SeamBudget.init hfit0).narrow fun evs h => seqEnv3_reassoc evs h
  have hsub := encSubStackV_le_two_pow_64 kit ikit hsp_le
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.ptext.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm_vt := loadVtablesPlaced_intro hEnv.vtables hcrl0.2 hm0
  let F_e0 : SepProp :=
    protocolAddressAt A.repAlloc x.rem x.remA ∗ kit.storeAt x.ssA st0 ∗ A.pool lim st_init s0 ∗
      ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗
        cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist0)
  have hm_e0 : s0.mem ⊨
      (nowAt s0.sp x.now ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ loadVtablesAt kit ∗ emp) ∗
      (F_e0 ∗ R) := by
    dsimp only [F_e0]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm_vt
  refine SegExitBudget.of_sepWP (R0 := R) hm_e0
    (segLoad_shim_budget_wp_vm x s0 emp hsp_le rfl hpc0 hrun0 hal0
      hx0 hx1 hx2 hx3 hx4 hx5 hx6 hx7 hx8) ?_
  intro sm P_m _ hsteps_e0 hpcm hrunm hmm hpostm
  rcases hpostm with ⟨hvm0, v50, v470, v478, waker0, waker1, v830, v838, v840,
    hspm, halm, _hfsm, htrm, hx0m, hx1m, hx19m, hx29m, hvregsm, hx30m, rfl⟩
  have hcrlm : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem := hcrl0.of_keepsFrozen hsteps_e0.keepsFrozen
  have hprefm : s0.trace <+: sm.trace := by rw [htrm]
  let F_shim : SepProp :=
    shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.loadShimStack) ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      kit.storeAt x.ssA st0 ∗
      loadVtablesAt kit
  have hm_shim : sm.mem ⊨
      (kitLoadShimBudgetSpec M A lim kit).pre (⟨x.ssA, x.remA⟩, st_init) sm ∗ (F_shim ∗ R) := by
    dsimp only [kitLoadShimBudgetSpec, F_shim, F_e0, shimFramePlaced] at hmm ⊢
    rw [← A.pool_transport lim st_init s0 sm hvm0] at hmm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0m, hx1m, hbud0.1.seq_left⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmm⟩
  refine call_rocl_alloc_placed (R0 := R)
    (hEnv.kitOk.loadShim (callerProg := lsProg_464 Hk) (callerBlk := 464) (by decide))
    (⟨x.ssA, x.remA⟩, st_init) hpcm hrunm halm hx30m hprefm hcrlm hm_shim ?_
  intro sf1 hsteps_shim hpc1 hrun1 hsp1 hal1 hcs1 hcrl1 hm1
  dsimp only [kitLoadShimBudgetSpec] at hm1
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm1
  obtain ⟨evs_shim, ⟨hx1_1, _hbox_ne, _hbox_align, htr1, hevs_shim⟩, hm1⟩ := hm1
  have hbud1 := hbud0.advance hevs_shim
  set st1 := M.stepEvents evs_shim st_init
  set box := sf1.readReg64 .x0
  have hsp1' : sf1.sp = s0.sp - 0xbe0#64 := by rw [hsp1, hspm]
  let F_pre : SepProp :=
    A.live box kit.loadBoxSize 8 ∗ kit.loadBoxAt box x.ssA x.remA 0#8 ∗
      A.pool lim st1 sf1 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840) ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      kit.storeAt x.ssA st0
  have hm_pre : sf1.mem ⊨
      (((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ v470) ∗ ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ v478) ∗
        stackAt sf1.sp kit.loadShimStack ∗
        memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - kit.loadShimStack) ∗
        loadVtablesAt kit ∗ emp) ∗ (F_pre ∗ R) := by
    dsimp only [F_pre, F_shim] at hm1 ⊢
    rw [hsp1]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
  refine SegExitBudget.of_sepWP (R0 := R) hm_pre
    (segLoad_pre_poll_budget_wp_vm hsub hpc1 hrun1 hsp1' hal1 rfl hx1_1) ?_
  intro sm2 P_m2 _ hsteps_pre hpcm2 hrunm2 hmm2 hpostm2
  rcases hpostm2 with ⟨hvm_pre, hspm2, halm2, _hfsm2, htrm2, hx0m2, hx8m2, hx20m2,
    hx19m2, hx29m2, hvregsm2, hx30m2, rfl⟩
  have hcrlm2 : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem := hcrl1.of_keepsFrozen hsteps_pre.keepsFrozen
  have hprefm2 : s0.trace <+: sm2.trace := by rw [htrm2, htr1, htrm]
  have henv2 : kit.envOk sm2.fs.files :=
    ((hfs.of_steps ((hsteps_e0.trans hsteps_shim).trans hsteps_pre)).envOk_at (evs := [])
      (by rw [htrm2, htr1, htrm, List.append_nil]) (fun _ => NoFsEv.nil)).1
  let pollCall : LoadPollCall × BitVec 64 × kit.StoreState × M.σ :=
    (⟨box, s0.sp - 0xbe0#64 + 0x580#64, x.remA, x.rem⟩, x.ssA, st0, st1)
  let F_poll : SepProp :=
    ((s0.sp - 0xbe0#64 + 0x470#64) ↦₆₄ box) ∗
      ((s0.sp - 0xbe0#64 + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      loadVtablesAt kit ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 6 ∗
      ((s0.sp - 0xbe0#64 + 0x480#64) ↦₆₄ waker0) ∗ ((s0.sp - 0xbe0#64 + 0x488#64) ↦₆₄ waker1) ∗
      ((s0.sp - 0xbe0#64 + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xbe0#64 + 0x498#64) 0xe8 ∗
      memRegion (s0.sp - 0xbe0#64 + 0x6f8#64) 312 ∗
      ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ v830) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ v838) ∗
      ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ v840)
  have hm_poll : sm2.mem ⊨
      (kitLoadPollBudgetSpecS M A lim kit kitEnv Scope encRecord).pre pollCall sm2 ∗ (F_poll ∗ R) := by
    dsimp only [kitLoadPollBudgetSpecS, pollCall, F_poll, F_pre] at hmm2 ⊢
    rw [← A.pool_transport lim st1 sf1 sm2 hvm_pre] at hmm2
    rw [hspm2, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0m2, hx8m2, haddr_ss, hbud1.1.seq_left⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmm2⟩
  refine call_rocl_alloc_placed (R0 := R)
    (hEnv.kitOk.loadPoll (callerProg := lsProg_464 Hk) (callerBlk := 464) (by decide))
    pollCall hpcm2 hrunm2 halm2 hx30m2 hprefm2 hcrlm2
    (withEnvPre_pre_intro (φ := fun s => kit.envOk s.fs.files) henv2 hm_poll) ?_
  intro sf2 hsteps_poll hpc2 hrun2 hsp2 hal2 hcs2 hcrl2 hm2
  dsimp only [kitLoadPollBudgetSpecSE, withEnvPre, kitLoadPollBudgetSpecS, pollCall] at hm2
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm2
  obtain ⟨ans, evs_poll, ⟨hl, htr2, hevs_poll⟩, hm2⟩ := hm2
  have hbud2 := hbud1.advance hevs_poll
  set st2 := M.stepEvents evs_poll st1
  have hsp2' : sf2.sp = s0.sp - 0xbe0#64 := by rw [hsp2, hspm2]
  have hx20_2 : sf2.readReg64 .x20 = s0.sp - 0xbe0#64 + 0x580#64 := by rw [cs_x20 hcs2, hx20m2]
  have hm2_out : sf2.mem ⊨
      loadPollPlacedOutAtS Scope A.repAlloc (s0.sp - 0xbe0#64 + 0x580#64) ans ∗
      ((kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st2 sf2 ∗ stackAt (s0.sp - 0xbe0#64) kit.loadPollStack ∗ F_poll) ∗ R) := by
    rw [hspm2] at hm2
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
  have hm2_dec := Satisfies.mono
    (sepConj_mono_left (loadPollPlacedOutAtS_decompose_sp Scope A.repAlloc (s0.sp - 0xbe0#64) ans))
    hm2_out
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm2_dec
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, tail, ⟨hw0_ne, htail_len⟩, hm2_dec⟩ := hm2_dec
  let sp := s0.sp - 0xbe0#64
  let F_5a : SepProp :=
    ((sp + 0x5b8#64) ↦ₛ tail) ∗
      memRegion (sp + 0x6f8#64) 312 ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      ((sp + 0x470#64) ↦₆₄ box) ∗
      ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      loadVtablesAt kit ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (sp + 0x46a#64) 6 ∗
      ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
      ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8
  have hm_5a : sf2.mem ⊨
      (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
        ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
        ((sp + 0x5b0#64) ↦₆₄ w6) ∗
        ((sp + 0x830#64) ↦₆₄ v830) ∗ ((sp + 0x838#64) ↦₆₄ v838) ∗ ((sp + 0x840#64) ↦₆₄ v840)) ∗
      (F_5a ∗ R) := by
    dsimp only [F_5a, F_poll, sp] at hm2_dec ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2_dec
  refine SegExitBudget.of_sepWP (R0 := R) hm_5a
    (segLoad_e1_to_memcpy_wp_vm hpc2 hrun2 hsp2' hal2 hx20_2 hw0_ne) ?_
  rintro s3 P3 _ hsteps_5a hpc3 hrun3 hm3
    ⟨hvm_5a, rfl, hsp3, hal3, htr3, hx0_3, hx1_3, hx2_3, hx30_3,
      hx19_3, hx29_3, hvregs_3, hx24_3, hx27_3, hx21_3, hx23_3, hx25_3, hx28_3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps_5a.keepsFrozen
  let F_5b : SepProp :=
    (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
      ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((sp + 0x5b0#64) ↦₆₄ w6) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6)) ∗
    (LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      ((sp + 0x470#64) ↦₆₄ box) ∗
      ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      loadVtablesAt kit ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (sp + 0x46a#64) 6 ∗
      ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
      ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8)
  have hm_5b : s3.mem ⊨
      sessionMemcpyRegionBudgetSpec.pre (sp + 0x6f8#64, sp + 0x5b8#64, tail) s3 ∗ (F_5b ∗ R) := by
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, framelessMemcpySpec, F_5b, F_5a] at hm3 ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_3, hx1_3, by rw [hx2_3, htail_len]; rfl⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm3
  refine call_nopanic_placed (R0 := R) (memcpy_budget_ok envF)
    (sp + 0x6f8#64, sp + 0x5b8#64, tail) hpc3 hrun3 hal3 hx30_3 hm_5b ?_
  intro s4 hsteps_5b hpc4 hrun4 hsp4 hal4 hcs4 hm4
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec, framelessMemcpySpec] at hm4
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨hvm_5b, hm4⟩ := hm4
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨htr4, hm4⟩ := hm4
  have hcrl4 : StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem := hcrl3.of_keepsFrozen hsteps_5b.keepsFrozen
  have hsp4' : s4.sp = sp := by rw [hsp4, hsp3]
  have hm4_368 : s4.mem ⊨
      (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
        ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₆₄ w4) ∗ ((sp + 0x5a8#64) ↦₆₄ w5) ∗
        ((sp + 0x5b0#64) ↦₆₄ w6) ∗ ((sp + 0x5b8#64) ↦ₛ tail)) ∗
      (((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
        ((sp + 0x470#64) ↦₆₄ box) ∗
        ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - kit.loadPollStack) ∗
        loadVtablesAt kit ∗
        A.live box kit.loadBoxSize 8 ∗
        shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
        memRegion (sp + 0x46a#64) 6 ∗
        ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
        ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8 ∗ R) := by
    dsimp only [F_5b] at hm4
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm4
  have hm4_folded := Satisfies.mono
    (sepConj_mono_left (out368_fold sp w0 w1 w2 w3 w4 w5 w6 tail htail_len)) hm4_368
  let F_5c : SepProp :=
    ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
      ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
      ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50 ∗
      memRegion (sp + 0x46a#64) 6 ∗
      ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
      ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8
  have hm_5c : s4.mem ⊨
      (((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
        ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff))) ∗ (F_5c ∗ R) := by
    unfold loadVtablesAt at hm4_folded
    dsimp only [F_5c]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm4_folded
  refine SegExitBudget.of_sepWP (R0 := R) hm_5c
    (segLoad_e1_to_drop_wp_vm kit hpc4 hrun4 hsp4' hal4) ?_
  rintro s5 P5 _ hsteps_5c hpc5 hrun5 hm5
    ⟨hvm_5c, rfl, hsp5, hal5, htr5, _hx0_5, hx20_5, hx22_5, hx30_5,
      hx19_5, hx29_5, hvregs_5, hx24_5, hx27_5, hx21_5, hx23_5, hx25_5, hx28_5⟩
  have hcrl5 : StoreKit.LibsignalCodeRoLoaded lsmpl s5.mem := hcrl4.of_keepsFrozen hsteps_5c.keepsFrozen
  have hm5_46a : s5.mem ⊨
      (memRegion (sp + 0x46a#64) 6 ∗
        ((sp + 0x470#64) ↦₆₄ box) ∗ ((sp + 0x478#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
        ((sp + 0x480#64) ↦₆₄ waker0) ∗ ((sp + 0x488#64) ↦₆₄ waker1) ∗
        ((sp + 0x490#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x498#64) 0xe8) ∗
      ((((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
        ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
        ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - kit.loadPollStack) ∗
        A.live box kit.loadBoxSize 8 ∗
        shimFramePlaced kit ikit ist0 ctl x s0 v50) ∗ R) := by
    dsimp only [F_5c] at hm5
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm5
  have hm5_folded := Satisfies.mono
    (sepConj_mono_left (fold_46a_498 sp box (0#64 + kit.loadFutVtOff) waker0 waker1 0#64)) hm5_46a
  let F_5d : SepProp :=
    memRegion (sp + 0x46a#64) 0x116 ∗
      ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
      ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
      ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
      ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
      ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗ kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      A.live box kit.loadBoxSize 8 ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50
  have hm_5d : s5.mem ⊨ futDropBudgetSpec.pre () s5 ∗ (F_5d ∗ R) := by
    dsimp only [futDropBudgetSpec, F_5d]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm5_folded
  refine call_rocl_nopanic_placed (R0 := R)
    (hEnv.kitOk.loadFutDrop (callerProg := lsProg_464 Hk) (callerBlk := 464) (by decide))
    () hpc5 hrun5 hal5 hx30_5 hcrl5 hm_5d ?_
  intro s6 hsteps_5d hpc6 hrun6 hsp6 hal6 hcs6 hm6
  dsimp only [futDropBudgetSpec] at hm6
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm6
  obtain ⟨⟨htr6, hvm_5d⟩, hm6⟩ := hm6
  have hcrl6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem := hcrl5.of_keepsFrozen hsteps_5d.keepsFrozen
  have hsp6' : s6.sp = sp := by rw [hsp6, hsp5]
  have hx20_6 : s6.readReg64 .x20 = box := by rw [cs_x20 hcs6, hx20_5]
  have hx22_6 : s6.readReg64 .x22 = 0#64 + kit.loadFutVtOff := by rw [cs_x22 hcs6, hx22_5]
  have hm6_box : s6.mem ⊨
      kit.loadBoxAt box x.ssA x.remA 1#8 ∗
      ((((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64)) ∗
      ((memRegion (sp + 0x46a#64) 0x116 ∗
        ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
        ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
        ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        kit.storeAt x.ssA st0 ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
        memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
          (encSubStackV kit ikit - kit.loadPollStack) ∗
        A.live box kit.loadBoxSize 8 ∗
        shimFramePlaced kit ikit ist0 ctl x s0 v50) ∗ R)) := by
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm6
  have hm6_mem := Satisfies.mono
    (sepConj_mono_left (kit.loadBoxAt_memRegion box x.ssA x.remA 1#8)) hm6_box
  let F_5e : SepProp :=
    memRegion box kit.loadBoxSize ∗ A.live box kit.loadBoxSize 8 ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
      ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
      ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st2 sf2 ∗ stackAt sp kit.loadPollStack ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - kit.loadPollStack) ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50
  have hm_5e : s6.mem ⊨
      (((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
        ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64)) ∗ (F_5e ∗ R) := by
    dsimp only [F_5e]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm6_mem
  refine SegExitBudget.of_sepWP (R0 := R) hm_5e
    (segLoad_e1_to_dealloc_wp_vm kit hpc6 hrun6 hsp6' hal6 hx20_6 hx22_6) ?_
  rintro s7 P7 _ hsteps_5e hpc7 hrun7 hm7
    ⟨hvm_5e, rfl, hsp7, hal7, htr7, hx0_7, hx1_7, hx2_7, hx30_7,
      hx19_7, hx29_7, hvregs_7, hx24_7, hx27_7, hx21_7, hx23_7, hx25_7, hx28_7⟩
  have hcrl7 : StoreKit.LibsignalCodeRoLoaded lsmpl s7.mem := hcrl6.of_keepsFrozen hsteps_5e.keepsFrozen
  have hvm_2_7 : VmPreserved sf2 s7 :=
    hvm_5a.trans (hvm_5b.trans (hvm_5c.trans (hvm_5d.trans hvm_5e)))
  let F_5f : SepProp :=
    loadVtablesAt kit ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
      kit.storeAt x.ssA st0 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
        (encSubStackV kit ikit - allocHookStack) ∗
      shimFramePlaced kit ikit ist0 ctl x s0 v50
  have hm_5f : s7.mem ⊨
      (rustCliDeallocBudgetSpec M A lim).pre (box, kit.loadBoxSize, 8, st2) s7 ∗ (F_5f ∗ R) := by
    dsimp only [rustCliDeallocBudgetSpec, F_5f, F_5e, loadVtablesAt] at hm7 ⊢
    rw [← A.pool_transport lim st2 sf2 s7 hvm_2_7] at hm7
    have hstk := stack_encSub_poll_to_dealloc_eq kit ikit hsub (hsp7 : s7.sp = sp)
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_7, by rw [hx1_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kit.loadBoxSize_lt],
      by rw [hx2_7]; rfl,
      hx30_7.symm ▸ LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_blockPlacement_base_add
        464 0x158#64 (by decide) (by decide)⟩, ?_⟩
    refine Satisfies.mono ?_ hm7
    have hpull_stk :
        (((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
          ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64)) ∗
        ((memRegion box kit.loadBoxSize ∗ A.live box kit.loadBoxSize 8 ∗
          memRegion (sp + 0x46a#64) 0x116 ∗
          ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
          ((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
          ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗
          memRegion (sp + 0x580#64) 368 ∗
          ((sp + 0x6f8#64) ↦ₛ tail) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
          LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
          kit.storeAt x.ssA st0 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          A.pool lim st2 s7 ∗ stackAt sp kit.loadPollStack ∗
          memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
            (encSubStackV kit ikit - kit.loadPollStack) ∗
          shimFramePlaced kit ikit ist0 ctl x s0 v50) ∗ R) =
        (memRegion (sp - BitVec.ofNat 64 (encSubStackV kit ikit))
            (encSubStackV kit ikit - kit.loadPollStack) ∗
          stackAt sp kit.loadPollStack) ∗
        ((memRegion box kit.loadBoxSize ∗ A.live box kit.loadBoxSize 8 ∗ A.pool lim st2 s7) ∗
          ((((kit.ss_vt + 24#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗
            ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗
            ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗
            ((0#64 + kit.loadFutVtOff + 16#64) ↦₆₄ᵣ 8#64) ∗
            ((0#64 + kit.loadFutVtOff + 24#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff))) ∗
            memRegion (sp + 0x46a#64) 0x116 ∗
            memRegion (sp + 0x580#64) 368 ∗
            ((sp + 0x6f8#64) ↦ₛ tail) ∗
            ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗ ((sp + 0x840#64) ↦₆₄ w6) ∗
            LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
            kit.storeAt x.ssA st0 ∗
            protocolAddressAt A.repAlloc x.rem x.remA ∗
            shimFramePlaced kit ikit ist0 ctl x s0 v50) ∗ R) := by
      sep_ac_rfl
    rw [hpull_stk, hstk]
    exact Entails.of_eq (by sep_ac_rfl)
  refine call_nopanic_placed (R0 := R) (dealloc_budget_ok envF.toEncEnvBudget)
    (box, kit.loadBoxSize, 8, st2) hpc7 hrun7 hal7 hx30_7 hm_5f ?_
  intro s8 hsteps_5f hpc8 hrun8 hsp8 hal8 hcs8 hm8
  dsimp only [rustCliDeallocBudgetSpec] at hm8
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm8
  obtain ⟨⟨hacp8, _⟩, hm8⟩ := hm8
  have htr8 : s8.trace = s7.trace := hacp8.2.1
  have hbud3 := hbud2.advance rfl
  set st3 := M.stepEvents (rustDeallocEvents kit.loadBoxSize 8) st2
  have hcrl8 : StoreKit.LibsignalCodeRoLoaded lsmpl s8.mem := hcrl7.of_keepsFrozen hsteps_5f.keepsFrozen
  have hsp8' : s8.sp = sp := by rw [hsp8, hsp7]
  have hx24_8 : s8.readReg64 .x24 = w0 := by
    rw [cs_x24 hcs8, hx24_7, cs_x24 hcs6, hx24_5, cs_x24 hcs4, hx24_3]
  have hm_5g : s8.mem ⊨ emp ∗ ((A.pool lim st3 s8 ∗ stackAt s7.sp allocHookStack ∗ F_5f) ∗ R) := by
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm8
  refine SegExitBudget.of_sepWP (R0 := R) hm_5g
    (segLoad_e1_tail_wp_vm hpc8 hrun8 hsp8' hal8 hx24_8) ?_
  rintro sf Pf _ hsteps_5g hpcf hrunf hmf
    ⟨hvm_5g, rfl, hspf, half, htrf, hx19f, hx29f, hvregsf,
      hx24f, hx27f, hx21f, hx23f, hx25f, hx26f, hx28f, hpsf⟩
  have hcrlf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl8.of_keepsFrozen hsteps_5g.keepsFrozen
  have hm_out : sf.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x580#64) 368 ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st3 sf ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R := by
    rw [← A.pool_transport lim st3 s8 sf hvm_5g] at hmf
    have hstk_back := stack_encSub_dealloc_back_eq kit ikit hsub (hsp7 : s7.sp = sp)
    have hsp_split := encSubStack_split_extra_placed kit st0 ikit ist0 x s0 hsp_le
    dsimp only [F_5f, shimFramePlaced, dispatchFramePlaced, sp] at hmf hstk_back ⊢
    rw [emp_sepConj] at hmf
    refine Satisfies.mono ?_ hmf
    refine sepConj_mono_left ?_
    have hperm1 :
        (A.pool lim st3 sf ∗ stackAt s7.sp allocHookStack ∗
            (loadVtablesAt kit ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
              LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
              kit.storeAt x.ssA st0 ∗
              protocolAddressAt A.repAlloc x.rem x.remA ∗
              memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
                (encSubStackV kit ikit - allocHookStack) ∗
              (nowAt s0.sp x.now ∗
                encSavedRegs s0.sp s0 ∗
                memRegion (s0.sp - 0xbe0#64) 0x50 ∗
                ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
                encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
                ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
                memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
                ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
                memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
                memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
                (x.ptA ↦ₛ x.ptext) ∗
                protocolAddressAt A.repAlloc x.loc x.locA ∗
                memRegion x.ret 248 ∗
                cliTapeAfter ctl x.cur x.rest 0 ∗
                FromRecordCallees.lsLogOff ∗
                ikit.identityAt x.idA ist0))) =
        (memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
            (encSubStackV kit ikit - allocHookStack) ∗
          stackAt s7.sp allocHookStack) ∗
        (kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          LoadOutResPlaced Scope A.repAlloc ans w0 w1 w2 w3 w4 w5 w6 tail ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          A.pool lim st3 sf ∗ loadVtablesAt kit ∗
          nowAt s0.sp x.now ∗
          encSavedRegs s0.sp s0 ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ v50) ∗
          encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x110#64) 0x358 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
          (x.ptA ↦ₛ x.ptext) ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          memRegion x.ret 248 ∗
          cliTapeAfter ctl x.cur x.rest 0 ∗
          FromRecordCallees.lsLogOff) := by
      sep_ac_rfl
    rw [hperm1, hstk_back]
    have hperm2 :
        stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) ∗
          (kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0) =
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
          stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) := by sep_ac_rfl
    rw [← sepConj_assoc, hperm2]
    refine Entails.trans (sepConj_mono_left hsp_split) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine hcont sf st3 sp ans w0 w1 w2 w3 w4 w5 w6 v50 tail
    hfit0 evs_shim evs_poll hevs_shim hevs_poll rfl hbud3 rfl
    hpcf ⟨hrunf, hspf, hal0, half, ?_, ?_, hcrlf, ?_⟩
    ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
    hw0_ne htail_len hl ?_ hx24f ?_ ?_ ?_ ?_ hx26f ?_ hpsf hm_out
  · rw [hx29f, cs_x29 hcs8, hx29_7, cs_x29 hcs6, hx29_5, cs_x29 hcs4, hx29_3, cs_x29 hcs2, hx29m2, cs_x29 hcs1, hx29m]
  · rw [hx19f, cs_x19 hcs8, hx19_7, cs_x19 hcs6, hx19_5, cs_x19 hcs4, hx19_3, cs_x19 hcs2, hx19m2, cs_x19 hcs1, hx19m]
  · rw [hvregsf, cs_vregs hcs8, hvregs_7, cs_vregs hcs6, hvregs_5, cs_vregs hcs4, hvregs_3, cs_vregs hcs2, hvregsm2, cs_vregs hcs1, hvregsm]
  · rw [htrf, htr8, htr7, htr6, htr5, htr4.2, htr3, htr2, htrm2, htr1, htrm]
  · rw [hx27f, cs_x27 hcs8, hx27_7, cs_x27 hcs6, hx27_5, cs_x27 hcs4, hx27_3]
  · rw [hx21f, cs_x21 hcs8, hx21_7, cs_x21 hcs6, hx21_5, cs_x21 hcs4, hx21_3]
  · rw [hx23f, cs_x23 hcs8, hx23_7, cs_x23 hcs6, hx23_5, cs_x23 hcs4, hx23_3]
  · rw [hx25f, cs_x25 hcs8, hx25_7, cs_x25 hcs6, hx25_5, cs_x25 hcs4, hx25_3]
  · rw [hx28f, cs_x28 hcs8, hx28_7, cs_x28 hcs6, hx28_5, cs_x28 hcs4, hx28_3]

/-! ## 2. Top-Level `h45_segLoad_placed_okVT` -/

set_option maxHeartbeats 1600000 in
theorem h45_segLoad_placed_okVT [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 : State)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s0)
    (hpc0 : s0.pc = encEntryPlaced) (hrun0 : s0.status = .Running) (hal0 : s0.spAligned = true)
    (hm0 : s0.mem ⊨
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).pre
        (x, st_init) s0 ∗ R) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s0
      (fun s' => ∃ st' r g sess,
        CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r g sess R s0 s') := by
  let envF := h45_envF_budget hEnv
  let envN := h45_envNone_budget hEnv
  refine h45_segLoad_to_dispatch_budget hEnv x st_init R s0 hfs hpc0 hrun0 hal0 hm0 ?_
  intro s st3 sp ans w0 w1 w2 w3 w4 w5 w6 v50 tail
    hfit0 evs_shim evs_poll hevs_shim hevs_poll hst3 hbud3
    hsp_eq hpc hmeta hbnds _hw0_ne3 htail
    hl htr hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps hm
  rcases ans with ⟨⟩ | (_ | r)
  · have hbudF :
        SeamBudget lim
          (WithStoresEncEnv (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
            (fun _ => False) C S sendEnv uuidTryParse x)
          st_init st3
          (LoadRemEnv C S sendEnv uuidTryParse (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
            (fun _ => False) x) :=
      hst3 ▸ h45_seamBudget_loadRem_of_prefix hfit0 hevs_shim hevs_poll (fun _ (h : False) => False.elim h)
    have hexit := segLoad_dispatch_err_budget envF x st_init st3 R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hbudF hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx27 hx21 hx23 hx25 hx26 hx28 hps hm
    rw [h45_segExitBudget_kitF_placed] at hexit
    exact h45_segExitBudget_scopeMono (fun _ (h : False) => False.elim h) hexit
      (fun _ => h45_curStateVBudget_of_false)
  · have hbudF :
        SeamBudget lim
          (WithStoresEncEnv (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
            (fun _ => False) C S sendEnv uuidTryParse x)
          st_init st3
          (LoadRemEnv C S sendEnv uuidTryParse (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
            (fun _ => False) x) :=
      hst3 ▸ h45_seamBudget_loadRem_of_prefix hfit0 hevs_shim hevs_poll (fun _ (h : False) => False.elim h)
    have hexit := segLoad_dispatch_none_budget envF x st_init st3 R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hbudF hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx24 hx26 hx28 hps hm
    rw [h45_segExitBudget_kitF_placed] at hexit
    exact h45_segExitBudget_scopeMono (fun _ (h : False) => False.elim h) hexit
      (fun _ => h45_curStateVBudget_of_false)
  · cases hcur : r.currentSession with
    | none =>
      have hmN : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
          memRegion (sp + 0x580#64) 368 ∗
          ((sp + 0x6f8#64) ↦ₛ tail) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
          ((sp + 0x840#64) ↦₆₄ w6) ∗
          LoadOutResPlaced (h45_ScopeNone_placed Scope) A.repAlloc (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          A.pool lim st3 s ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
          dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R := by
        refine Satisfies.mono ?_ hm
        exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (h45_loadOutRes_some_scopeNone_placed A.repAlloc w0 w1 w2 w3 w4 w5 w6 tail hcur))))))))
      have hbudN :
          SeamBudget lim
            (WithStoresEncEnv (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
              (h45_ScopeNone_placed Scope) C S sendEnv uuidTryParse x)
            st_init st3
            (LoadRemEnv C S sendEnv uuidTryParse (h45_kitF_placed kit) (h45_kitEnvF kit kitEnv) st0 ikit ikitEnv ist0
              (h45_ScopeNone_placed Scope) x) :=
        hst3 ▸ h45_seamBudget_loadRem_of_prefix hfit0 hevs_shim hevs_poll (fun _ (h : h45_ScopeNone_placed Scope _) => h.1)
      have hexit := segLoad_dispatch_some_budget envN x st_init st3 R s0 s r sp w0 w1 w2 w3 w4 w5 w6 v50 tail
        hbudN hsp_eq hpc hmeta hbnds htail hl htr hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps hmN
      rw [h45_segExitBudget_kitF_placed] at hexit
      exact h45_segExitBudget_scopeMono (fun _ (h : h45_ScopeNone_placed Scope _) => h.1) hexit
        (fun _ => h45_curStateVBudget_of_scopeNone)
    | some sess =>
      subst hsp_eq
      rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩
      rcases hbnds with ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
      have hm_drop : s.mem ⊨
          LoadOutResPlaced Scope A.repAlloc (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
          ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            protocolAddressAt A.repAlloc x.rem x.remA ∗
            A.pool lim st3 s ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
        refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
      clear hm
      rw [loadOutResPlaced_some_eq] at hm_drop
      obtain ⟨g, hm_drop1⟩ := satisfies_sepExists_left hm_drop
      clear hm_drop
      rw [sepConj_assoc] at hm_drop1
      obtain ⟨⟨hscope, hcap_lt, hw0_eq, hw1_eq, hw2_eq, hw3_eq_init, htail_inl⟩, hm_drop2⟩ :=
        satisfies_pure_left hm_drop1
      clear hm_drop1
      subst hw0_eq hw1_eq hw2_eq hw3_eq_init
      obtain ⟨hw0_ne1, hw0_ne2, _⟩ := ne_neg_tags_of_lt_two_pow_63 hcap_lt
      let sp := s0.sp - 0xbe0#64
      let F_1 : SepProp :=
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
          recordHeap A.repAlloc g r ∗
          memRegion (sp + 0x46a#64) 0x116 ∗
          memRegion (sp + 0x580#64) 368 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          A.pool lim st3 s ∗ stackAt sp encSubStack ∗
          memRegion (sp + 0x848#64) 0x338 ∗
          dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0
      have hm_1 : s.mem ⊨
          (((sp + 0x50#64) ↦₆₄ v50) ∗
            ((sp + 0x108#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 0x110#64) 0x358 ∗
            ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
            ((sp + 0x840#64) ↦₆₄ w6)) ∗ (F_1 ∗ R) := by
        dsimp only [F_1, sp]
        refine Satisfies.mono ?_ hm_drop2
        rw [dispatchFramePlaced_eq_rec_sep kit st0 ikit ist0 ctl x s0 v50]
        exact Entails.of_eq (by sep_ac_rfl)
      clear hm_drop2
      refine SegExitBudget.of_sepWP (R0 := R) hm_1
        (segLoad_dispatch_some_to_memcpy_wp_vm hpc hrun hsp hal hw0_ne1 hw0_ne2
          hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps) ?_
      rintro sm1 P1 _ hsteps_1 hpc1 hrun1 hm1
        ⟨hvm_1, rfl, hsp1, hal1, htr1, hx0_1, hx1_1, hx2_1, hx30_1,
          hx19_1, hx29_1, hvregs_1, hx20_1, hx22_1, hx23_1, hx25_1, hx26_1, hx28_1⟩
      have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl sm1.mem := hcrl.of_keepsFrozen hsteps_1.keepsFrozen
      let F_2 : SepProp :=
        (((sp + 0x110#64) ↦₆₄ g.prevCap) ∗ ((sp + 0x118#64) ↦₆₄ g.prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ ((sp + 0x128#64) ↦₆₄ recordCurCap g) ∗
          ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
          ((sp + 0x140#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x280#64) 0x1e8 ∗
          ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
          ((sp + 0x108#64) ↦₆₄ x.remA) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
          ((sp + 0x840#64) ↦₆₄ w6)) ∗
        (recordHeap A.repAlloc g r ∗
          memRegion (sp + 0x46a#64) 0x116 ∗
          memRegion (sp + 0x580#64) 368 ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          A.pool lim st3 s ∗ stackAt sp encSubStack ∗
          memRegion (sp + 0x848#64) 0x338 ∗
          dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0)
      have hm_2 : sm1.mem ⊨
          sessionMemcpyRegionBudgetSpec.pre (sp + 0x148#64, sp + 0x6f8#64, tail) sm1 ∗ (F_2 ∗ R) := by
        dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, framelessMemcpySpec, memcpyRegionSpec, F_2, F_1] at hm1 ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj]
        refine ⟨⟨hx0_1, hx1_1, by rw [hx2_1, htail]; rfl⟩, ?_⟩
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
      refine call_nopanic_placed (R0 := R) (memcpy_budget_ok envF)
        (sp + 0x148#64, sp + 0x6f8#64, tail) hpc1 hrun1 hal1 hx30_1 hm_2 ?_
      intro sm2 hsteps_2 hpc2 hrun2 hsp2 hal2 hcs2 hm2
      dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, framelessMemcpySpec, memcpyRegionSpec] at hm2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
      obtain ⟨hvm_2, hm2⟩ := hm2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
      obtain ⟨⟨_hx0_2, htr2⟩, hm2⟩ := hm2
      have hcrl2 : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem := hcrl1.of_keepsFrozen hsteps_2.keepsFrozen
      have hsp2' : sm2.sp = sp := by rw [hsp2, hsp1]
      have hx20_2 : sm2.readReg64 .x20 = sp + 0x58#64 := by rw [cs_x20 hcs2, hx20_1]
      have hx23_2 : sm2.readReg64 .x23 = recordCurCap g := by rw [cs_x23 hcs2, hx23_1]
      have hx25_2 : sm2.readReg64 .x25 = sp + 0x580#64 := by rw [cs_x25 hcs2, hx25_1]
      have hx26_2 : sm2.readReg64 .x26 = sp + 0x9d0#64 := by rw [cs_x26 hcs2, hx26_1]
      have hx28_2 : sm2.readReg64 .x28 = sp + 0x4a0#64 := by rw [cs_x28 hcs2, hx28_1]
      have hvm_s_2 : VmPreserved s sm2 := hvm_1.trans hvm_2
      have hbud_cur : SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
          st_init st3 (FromCurEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x) :=
        hbud3.narrow fun _ h => Or.inr (Or.inr h)
      have hm2_pure : sm2.mem ⊨
          ⌜recordCurCap g ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
          ((((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail) ∗ F_2) ∗ R) := by
        dsimp only [F_2] at hm2 ⊢
        refine Satisfies.mono ?_ hm2
        have hpull_rh :
            (((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail)) ∗
              ((((sp + 0x110#64) ↦₆₄ g.prevCap) ∗ ((sp + 0x118#64) ↦₆₄ g.prevPtr) ∗
                ((sp + 0x120#64) ↦₆₄ 0#64) ∗ ((sp + 0x128#64) ↦₆₄ recordCurCap g) ∗
                ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
                ((sp + 0x140#64) ↦₆₄ w6) ∗
                memRegion (sp + 0x280#64) 0x1e8 ∗
                ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
                ((sp + 0x108#64) ↦₆₄ x.remA) ∗
                ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
                ((sp + 0x840#64) ↦₆₄ w6)) ∗
              (recordHeap A.repAlloc g r ∗
                memRegion (sp + 0x46a#64) 0x116 ∗
                memRegion (sp + 0x580#64) 368 ∗
                protocolAddressAt A.repAlloc x.rem x.remA ∗
                A.pool lim st3 s ∗ stackAt sp encSubStack ∗
                memRegion (sp + 0x848#64) 0x338 ∗
                dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0)) ∗ R =
            recordHeap A.repAlloc g r ∗
              ((((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail) ∗
                ((((sp + 0x110#64) ↦₆₄ g.prevCap) ∗ ((sp + 0x118#64) ↦₆₄ g.prevPtr) ∗
                  ((sp + 0x120#64) ↦₆₄ 0#64) ∗ ((sp + 0x128#64) ↦₆₄ recordCurCap g) ∗
                  ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
                  ((sp + 0x140#64) ↦₆₄ w6) ∗
                  memRegion (sp + 0x280#64) 0x1e8 ∗
                  ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
                  ((sp + 0x108#64) ↦₆₄ x.remA) ∗
                  ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
                  ((sp + 0x840#64) ↦₆₄ w6)) ∗
                (memRegion (sp + 0x46a#64) 0x116 ∗
                  memRegion (sp + 0x580#64) 368 ∗
                  protocolAddressAt A.repAlloc x.rem x.remA ∗
                  A.pool lim st3 s ∗ stackAt sp encSubStack ∗
                  memRegion (sp + 0x848#64) 0x338 ∗
                  dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0))) ∗ R) := by
          sep_ac_rfl
        rw [hpull_rh]
        refine Entails.trans (sepConj_mono_left (curSession_some_of_recordTailInline htail_inl hcur)) ?_
        exact Entails.of_eq (by sep_ac_rfl)
      obtain ⟨hw3_ne, hm2_cur⟩ := satisfies_pure_left hm2_pure
      clear hm2 hm2_pure
      have hm_cur_emp : sm2.mem ⊨
          emp ∗ ((((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail) ∗ F_2) ∗ R) :=
        Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2_cur
      refine SegExitBudget.of_sepWP (R0 := R) hm_cur_emp
        (segLoad_dispatch_some_cur_tail_wp_vm hpc2 hrun2 hsp2' hal2 hw3_ne hx20_2 hx23_2) ?_
      rintro sf Pf _ hsteps_3 hpcf hrunf hm_f
        ⟨hvm_3, rfl, hspf, half, htrf, hx19f, hx29f, hvregsf, hx20f, hx21f, hx25f, hx26f, hx28f⟩
      have hcrlf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl2.of_keepsFrozen hsteps_3.keepsFrozen
      have hvm_s_f : VmPreserved s sf := hvm_s_2.trans hvm_3
      refine SegExitBudget.next ⟨st3, r, g, sess, hbud_cur, hcur, ⟨hscope, hl⟩, ?_⟩
      refine ⟨hpcf,
        ⟨hrunf, hspf, hal0, half,
          by rw [hx29f, cs_x29 hcs2, hx29_1, hx29],
          by rw [hx19f, cs_x19 hcs2, hx19_1, hx19], hcrlf,
          by rw [hvregsf, cs_vregs hcs2, hvregs_1, hvregs]⟩,
        by rw [htrf, htr2, htr1, htr]; rfl,
        ⟨hx20f, hx21f, by rw [hx25f, hx25_2], by rw [hx26f, hx26_2], by rw [hx28f, hx28_2]⟩,
        hpt_lt, hrest_lt, hloc_ne, hnsec, enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩
      dsimp only [EncSeamVPlaced, curScratch, F_2, sp] at hm_f ⊢
      rw [← A.pool_transport lim st3 s sf hvm_s_f] at hm_f
      refine Satisfies.mono ?_ hm_f
      have hrec_words := recordWords56At_fold_sp110 (s0.sp - 0xbe0#64)
        g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6
      have hrec := sessionRecordAt_of_words56_sep_tail A.repAlloc
        (s0.sp - 0xbe0#64 + 0x110#64) g r htail_inl
      have h38 : (s0.sp - 0xbe0#64 + 0x110#64) + 0x38#64 = s0.sp - 0xbe0#64 + 0x148#64 := by bv_arith
      rw [h38] at hrec
      have hrec_full :
          (((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
            ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
            ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ recordCurCap g) ∗
            ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6)) ∗
          ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
          recordHeap A.repAlloc g r ⊢
          sessionRecordAt (A.atState lim st3 sf) (s0.sp - 0xbe0#64 + 0x110#64) g r :=
        Entails.trans (sepConj_mono_left hrec_words) hrec
      have h46a := memRegion_0x46a_0x716_fold (s0.sp - 0xbe0#64) w4 w5 w6 tail htail
      have hspills := encSpillsAt_fold kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x
      have hperm_cur :
          emp ∗
            ((((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
              ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
              ((((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
                ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
                ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
                ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ recordCurCap g) ∗
                ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
                ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
                ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6) ∗
                memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
                ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
                ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
                ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
                ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
                ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6)) ∗
              (recordHeap A.repAlloc g r ∗
                memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
                memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
                protocolAddressAt A.repAlloc x.rem x.remA ∗
                A.pool lim st3 sf ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
                memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
                dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0))) ∗ R) =
          ((((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
            ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
            ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ recordCurCap g) ∗
            ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6)) ∗
            ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗ recordHeap A.repAlloc g r) ∗
          (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
            memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338) ∗
          (memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
            memRegion (s0.sp - 0xbe0#64) 0x50 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            memRegion x.ret 248 ∗
            encCommonPlaced (A.atState lim st3 sf) ctl x 0 s0 ∗
            (encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st3 sf) kit) st0
              (retagIdentityStore (A' := A.atState lim st3 sf) ikit) ist0 x s0 ∗ R)) := by
        dsimp only [dispatchFrameNoRecPlaced, encCommonPlaced]
        change _ = _ ∗ (_ ∗ (_ ∗ (_ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗
          ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
            protocolAddressAt A.repAlloc x.loc x.locA ∗
            nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
            stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st3 sf) ∗
          (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R))))
        sep_ac_rfl
      rw [hperm_cur]
      refine Entails.trans (sepConj_mono hrec_full (sepConj_mono hspills (sepConj_mono_left h46a))) ?_
      change sessionRecordAt (A.atState lim st3 sf) (s0.sp - 0xbe0#64 + 0x110#64) g r ∗
        encSpillsAtV (retagSessionStore (A' := A.atState lim st3 sf) kit).ss_vt
          (retagIdentityStore (A' := A.atState lim st3 sf) ikit).id_vt (s0.sp - 0xbe0#64) x ∗ _ ⊢ _
      exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5PlacedBudget
