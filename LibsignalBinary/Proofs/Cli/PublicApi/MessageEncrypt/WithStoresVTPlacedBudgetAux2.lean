/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux1
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStalenessPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyStalePlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyBody
public import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommonPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatch

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Aux 2): `SegPreKey` Prefix (`+0x344..+0x8b4`)

Proves `h45_segPreKey_unackItems_to_dur_placed_ok`, `h45_segPreKey_staleness_to_add_placed_ok`,
`h45_segPreKey_stale_placed_ok`, and `h45_segPreKey_regId_kyber_placed_ok` under `EncEnvTBudget` /
`EncEnvTFullBudget` on Block `464` (`lsProg_464 H`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux2

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlacedBudget
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems (subroutine_ok_merge_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (lsRetAddr624_of_lr_eq_blockPlacement_base_add)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStalenessPlacedBudget (
  pollWithBaseKey_placed StalenessDurStatePlaced StalenessDurStateBudget
  StalenessAddStatePlaced StalenessAddStateBudget
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailPlacedBudget (
  PreKeyEncryptStateBudget
)

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey hiding
  segPreKey_encrypt_call_placed_ok segPreKey_encrypt_err_placed_ok segPreKey_buildMessage_placed_ok
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] blkPl_198_ρ_lanon122

private theorem lsLogOff_eq [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

private theorem poll_unackItems_pack_pollWithBaseKey_placed (sp : BitVec 64) (items : PendingPreKey)
    (ts : SystemTime) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x298 ∗
      memRegion (sp + 0x870#64) 36 ∗
      memRegion (sp + 0x894#64) 0x21c ∗
      memRegion (sp + 0xab0#64) 4 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0xb0c#64) 4 ∗
      memRegion (sp + 0xb10#64) 0x70) ⊢
    pollWithBaseKey_placed sp items ts := by
  unfold pollWithBaseKey_placed
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 88 0x4dc (by decide),
      mr_cut_add sp 0x5d8 0x298 0x244 (by decide),
      mr_cut_add sp 0x870 36 0x220 (by decide),
      mr_cut_add sp 0x894 0x21c 4 (by decide)]
  simp only [sepConj_assoc]
  exact Entails.refl _

private theorem pollWithBaseKey_dur_unpack_placed (sp : BitVec 64) (items : PendingPreKey)
    (ts : SystemTime) :
    pollWithBaseKey_placed sp items ts =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 24 ∗
      memRegion (sp + 0x598#64) 0x300 ∗
      memRegion (sp + 0x898#64) 8 ∗
      memRegion (sp + 0x8a0#64) 0x214 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0xb0c#64) 4 ∗
      memRegion (sp + 0xb10#64) 0x70 := by
  unfold pollWithBaseKey_placed
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 24 0x51c (by decide),
      mr_cut_add sp 0x598 0x300 0x21c (by decide),
      mr_cut_add sp 0x898 8 0x214 (by decide)]
  simp only [sepConj_assoc]

private theorem durationSinceBounded_b00_intro_placed (sp : BitVec 64) (tvSec : BitVec 64)
    (tvNsec : BitVec 32) (hns : tvNsec.toNat < 1000000000) :
    (((sp + 0xb00#64) ↦₆₄ tvSec) ∗ ((sp + 0xb08#64) ↦₃₂ tvNsec) ∗ memRegion (sp + 0xb0c#64) 4) ⊢
      (∃∗ tvSec : BitVec 64, ∃∗ tvNsec : BitVec 32,
        ⌜tvNsec.toNat < 1000000000⌝ ∗
        ((sp + 0xb00#64) ↦₆₄ tvSec) ∗ (((sp + 0xb00#64) + 8#64) ↦₃₂ tvNsec) ∗
        memRegion ((sp + 0xb00#64) + 12#64) 4) := by
  refine Entails.sepExists_right tvSec (Entails.sepExists_right tvNsec ?_)
  refine Entails.pure_right hns ?_
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using Entails.refl _

private theorem vecU8_580_unpack_buf (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 1408#64) bs ⊢
      ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
        ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  have h1408 : sp + 1408#64 = sp + 0x580#64 := by bv_omega
  rw [h1408, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.vecU8_eq_words3_sep_buf]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
    Entails.sepExists_right ptr (Entails.sepExists_right cap ?_)
  have ha1 : sp + 0x580#64 + 8#64 = sp + 0x588#64 := by bv_omega
  have ha2 : sp + 0x580#64 + 0x10#64 = sp + 0x590#64 := by bv_omega
  rw [ha1, ha2]
  exact Entails.refl _

private theorem kyberMapBudgetSpec_pre_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (xc : KyberMapCall) (st : M.σ) (sm : State) :
    (kyberMapBudgetSpec M A lim).pre (xc, st) sm =
      ⌜FitsEnv M lim st (KyberOptEnv (xc.kp.map (·.ciphertext))) ∧
        (sm.readReg64 .x0 = xc.out ∧ sm.readReg64 .x1 = xc.arg)⌝ ∗
      (kyberArgAt xc ∗ memRegion xc.out 24 ∗ A.pool lim st sm ∗
        stackAt sm.sp (allocHookStack + 0x40)) := by
  dsimp only [kyberMapBudgetSpec, kyberMapSpec]
  apply ProofLib.sepProp_eq_of_entails
  · exact Entails.pure_left fun h1 => Entails.pure_left fun h2 => Entails.pure_right ⟨h1, h2⟩ (Entails.refl _)
  · exact Entails.pure_left fun ⟨h1, h2⟩ => Entails.pure_right h1 (Entails.pure_right h2 (Entails.refl _))

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_unackItems_to_dur_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg4PlacedBudget.EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hpk : sess.pendingPreKey = some items)
    (hkey : KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen,
        StalenessDurStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hkey with ⟨hbud, hcur, hscope, hotr, hrem, hpc, hmeta, htr, hregs,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at hscope htr hmem
  rcases hregs with ⟨hx0, hx8, hx20, hx22, hx23, hx25, hx26, hx27, hx28⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  rw [sp_sub_60_eq_add_b80 s0.sp] at hx29
  set sp := s0.sp - 0xbe0#64
  unfold keyPCPlaced encEntryPlaced at hpc
  have hunack := hEnv.callees.unack
  clear hEnv
  apply segExitBudget_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 1732#64)
    (encSeam_mem_group hmem)
  dsimp only [takenSlots, encCommonPlaced]
  rw [show sessionRecordAt (A.atState lim st s) = sessionRecordAt A.repAlloc from rfl,
      show otrAt (A.atState lim st s) = otrAt A.repAlloc from rfl,
      show protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc from rfl,
      show (A.atState lim st s).pool = A.pool lim st s from rfl]
  rw [poll_unackItems_regions sp, encSubStack_split_unack hsp]
  refine SepWPp.fold (takenRecord_sessionRecordAt_unpack A.repAlloc sp sess taken) (by sep_focus) ?_
  refine sepWPp_elim_ex fun prevCap => sepWPp_elim_ex fun prevPtr => sepWPp_elim_ex fun G => ?_
  dsimp only [lsProg_464, ite_true] at hunack ⊢
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP (mid := lsmpl.base 36)
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ProofLib.SepWPp.transport_budgetPool (s1 := s) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
  refine SepWPp.call_frame_rocl hunack
    (x := (⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ : UnackCall))
    (by wp_norm_goal) (by wp_norm_goal) hspAl
    (show _ = (blkPl_464).base + 840#64 by rfl)
    hcrl rfl ⟨by simp_all, by simp_all⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      exact onPanic_of_unack_budget htr hcur hscope hotr hrem hpk hm)
    fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
  dsimp only [unackItemsBudgetSpec, unackItemsPlacedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm1 => ?_
  refine ProofLib.SepWPp.transport_budgetPool hvm1 (hnext := ?_)
  rw [← sepConj_assoc, sepConj_comm (A.pool lim st s1), sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (unackOutAt_taken_some sp G.kyber sess items hpk) (by sep_focus) ?_
  refine sepWPp_elim_ex fun ts => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hts => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack32 (sp + 0x580#64) items.preKeyId) (by sep_focus)
    fun pkVal hpkVal => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack64 (sp + 0x588#64) (sess.pendingKyberPreKey.map (·.preKeyId)))
    (by sep_focus) fun kyIdVal hkyIdVal => ?_
  refine sepWPp_fold_ex5 (baseKeyShift_unpack_59c sp items.baseKey) (by sep_focus)
    fun bk0 bk1 bk2 bk3 bk4 hbk => ?_
  refine sepWPp_fold_ex2 (unackKyberSliceAt_unpack (sp + 0x5c0#64) G.kyber) (by sep_focus)
    fun kyPtr kyLen hkySlice => ?_
  refine SepWPp.fold (curScratch_unackItems_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun s48 => sepWPp_elim_ex fun s40 => sepWPp_elim_ex fun s38 =>
    sepWPp_elim_ex fun s34 => sepWPp_elim_ex fun s28 => sepWPp_elim_ex fun s24 =>
    sepWPp_elim_ex fun s18 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0x870#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w890 => sepWPp_elim_ex fun w888 => sepWPp_elim_ex fun w880 =>
    sepWPp_elim_ex fun w878 => sepWPp_elim_ex fun w870 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0xab0#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wad0 => sepWPp_elim_ex fun wac8 => sepWPp_elim_ex fun wac0 =>
    sepWPp_elim_ex fun wab8 => sepWPp_elim_ex fun wab0 => ?_
  refine SepWPp.fold (memRegion_16_ts_unpack_b00 sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wb08 => sepWPp_elim_ex fun wb00 => ?_
  wp_steps_sync_pool ((blkPl_464).base + 1732#64)
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
  refine SepWP.fold (baseKeyShift_pack_ab0 sp items.baseKey bk0 bk1 bk2 bk3 bk4 hbk) (by sep_focus) ?_
  refine SepWP.fold (cells36_entails_memRegion_36_870 sp bk0 bk1 bk2 bk3 bk4) (by sep_focus) ?_
  refine SepWP.fold
    (unackOut_cells_entails_memRegion_88_580 sp _ pkVal _ ts.tvSec ts.tvNsec bk0 bk1 bk2 bk3 bk4 kyPtr kyLen items.signedPreKeyId)
    (by sep_focus) ?_
  refine SepWP.fold (poll_unackItems_pack_pollWithBaseKey_placed sp items ts) (by sep_focus) ?_
  refine sepWP_fold_preKeyScratch sp kyLen _ items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey
    (by sep_focus) (by rfl) ?_
  refine SepWP.fold (encSubStack_pack_unack hsp _ _) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_f hmf
  dsimp only [StalenessDurStateBudget, StalenessDurStatePlaced, encEntryPlaced, sp]
    at hsp1 hx19_1 hx20_1 hx22_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
  refine ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen, hbud,
    hts, hpkVal, hkyIdVal, hkySlice, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · wp_norm_goal
  · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; wp_norm_goal; exact hsp0Al,
      by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
      by wp_norm_goal, hcrl_f, by wp_norm_goal⟩
  · dsimp only [retagSessionStore]; wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · cases items.preKeyId <;> wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced] at hmf ⊢
    rw [show (retagSessionStore (A' := A.atState lim st _) kit).ss_vt = kit.ss_vt from rfl,
        show (retagIdentityStore (A' := A.atState lim st _) ikit).id_vt = ikit.id_vt from rfl,
        show encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st _) kit) st0
          (retagIdentityStore (A' := A.atState lim st _) ikit) ist0 x s0 =
        encStoreExtraPlaced kit st0 ikit ist0 x s0 from rfl,
        show vecAt (A.atState lim st _) = vecAt A.repAlloc from rfl,
        show sessionStateReprAt (A.atState lim st _) = sessionStateReprAt A.repAlloc from rfl,
        show otrAt (A.atState lim st _) = otrAt A.repAlloc from rfl,
        show protocolAddressAt (A.atState lim st _) = protocolAddressAt A.repAlloc from rfl,
        show (A.atState lim st _).pool = A.pool lim st _ from rfl]
    arm64_sep_close

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_staleness_to_add_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg5PlacedBudgetAux.EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hdur : StalenessDurStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ expiry,
        StalenessAddStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  let envF := WithStoresVT.Seg5PlacedBudgetAux.h45_envF_budget hEnv
  rcases hdur with ⟨hbud, hts, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx2, hx8, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hmem
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have hts_nsec : ts.tvNsec.toNat < 10 ^ 9 := (unixEpoch_checkedAddSecs_tvNsec hts).2
  set sp := s0.sp - 0xbe0#64
  unfold encEntryPlaced at hpc
  have hdur_call := subroutine_ok_merge_withLsRet (fun _ _ => rfl) (durationSince_budget_ok_at_enc envF)
  have hadd_call := subroutine_ok_merge_withLsRet (fun _ _ => rfl) (timeAdd_budget_ok_at_enc envF)
  clear envF hEnv
  apply segExitBudget_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 1788#64)
    (dur_mem_group hmem)
  dsimp only [encCommonPlaced]
  rw [show vecAt (A.atState lim st s) = vecAt A.repAlloc from rfl,
      show sessionStateReprAt (A.atState lim st s) = sessionStateReprAt A.repAlloc from rfl,
      show otrAt (A.atState lim st s) = otrAt A.repAlloc from rfl,
      show protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc from rfl,
      show (A.atState lim st s).pool = A.pool lim st s from rfl]
  rw [pollWithBaseKey_dur_unpack_placed sp items ts, encSubStack_split_ext hsp]
  refine SepWPp.fold (durationSinceBounded_b00_intro_placed sp ts.tvSec ts.tvNsec hts_nsec) (by sep_focus) ?_
  dsimp only [lsProg_464, ite_true] at hdur_call hadd_call ⊢
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP
    (mid := lsρ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsDurationSinceSym)
  wp_step
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine ProofLib.SepWPp.transport_budgetPool (s1 := s) (by simp only [wp_norm, arm64_norm]) (hnext := ?_)
  refine CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.call_frame hdur_call
    (x := (sp + 0xb00#64, sp + 0x580#64))
    (by wp_norm_goal) (by wp_norm_goal) hspAl
    (show _ = (blkPl_464).base + 1736#64 by rfl)
    rfl
    ⟨lsRetAddr624_of_lr_eq_blockPlacement_base_add 464 1736#64 rfl,
      by simp_all, by simp_all, by dsimp [State.setPC, State.writeReg64, State.readReg64, Reg.x2] at hx2 ⊢; rw [hx2]; decide⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ hm => by
      dsimp only [durationSinceBoundedBudgetSpec, durationSinceBoundedSpec, Spec.onPanic] at hm
      rw [sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [durationSinceBoundedBudgetSpec, durationSinceBoundedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm1 => ?_
  refine ProofLib.SepWPp.transport_budgetPool hvm1 (hnext := ?_)
  rw [← sepConj_assoc, sepConj_comm (A.pool lim st s1), sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1; rw [hx23] at hx23_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  have hx21_1' : (s1.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s1.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_1]; exact hx21
  have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (dur_ret_24_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  refine SepWPp.fold (memRegion_8_898_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w898 => ?_
  wp_steps_sync_pool (lsρ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.lsTimeAddSym)
  refine CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.call_frame hadd_call
    (x := (ts, maxUnacknowledgedSessionAge))
    (by wp_norm_goal) (by wp_norm_goal)
    (by unfold State.spAligned at hsp1_al ⊢; rw [hsp1] at hsp1_al; wp_norm_goal)
    (show _ = (blkPl_464).base + 1788#64 by wp_norm_goal)
    rfl
    ⟨lsRetAddr624_of_lr_eq_blockPlacement_base_add 464 1788#64 (by wp_norm_goal),
      by wp_norm_goal, by wp_norm_goal, hts_nsec, by wp_norm_goal, by wp_norm_goal⟩
    (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      refine onPanic_of_timeAdd_budget (s := _) ?_ hcur hscope hotr hrem hpk hts hm
      wp_norm_goal)
    fun s2 hpc2 hstat2 hsp2 hcs2 => ?_
  dsimp only [timeAddBudgetSpec, timeAddSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hvm2 => ?_
  refine ProofLib.SepWPp.transport_budgetPool hvm2 (hnext := ?_)
  rw [← sepConj_assoc, sepConj_comm (A.pool lim st s2), sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hexp, htr2⟩ => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp2) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2 hsp2 htr2
  rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
  rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2; rw [hx27_1] at hx27_2; rw [hx28_1] at hx28_2; rw [hx29_1] at hx29_2; rw [hvregs_1] at hvregs_2
  have hx21_2' : (s2.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s2.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_2]; exact hx21_1'
  have hx24_2' : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s2.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_2]; exact hx24_1'
  rw [hsp1] at hsp2
  rw [htr1] at htr2
  apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
  refine SepWP.fold (pollWithBaseKey_dur_pack sp items w580 w588 _) (by sep_focus) ?_
  have hsp2_pack :
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt s2.sp extHookStack) ⊢ stackAt sp encSubStack := by
    rw [hsp2, ← encSubStack_split_ext rfl]
    exact Entails.refl _
  refine SepWP.fold hsp2_pack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_f hmf
  dsimp only [StalenessAddStateBudget, StalenessAddStatePlaced, encEntryPlaced, sp]
    at hsp2 hx19_2 hx20_2 hx22_2 hx25_2 hx26_2 hx28_2 hx29_2 hvregs_2 hmf ⊢
  refine ⟨⟨s2.readReg64 .x0, (s2.readReg64 .x1).setWidth 32⟩, hbud,
    hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc2, ?_, htr2, rfl, rfl,
    hx20_2, hx21_2', hx22_2, hx23_2, hx24_2', hx25_2, hx26_2, hx27_2, hx28_2,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · refine ⟨hstat2, hsp2, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; rw [hsp2]; wp_norm_goal,
      hx29_2, hx19_2, hcrl_f, hvregs_2⟩
  · dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced] at hmf ⊢
    rw [show (retagSessionStore (A' := A.atState lim st _) kit).ss_vt = kit.ss_vt from rfl,
        show (retagIdentityStore (A' := A.atState lim st _) ikit).id_vt = ikit.id_vt from rfl,
        show encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st _) kit) st0
          (retagIdentityStore (A' := A.atState lim st _) ikit) ist0 x s0 =
        encStoreExtraPlaced kit st0 ikit ist0 x s0 from rfl,
        show vecAt (A.atState lim st _) = vecAt A.repAlloc from rfl,
        show sessionStateReprAt (A.atState lim st _) = sessionStateReprAt A.repAlloc from rfl,
        show otrAt (A.atState lim st _) = otrAt A.repAlloc from rfl,
        show protocolAddressAt (A.atState lim st _) = protocolAddressAt A.repAlloc from rfl,
        show (A.atState lim st _).pool = A.pool lim st _ from rfl]
    arm64_sep_close

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_stale_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg5PlacedBudgetAux.EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = true)
    (hadd : StalenessAddStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False) := by
  rcases hadd with ⟨hbud, hts, hexp, _hpkVal, _hkyIdVal, _hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, _hx23, _hx24, hx25, hx26, _hx27, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hmem
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have ⟨hmod, hdraws⟩ := model_of_stale (C := C) (S := S) (x := x)
    hcur hotr hrem hpk hts hexp hlt
  have hbud_stale : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs) :=
    hbud.narrow fun _ h => Or.inr ⟨items, hpk, Or.inl h⟩
  have hfit_clone : FitsEnv M lim st (StringCloneEnv x.rem.name) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud_stale.1
  set sp := s0.sp - 0xbe0#64
  apply segExitBudget_trans
    (mid := fun sf =>
      ∃ st' cap ptr devWord,
        devWord.setWidth 8 = x.rem.device ∧
        sf.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv x st_init st'
          (preKeyErrAnswers r)
          (encEntryPlaced + 0x46c#64)
          (tailRegs cap ptr (BitVec.ofNat 64 x.rem.val.name.length))
          (fun sp => dropRecordSlots A.repAlloc sp curScratch ⟨prevCap, prevPtr, some G⟩
            (takenRecord sess taken) (some (pqCap, pqPtr, otr)) none
            (pollWith sp 0x9d0 [devWord, lsmpl.ρ lsMessageEncryptRodataSym, 15#64]) ∗
            (vecU8Buf A.repAlloc cap ptr x.rem.val.name ∗
              ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt")))
          R s0 sf)
  · unfold encEntryPlaced at hpc
    have hclone_call := stringClone_placed_ok_at_enc (WithStoresVT.Seg5PlacedBudgetAux.h45_envF_budget hEnv).toEncEnvBudget
    apply segExitBudget_of_sepWPp_lscro hcrl
      (target := (blkPl_464).base + 1132#64)
      (dur_mem_group hmem)
    dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced, protocolAddressAt, lsLogOff_eq]
    rw [show vecAt (A.atState lim st s) = vecAt A.repAlloc from rfl,
        show sessionStateReprAt (A.atState lim st s) = sessionStateReprAt A.repAlloc from rfl,
        show otrAt (A.atState lim st s) = otrAt A.repAlloc from rfl,
        show vecGhostAt (A.atState lim st s) = vecGhostAt A.repAlloc from rfl,
        show (A.atState lim st s).pool = A.pool lim st s from rfl]
    refine rodata_message_encrypt_placed_sepWPp hcrl.2 ?_
    refine SepWPp.fold (takenRecord_sessionRecordAt_pack_exact A.repAlloc sp prevCap prevPtr G sess taken)
      (by sep_focus) ?_
    refine SepWPp.fold (pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64))
      (by sep_focus) ?_
    refine SepWPp.fold (cmSlotAt_none_pack A.repAlloc sp k) (by sep_focus) ?_
    refine SepWPp.fold
      (preKeyScratch_stale_weaken sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
      (by sep_focus) ?_
    refine SepWPp.fold (pollWithBaseKey_stale_weaken sp items) (by sep_focus) ?_
    rw [poll_stale_split sp, encSubStack_split_ext hsp]
    refine SepWPp.fold (memRegion_16_unpack_598 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w5a0 => sepWPp_elim_ex fun w598 => ?_
    refine SepWPp.fold (memRegion_24_unpack_9d0 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w9e0 => sepWPp_elim_ex fun w9d8 => sepWPp_elim_ex fun w9d0 => ?_
    dsimp only [lsProg_464, ite_true] at hclone_call ⊢
    apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 623)
    wp_steps_sync_pool (lsmpl.base 623)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hcrl_call
    refine SepWPp.call_frame_rocl hclone_call
      (x := (x.remA, sp + 1408#64, x.rem.name, st))
      (by wp_norm_goal) (by wp_norm_goal)
      (by unfold State.spAligned at hspAl ⊢; wp_norm_goal; rw [← hsp]; exact hspAl)
      (show _ = (blkPl_464).base + 1948#64 by wp_norm_goal)
      hcrl_call
      rfl ⟨by wp_norm_goal, by wp_norm_goal, hfit_clone⟩
      (by dsimp only [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ hm => by
        dsimp only [stringCloneBudgetSpec, Spec.onPanic] at hm
        rw [sepConj_assoc] at hm
        exact (not_satisfies_false_sepConj hm).elim)
      fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
    dsimp only [stringCloneBudgetSpec]
    refine sepWPp_elim_ex fun evs_clone => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr1, hevs_clone⟩ => ?_
    refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm]
      at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
    rw [hx19] at hx19_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned at hspAl ⊢; rwa [hsp1]
    rw [hsp] at hsp1
    rw [htr] at htr1
    refine SepWPp.fold (vecU8_580_unpack_buf A.repAlloc sp x.rem.name.bytes) (by sep_focus) ?_
    refine sepWPp_elim_ex fun ptr => sepWPp_elim_ex fun cap => ?_
    wp_steps_sync_pool ((blkPl_464).base + 1132#64)
    apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
    refine SepWP.fold (curScratch_stale_pack sp) (by sep_focus) ?_
    refine SepWP.fold (pollWith_9d0_pack sp cap ptr _ _ _ _ _ _) (by sep_focus) ?_
    have hsp1_pack :
        (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt s1.sp extHookStack) ⊢ stackAt sp encSubStack := by
      rw [hsp1, ← encSubStack_split_ext rfl]
      exact Entails.refl _
    refine SepWP.fold hsp1_pack (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1 hmf
    have hfinal :
        kit.storeFinal st0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = st0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    have hidfinal :
        ikit.idFinal ist0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = ist0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    refine ⟨M.stepEvents evs_clone st, cap, ptr,
      (w598 &&& 0xffffffffffffff00#64) ||| BitVec.zeroExtend 64 x.rem.device,
      by ext i hi; simp, by wp_norm_goal, hbud_stale.advance hevs_clone, ?_⟩
    refine ⟨?_, ?_, ?_, hstack, ?_⟩
    · dsimp only [encEntryPlaced]; wp_norm_goal
    · dsimp only [encMidMetaPlaced, sp] at hsp1 hx19_1 hx29_1 hvregs_1 ⊢
      refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al,
        by unfold State.spAligned at hsp0Al ⊢; wp_norm_goal; exact hsp0Al,
        by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
        by wp_norm_goal, hcrl1, by wp_norm_goal⟩
    · dsimp only [tailRegs, AddrGhost.val, sp] at hx26_1 hx28_1 ⊢
      refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · rw [preKey_encTail_mem_retag_eq (A' := A.atState lim (M.stepEvents evs_clone st) _)
        kit st0 ikit ist0 C ctl S x (preKeyErrAnswers r) _ R s0]
      dsimp only [encEntryPlaced, encStoreExtraPlaced,
        tailRegs, dropRecordSlots, otrSlotAt, encSpillsAt, encSpillsAtV, encCommonPlaced,
        protocolAddressAt, lsLogOff_eq, AddrGhost.val, sp]
        at hmf ⊢
      rw [hdraws, hfinal, hidfinal,
        show vecGhostAt (A.atState lim (M.stepEvents evs_clone st) _) = vecGhostAt A.repAlloc from rfl,
        show (A.atState lim (M.stepEvents evs_clone st) _).pool =
          A.pool lim (M.stepEvents evs_clone st) _ from rfl]
      arm64_sep_close
  · intro sf ⟨st', cap, ptr, devWord, hdev, htr_sf, htail⟩
    have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r)
        (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 sf := by
      refine ⟨⟨congrArg Prod.fst hmod, by rw [congrArg Prod.snd hmod]; exact ⟨hscope.2, trivial⟩,
        by rw [congrArg Prod.snd hmod]; trivial⟩, ?_⟩
      rw [congrArg Prod.snd hmod, htr_sf, ikit.traceOfWith_load]
      rfl
    have hdev_word : CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.DevWord
        x.rem.val.device devWord := by
      refine ⟨(unpack64 devWord).tail, by rw [List.length_tail, unpack64_length], ?_⟩
      unfold unpack64
      dsimp only [List.tail_cons]
      rw [← BitVec.setWidth_eq_extractLsb' (by decide), hdev]
      rfl
    have hst :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.speStaged_sessionNotFound_devWord_placed
        A.repAlloc x.ret cap ptr devWord (lsmpl.ρ lsMessageEncryptRodataSym) x.rem.val hdev_word
    exact hEnv.tailDropRecord x st_init st' R s0 sf (preKeyErrAnswers r)
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.val.name.length) devWord
      (lsmpl.ρ lsMessageEncryptRodataSym) 15#64
      (vecU8Buf A.repAlloc cap ptr x.rem.val.name ∗
        ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt"))
      curScratch (Or.inl rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
      (some (pqCap, pqPtr, otr)) hm hst htail

set_option maxHeartbeats 800000 in
theorem h45_segPreKey_regId_kyber_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : WithStoresVT.Seg5PlacedBudgetAux.EncEnvTFullBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = false)
    (hadd : StalenessAddStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R s0 s
      (fun sf => ∃ st',
        PreKeyEncryptStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st' r sess otr taken pqCap pqPtr k items R s0 sf) := by
  rcases hadd with ⟨hbud, hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, hx23, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hmem
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have hky_bound := (hEnv.toEncEnvTBudget.scopeIn r hscope sess hcur).2.2.2
  have hbud_ky : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (SeqEnv (KyberOptEnv (sess.pendingKyberPreKey.map (·.ciphertext)))
        (FromPreKeyEncEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items)) :=
    hbud.narrow fun _ h => Or.inr ⟨items, hpk, Or.inr h⟩
  have hfit_ky : FitsEnv M lim st (KyberOptEnv (sess.pendingKyberPreKey.map (·.ciphertext))) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud_ky.1
  set sp := s0.sp - 0xbe0#64
  unfold encEntryPlaced at hpc
  have hkyber_call := hEnv.calleesFull.kyber
  clear hEnv
  apply segExitBudget_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 2228#64)
    (dur_mem_group hmem)
  rw [show vecAt (A.atState lim st s) = vecAt A.repAlloc from rfl,
      show sessionStateReprAt (A.atState lim st s) = sessionStateReprAt A.repAlloc from rfl,
      show otrAt (A.atState lim st s) = otrAt A.repAlloc from rfl]
  refine SepWPp.fold (sessionAt_regId_unpack A.repAlloc sp G sess taken) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hkyRel => ?_
  refine SepWPp.fold
    (preKeyScratch_regId_unpack sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
    (by sep_focus) ?_
  refine sepWPp_elim_ex fun w14 => ?_
  refine SepWPp.fold (pollWithBaseKey_regId_unpack sp items) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w590 => sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq]
  rw [show protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc from rfl,
      show (A.atState lim st s).pool = A.pool lim st s from rfl,
      encSubStack_split_kyber hsp]
  dsimp only [lsProg_464, ite_true] at hkyber_call ⊢
  cases hky : sess.pendingKyberPreKey with
  | none =>
    cases hGky : G.kyber with
    | some g =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | none =>
      rw [hky] at hbud_ky hfit_ky
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      subst hkySlice
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 430)
      wp_steps_sync_pool (lsmpl.base 430)
      refine SepWP.fold (kyberArgAt_none_pack sp w580 w590) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hcrl_call
      let call : KyberMapCall := ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩
      have hfit' : FitsEnv M lim st (KyberOptEnv (call.kp.map (·.ciphertext))) := by
        simpa [call, hky] using hfit_ky
      refine SepWPp.call_frame_rocl hkyber_call
        (x := (call, st))
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        (show _ = (blkPl_464).base + 2228#64 by wp_norm_goal)
        hcrl_call
        (kyberMapBudgetSpec_pre_eq A lim call st _)
        ⟨hfit', by dsimp only [call]; wp_norm_goal, by dsimp only [call]; wp_norm_goal⟩
        (by dsimp [call, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun _ _ hm => by
          dsimp only [kyberMapBudgetSpec, Spec.onPanic] at hm
          rw [sepConj_assoc] at hm
          exact (not_satisfies_false_sepConj hm).elim)
        fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
      dsimp only [kyberMapBudgetSpec]
      refine SepWPp.fold (Entails.refl (∃∗ evs_ky : List AllocEvent, _)) (by sep_focus) ?_
      refine sepWPp_elim_ex fun evs_ky => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hevs_ky => ?_
      dsimp only [kyberMapSpec, call]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      set st' := M.stepEvents evs_ky st
      have hbud_enc := hbud_ky.advance (by simpa [call, hky] using hevs_ky)
      rw [show optKyberAt (A.atState lim st' s1) = optKyberAt A.repAlloc from rfl,
          show (A.atState lim st' s1).pool = A.pool lim st' s1 from rfl]
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold (kyberPost_unpack A.repAlloc (sp + 0x8a0#64) (sp + 0x580#64) 0#64 none) (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_none_to_memRegion sp) (by sep_focus) ?_
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      rw [← hGky]
      apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A.repAlloc sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A.repAlloc sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp kyLen _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold (pollPreKeyEncrypt_pack A.repAlloc sp bp items sess.pendingKyberPreKey none (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hcrl_f hmf
      refine ⟨st', hbud_enc, ?_⟩
      dsimp only [PreKeyEncryptState'Placed,
        preKeyEncryptScratch, preKeyEncryptScratch', pollPreKeyEncrypt, pollE6c', encMidMetaPlaced,
        encEntryPlaced, encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hcrl_f, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      rw [show (retagSessionStore (A' := A.atState lim st' s1) kit).ss_vt = kit.ss_vt from rfl,
          show (retagIdentityStore (A' := A.atState lim st' s1) ikit).id_vt = ikit.id_vt from rfl,
          show encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st' s1) kit) st0
            (retagIdentityStore (A' := A.atState lim st' s1) ikit) ist0 x s0 =
            encStoreExtraPlaced kit st0 ikit ist0 x s0 from rfl,
          show sessionRecordAt (A.atState lim st' s1) = sessionRecordAt A.repAlloc from rfl,
          show otrAt (A.atState lim st' s1) = otrAt A.repAlloc from rfl,
          show optKyberAt (A.atState lim st' s1) = optKyberAt A.repAlloc from rfl,
          show protocolAddressAt (A.atState lim st' s1) = protocolAddressAt A.repAlloc from rfl,
          show (A.atState lim st' s1).pool = A.pool lim st' s1 from rfl]
      arm64_sep_close
  | some ky =>
    cases hGky : G.kyber with
    | none =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | some g =>
      rw [hky] at hbud_ky hfit_ky
      rw [hGky, hky] at hkyRel
      dsimp only [KyberRel] at hkyRel
      rcases hkyRel with ⟨hkyBytes, _⟩
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      rcases hkySlice with ⟨rfl, rfl⟩
      have hkyId_eq : kyIdVal = ky.preKeyId := hkyIdVal ky.preKeyId (by simp [hky])
      subst hkyId_eq
      have hct_lt : ky.ciphertext.length < 2 ^ 32 := hky_bound ky hky
      rw [hkyBytes]
      refine SepWPp.fold (optTailVecAt_borrow A.repAlloc (sp + 0x250#64) g) (by sep_focus) ?_
      rw [sepConj_assoc, sepConj_assoc]
      refine SepWPp.pure_elim fun hptr => ?_
      rw [hkyBytes]
      dsimp only [Option.map, Option.isSome]
      have hptr_beq : (g.vec.ptr == 0#64) = false := _root_.beq_false_of_ne hptr
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 430)
      wp_steps_sync_pool (lsmpl.base 430)
      refine SepWP.fold (kyberArgAt_some_pack sp g.vec.ptr ky hptr hct_lt) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hcrl_call
      let call : KyberMapCall := ⟨sp + 0x8a0#64, sp + 0x580#64, g.vec.ptr,
        some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)⟩
      have hfit' : FitsEnv M lim st (KyberOptEnv (call.kp.map (·.ciphertext))) := by
        simpa [call, hky] using hfit_ky
      refine SepWPp.call_frame_rocl hkyber_call
        (x := (call, st))
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        (show _ = (blkPl_464).base + 2228#64 by wp_norm_goal)
        hcrl_call
        (kyberMapBudgetSpec_pre_eq A lim call st _)
        ⟨hfit', by dsimp only [call]; wp_norm_goal, by dsimp only [call]; wp_norm_goal⟩
        (by dsimp [call, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun _ _ hm => by
          dsimp only [kyberMapBudgetSpec, Spec.onPanic] at hm
          rw [sepConj_assoc] at hm
          exact (not_satisfies_false_sepConj hm).elim)
        fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
      dsimp only [kyberMapBudgetSpec]
      refine SepWPp.fold (Entails.refl (∃∗ evs_ky : List AllocEvent, _)) (by sep_focus) ?_
      refine sepWPp_elim_ex fun evs_ky => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hevs_ky => ?_
      dsimp only [kyberMapSpec, call]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      set st' := M.stepEvents evs_ky st
      have hbud_enc := hbud_ky.advance (by simpa [call, hky] using hevs_ky)
      rw [show optKyberAt (A.atState lim st' s1) = optKyberAt A.repAlloc from rfl,
          show (A.atState lim st' s1).pool = A.pool lim st' s1 from rfl]
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold
        (kyberPost_unpack A.repAlloc (sp + 0x8a0#64) (sp + 0x580#64) g.vec.ptr
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)))
        (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_some_unpack sp g.vec.ptr ky) (by sep_focus) ?_
      rw [← hkyBytes]
      refine SepWPp.fold (optTailVecAt_unborrow A.repAlloc (sp + 0x250#64) g) (by sep_focus) ?_
      rw [hkyBytes, ← hGky]
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A.repAlloc sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A.repAlloc sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp _ _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold
        (pollPreKeyEncrypt_pack A.repAlloc sp bp items sess.pendingKyberPreKey
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)) (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hcrl_f hmf
      refine ⟨st', hbud_enc, ?_⟩
      dsimp only [PreKeyEncryptState'Placed,
        preKeyEncryptScratch, preKeyEncryptScratch', pollPreKeyEncrypt, pollE6c', encMidMetaPlaced,
        encEntryPlaced, encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hcrl_f, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      rw [show (retagSessionStore (A' := A.atState lim st' s1) kit).ss_vt = kit.ss_vt from rfl,
          show (retagIdentityStore (A' := A.atState lim st' s1) ikit).id_vt = ikit.id_vt from rfl,
          show encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st' s1) kit) st0
            (retagIdentityStore (A' := A.atState lim st' s1) ikit) ist0 x s0 =
            encStoreExtraPlaced kit st0 ikit ist0 x s0 from rfl,
          show sessionRecordAt (A.atState lim st' s1) = sessionRecordAt A.repAlloc from rfl,
          show otrAt (A.atState lim st' s1) = otrAt A.repAlloc from rfl,
          show optKyberAt (A.atState lim st' s1) = optKyberAt A.repAlloc from rfl,
          show protocolAddressAt (A.atState lim st' s1) = protocolAddressAt A.repAlloc from rfl,
          show (A.atState lim st' s1).pool = A.pool lim st' s1 from rfl]
      arm64_sep_close

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVTPlacedBudgetAux2
