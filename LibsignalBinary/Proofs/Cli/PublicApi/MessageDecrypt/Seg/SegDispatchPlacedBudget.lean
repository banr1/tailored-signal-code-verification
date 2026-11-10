/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchAuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification
open LibsignalBinary.Heap LibsignalBinary.Proofs.Placed.BudgetVmSteps
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchAuxPlacedBudget
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoVerification.RustHeap
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch hiding apiDecResultAt_store_placed_of_words stagedRes_store_err_placed apiDecResultAt_sessionNotFound_placed_of_words stagedRes_sessionNotFound_placed messageDecrypt_of_sepWP_lscro messageDecrypt_of_sepWP_done_lscro messageDecrypt_call_panic_then_wp_lscro decSeg_of_sepWP_mid_placed decSeg_of_sepWP_done_placed decSeg_of_sepWPp_placed satisfies_rodata_msgDecryptStr_placed ls_hook_ok_197 stringClone_placed_ok msgDecrypt_memcpy_placed_ok msgDecrypt_dealloc_placed_ok stringClone_onPanic_entails_placed loadPollPlacedOutAt_err_entails loadPollPlacedOutAt_none_entails loadPollPlacedOutAt_some_entails loadPollBranchRestPlaced loadPollPlacedOutAt_entails_common wsFixedRestPlaced wsFixed_eq_active_rest_placed fold_wsFixed_assoc_placed branch_err_entails_placed wsNonePassivePlaced F_clonePlaced branch_none_pre_clone_entails_placed branch_none_post_entails_placed regionCommonBodyPlaced wsRegionFrameRestPlaced branch_some_common_entails_placed regionNone_of_common_placed regionSome_of_common_placed segDispatchVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch (
  apiDecResultAt_store_placed_of_words stagedRes_store_err_placed
  apiDecResultAt_sessionNotFound_placed_of_words stagedRes_sessionNotFound_placed
  messageDecrypt_of_sepWP_lscro messageDecrypt_of_sepWP_done_lscro
  messageDecrypt_call_panic_then_wp_lscro msgDecryptStrSym
  satisfies_rodata_msgDecryptStr_placed loadPollPlacedOutAt_err_entails
  loadPollPlacedOutAt_none_entails loadPollPlacedOutAt_some_entails
  loadPollBranchRestPlaced loadPollPlacedOutAt_entails_common
  wsFixedRestPlaced wsFixed_eq_active_rest_placed fold_wsFixed_assoc_placed
  branch_err_entails_placed wsNonePassivePlaced F_clonePlaced
  branch_none_pre_clone_entails_placed branch_none_post_entails_placed
  regionCommonBodyPlaced wsRegionFrameRestPlaced branch_some_common_entails_placed
  regionNone_of_common_placed regionSome_of_common_placed)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWP_seq_cut {prog : Program} (mid : BitVec 64) {tgt : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post := by
  apply SepWP.of_reaches_pc; intro R hm hL
  obtain ⟨sm, hs1, ⟨_, _, Pm, hmm, h2⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h hm hL
  · obtain ⟨sf, hs2, hout⟩ := SepWP.to_reaches_pc h2 hmm (hs1.codeLoaded hL)
    exact ⟨sf, hs1.trans hs2, hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem rep_protocolAddressAt_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp) :
    protocolAddressAt { pool := P, live := A.live } = protocolAddressAt A.repAlloc := rfl

private theorem rep_signalMessageAt_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp) :
    signalMessageAt { pool := P, live := A.live } = signalMessageAt A.repAlloc := rfl

private theorem rep_loadPollOut_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (P : SepProp) :
    loadPollPlacedOutAtS Scope { pool := P, live := A.live } = loadPollPlacedOutAtS Scope A.repAlloc := rfl

private theorem rep_loadPollBranchRest_eq {M : AllocCostModel} (A : RustCliAllocBudget M)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (P : SepProp) :
    loadPollBranchRestPlaced Scope { pool := P, live := A.live } =
      loadPollBranchRestPlaced Scope A.repAlloc := rfl

private theorem rep_wsFixedRest_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64) :
    wsFixedRestPlaced (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit) =
    wsFixedRestPlaced kit ikit := rfl

private theorem rep_decStoreExtra_eq [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64) :
    decStoreExtraPlaced (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit) =
    decStoreExtraPlaced kit ikit := rfl

private theorem rep_recordHeap_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (g : RecordGhost) (rec : SessionRecord (List (BitVec 8))) :
    recordHeap ({ pool := P, live := A.live }) g rec =
    recordHeap A.repAlloc g rec := by
  cases rec.currentSession <;> rfl

private theorem rep_vecGhostAt_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp) (v : VecGhost) (a : BitVec 64) :
    vecGhostAt ({ pool := P, live := A.live }) v a = vecGhostAt A.repAlloc v a := rfl

private theorem rep_F_clone_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp) (ctl : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (x : DecryptGhost) (s0 : State) (sp : BitVec 64) :
    F_clonePlaced ({ pool := P, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit)
      st0 ist0 x s0 sp =
    F_clonePlaced A.repAlloc ctl kit ikit st0 ist0 x s0 sp := rfl

set_option maxHeartbeats 3200000 in
theorem segDispatchVPlaced_ok [LibsignalPlacement] {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegDispatchSpecVBudget C A lim ctl uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope := by
  intro hH x st_init ans R s0 s hLPB
  rcases hLPB with ⟨st, hsb, hLP⟩
  dsimp only [LoadPolledStateVPlaced, wsMetaPlaced] at hLP
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, hcrl, hvregs⟩,
    hsp_le, hx19, hloadRel, htrace, hmem⟩ := hLP
  have hsp' : s0.sp - 0xee0#64 = s.sp := hsp.symm
  clear hsp
  have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
  rw [hsp'] at hx19 hmem
  simp only [← sepConj_assoc] at hmem
  have hdz0 : (0#64 + kit.loadFutDropOff == 0#64) = false :=
    beq_eq_false_iff_ne.mpr (kit.loadFutDrop_ne_zero (by decide))
  have hdz : (kit.loadFutDropOff == 0#64) = false := by
    simpa only [BitVec.zero_add] using hdz0
  have hsz : (BitVec.ofNat 64 kit.loadBoxSize == 0#64) = false :=
    beq_eq_false_iff_ne.mpr kit.loadBoxSize_ne_zero
  have hbs_pos : 0 < kit.loadBoxSize :=
    Nat.pos_of_ne_zero (fun h => kit.loadBoxSize_ne_zero (by simp [h]))
  have hevs_dealloc : BoxDeallocEnv kit.loadBoxSize (rustDeallocEvents kit.loadBoxSize 8) :=
    Or.inr ⟨hbs_pos, rfl⟩
  have hsb1 := hsb.advance hevs_dealloc
  let st1 := M.stepEvents (rustDeallocEvents kit.loadBoxSize 8) st
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx19
  have hmemcpy := msgDecrypt_memcpy_placed_ok hH.hooks.memcpy
  have hdrop := futDropBudget_463 (hH.kit.loadFutDrop (p := lsProg_463 H) (i := 463) (by decide))
  have hdealloc := msgDecrypt_dealloc_placed_ok hH.hooks.dealloc
  have hclone := stringClone_placed_ok hH.hooks
  apply decSeg_of_sepWP_mid_placed (st_init := st_init) hcrl hmem (mid := (blkPl_463).base + 312#64)
  dsimp only [lsProg_463, loadPolledPCPlaced] at hpc hmemcpy hclone ⊢
  wp_conv_pre => rw [wsFixed_eq_active_rest_placed (retagSessionStore kit) (retagIdentityStore ikit) x s0 s.sp, split_300_for_recordMove s.sp]
  wp_conv_pre => unfold wsEnvPlaced
  wp_conv_pre => dsimp only [RustCliAllocBudget.atState]
  wp_conv_pre => simp only [rep_protocolAddressAt_eq, rep_signalMessageAt_eq, rep_loadPollOut_eq, rep_wsFixedRest_eq, rep_decStoreExtra_eq]
  apply SepWP.fold (loadPollPlacedOutAt_entails_common Scope A.repAlloc s.sp ans.loadSession)
    (by sep_focus)
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
    q0OfWords_pointsTo128, q1OfWords_pointsTo128, CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64,
    BitVec.add_assoc, BitVec.reduceAdd]
  apply SepWP.exists_elim; intro _w8_init
  apply SepWP.exists_elim; intro _q1_init
  apply SepWP.exists_elim; intro _q0_init
  apply SepWP.exists_elim; intro box
  apply SepWP.exists_elim; intro w0
  apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2
  apply SepWP.exists_elim; intro w3
  apply SepWP.exists_elim; intro w4
  apply SepWP.exists_elim; intro w5
  apply SepWP.exists_elim; intro w6
  apply SepWP.exists_elim; intro tail
  apply SepWP.pure_elim; rintro ⟨hw0_ne, htail_len⟩
  wp_simp_pre [sepConj_pure_left_comm]
  apply SepWP.pure_elim; intro hbox_ne
  apply SepWP.fold (A.block_valid box kit.loadBoxSize 8) (by sep_focus)
  wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
  apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow8, hbound_box⟩, _⟩
  apply StoreKit.sepWP_seq_lscro hcrl (mid := kit.loadFutDropOff)
  apply sepWP_seq_cut (lsmpl.ρ "memcpy")
  by_vm_open (
    wp_steps
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm_m1
    refine SepWP.transport_budgetPool hvm_m1 (hnext := ?_); clear hvm_m1
    wp_call hmemcpy (s.sp + 0x328#64, s.sp + 0x628#64, tail)
    refine SepWP.transport_budgetPool ?_ (hnext := ?_)
    · assumption
    by_vm_open (
      wp_steps
      refine SepWP.done rfl (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      rintro hvm_d1 ⟨hcl_d, hro_d⟩
      refine SepWP.transport_budgetPool hvm_d1 (hnext := ?_); clear hvm_d1
      wp_call hdrop ()
      refine SepWP.transport_budgetPool ?_ (hnext := ?_)
      · assumption
      apply sepWP_seq_cut (lsρ lsRustDeallocSym)
      by_vm_open (
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm_da
        refine SepWP.transport_budgetPool hvm_da (hnext := ?_); clear hvm_da
        apply SepWP.fold (kit.loadBoxAt_memRegion box (s0.readReg64 .x3) x.remA 1#8) (by sep_focus)
        apply SepWP.fold (Entails.of_eq (stack_wsCallee_dealloc s.sp)) (by sep_focus)
        have hbs_toNat : (BitVec.ofNat 64 kit.loadBoxSize).toNat = kit.loadBoxSize :=
          Nat.mod_eq_of_lt kit.loadBoxSize_lt
        wp_call hdealloc (box, kit.loadBoxSize, 8, st)
        have hsp1 : sf_1.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
        have hsp2 : sf_2.sp = s.sp := by simp only [wp_norm, arm64_norm, *]
        rw [hsp1]
        apply SepWP.fold (Entails.of_eq (stack_wsCallee_dealloc_back s.sp)) (by sep_focus)
        apply SepWP.fold (fold_2d0 s.sp box _) (by sep_focus)
        apply SepWP.done hpc_sf_2 hrun_sf_2
        intro hcrl2 hmm2
        have hal2 : (sf_2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hal_s
        have htr2 : sf_2.trace = s.trace := by simp only [wp_norm, arm64_norm, *]
        have hx20_2 : sf_2.readReg64 (Reg.gpr 20#5) = w0 := by simp only [wp_norm, arm64_norm, *]
        have hx21_2 : sf_2.readReg64 (Reg.gpr 21#5) = BitVec.zeroExtend 64 (w2.extractLsb' 0 32) := by
          simp only [wp_norm, arm64_norm, *]
        have hx23_2 : sf_2.readReg64 (Reg.gpr 23#5) = s.sp + 1520#64 := by simp only [wp_norm, arm64_norm, *]
        have hx27_2 : sf_2.readReg64 (Reg.gpr 27#5) = x.ret := by simp only [wp_norm, arm64_norm, *]
        have hx28_2 : sf_2.readReg64 (Reg.gpr 28#5) = w1 := by simp only [wp_norm, arm64_norm, *]
        have hx29_2 : sf_2.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 := by
          simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *]
        have hvregs2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by
          simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *]
        rcases hload : ans.loadSession with ⟨⟨⟩⟩ | (_ | rec)
        · have ⟨hmod, hdraws⟩ := model_of_load_err C S x ans hload
          have hsb_err := hsb1.narrow (fun _ h => Or.inl h)
          apply decSeg_of_sepWP_done_placed (st_init := st_init) hcrl2 hmm2 (target := resultFinalPCPlaced)
          dsimp only [lsProg_463, resultFinalPCPlaced]
          wp_conv_pre => rw [hload, split_300_for_resultCopy s.sp, split_4b0_for_resultCopy s.sp]
          dsimp only [loadPollBranchRestPlaced]
          wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_pure_left_comm]
          repeat' (apply SepWP.exists_elim; intro _)
          apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, rfl⟩
          by_vm_open (
            wp_steps
            refine SepWP.done rfl hrun_sf_2 ⟨by simp only [wp_norm, arm64_norm], ?_⟩
            intro hvm_err hcrl3 hmf3
            let s_err := (fun {a b : State} (_ : VmPreserved a b) => b) hvm_err
            have hpool_err := A.pool_transport lim st1 sf_2 s_err hvm_err
            rw [← hpool_err] at hmf3
            let A_err := A.atState lim st1 s_err
            have hmf3'' := Satisfies.mono
              (sepConj_mono_left (Entails.trans (Entails.of_eq (by
                  dsimp only [A_err, RustCliAllocBudget.atState]
                  simp only [rep_protocolAddressAt_eq, rep_signalMessageAt_eq, rep_wsFixedRest_eq, rep_decStoreExtra_eq]
                  sep_ac_rfl))
                (branch_err_entails_placed A_err ctl (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 x s0 s.sp w2 w5 w6 tail htail_len))) hmf3
            refine Or.inr (Or.inr ⟨st1, hsb_err, ?_⟩)
            dsimp only [ResultFinalStateVPlaced, wsMetaPlaced]
            refine ⟨rfl, ⟨hrun_sf_2, hsp2.trans hsp'.symm, hal0, hal2, ?_, ?_, hcrl3, hvregs2⟩,
              ans, by simp [hmod], fun r hr => by simp [hload] at hr,
              by simp only [hmod]; exact ⟨hload ▸ hloadRel, trivial⟩,
              by simp only [hmod]; trivial, ?_, ?_⟩
            · simpa [wp_norm, arm64_norm] using hx29_2
            · simpa [wp_norm, arm64_norm] using hx27_2
            · simp only [wp_norm, arm64_norm, htr2, htrace, hmod, hload,
                Identity.IdentityStoreSpec.traceOfWith_load]
            · rw [hsp', hmod, hdraws]
              dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal, A_err]
              simpa only [wp_norm, arm64_norm, hx28_2, hx21_2, sepConj_assoc] using hmf3''
          )
        · have ⟨hmod, hdraws⟩ := model_of_load_none C S x ans hload
          have hsb_none := hsb1.narrow (fun _ h => Or.inr (Or.inl h))
          have hfits_cl : FitsEnv M lim st1 (StringCloneEnv x.rem.name) := hsb_none.1.seq_left
          apply decSeg_of_sepWP_mid_placed (st_init := st_init) hcrl2 hmm2 (mid := lsmpl.base 623)
          dsimp only [lsProg_463]
          wp_conv_pre => rw [hload]
          dsimp only [loadPollBranchRestPlaced]
          wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
          apply SepWP.pure_elim; rintro rfl
          by_vm_open (
            wp_steps
            refine SepWP.done rfl hrun_sf_2 ⟨by simp only [wp_norm, arm64_norm], ?_⟩
            intro hvm_cl hcrl3 hmm3
            let s_cl := (fun {a b : State} (_ : VmPreserved a b) => b) hvm_cl
            have hpool_cl := A.pool_transport lim st1 sf_2 s_cl hvm_cl
            rw [← hpool_cl] at hmm3
            apply decSeg_of_sepWPp_placed (st_init := st_init) hmm3 (target := resultFinalPCPlaced)
            dsimp only [lsProg_463, resultFinalPCPlaced]
            refine messageDecrypt_call_panic_then_wp_lscro hclone
              (x := (x.remA, s.sp + 0x5f0#64, x.rem.name, st1))
              (F := F_clonePlaced A.repAlloc ctl kit ikit st0 ist0 x s0 s.sp)
              hcrl3 rfl
              (by simpa only [wp_norm, arm64_norm] using hrun_sf_2)
              (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2]; exact hal_s)
              (by simp only [wp_norm, arm64_norm]; rfl)
              (fun R' hm' => ?_)
              (fun _ => false_onPanic_entails)
              (fun _ _ => rfl)
              ?_
            · dsimp only [CryptoVerification.withLsCodeLoaded]
              rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
              refine ⟨hcrl3.1, ?_⟩
              try dsimp only [stringCloneBudgetSpec]
              rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj, ← sepConj_assoc]
              refine ⟨⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], hfits_cl⟩, ?_⟩
              rw [show s_cl.sp = s.sp by simpa only [s_cl, wp_norm, arm64_norm] using hsp2]
              let A_cl := A.atState lim st1 s_cl
              dsimp only [A_cl, RustCliAllocBudget.atState, s_cl] at hm' ⊢
              refine Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq ?_)
                (Entails.trans
                  (branch_none_pre_clone_entails_placed A_cl ctl (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 x s0 s.sp w1 w2 w3 w4 w5 w6 tail htail_len)
                  (Entails.of_eq ?_)))) hm'
              · dsimp only [A_cl, RustCliAllocBudget.atState, s_cl]
                simp only [BitVec.zero_add, wp_norm, arm64_norm, rep_protocolAddressAt_eq, rep_signalMessageAt_eq, rep_wsFixedRest_eq, rep_decStoreExtra_eq]
              · dsimp only [A_cl, RustCliAllocBudget.atState, s_cl]
                simp only [rep_vecGhostAt_eq, rep_F_clone_eq]
            · intro sf4 hpc4 hrun4 hsp4 hcs4
              have hsp4' : sf4.sp = s.sp := by simpa only [wp_norm, arm64_norm, hsp2] using hsp4
              have hal4 : (sf4.sp &&& 15#64 == 0#64) = true := by rw [hsp4']; exact hal_s
              have hx19_4 : sf4.readReg64 (Reg.gpr 19#5) = x.remA := by
                simpa [wp_norm, arm64_norm] using hcs4.1
              have hx23_4 : sf4.readReg64 (Reg.gpr 23#5) = s.sp + 1520#64 := by
                have h := hcs4.2.2.2.2.1
                simp only [wp_norm, arm64_norm] at h
                exact h.trans hx23_2
              have hx27_4 : sf4.readReg64 (Reg.gpr 27#5) = x.ret := by
                have h := hcs4.2.2.2.2.2.2.2.2.1
                simp only [wp_norm, arm64_norm] at h
                exact h.trans hx27_2
              have hx29_4 : sf4.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 := by
                have h := hcs4.2.2.2.2.2.2.2.2.2.2.1
                simp only [wp_norm, arm64_norm] at h
                exact h.trans hx29_2
              have hvregs4 : calleeSavedVRegs sf4 = calleeSavedVRegs s0 :=
                hcs4.2.2.2.2.2.2.2.2.2.2.2.trans hvregs2
              dsimp only [stringCloneBudgetSpec]
              wp_simp_pre [wp_norm, arm64_norm, hsp2, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
              apply SepWP.exists_elim; intro (evs_cl : List AllocEvent)
              wp_simp_pre [sepConj_assoc]
              apply SepWP.pure_elim; rintro ⟨htr4, hevs_cl⟩
              have hsb2 := hsb_none.advance hevs_cl
              let st2 := M.stepEvents evs_cl st1
              apply SepWP.fold (vecU8_unpack_for_noRecord A.repAlloc s.sp x.rem.name.bytes) (by sep_focus)
              wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
              apply SepWP.exists_elim; intro cap
              apply SepWP.exists_elim; intro ptr
              apply SepWP.pure_elim; intro hcap_ne
              have hcond_cap : (cap + 3#64 != 0#64) = true :=
                bne_iff_ne.mpr (fun h => hcap_ne (by rw [show cap = cap + 3#64 - 3#64 by bv_arith, h]; rfl))
              dsimp only [F_clonePlaced]
              wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
                CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_pure_left_comm]
              apply SepWP.exists_elim; intro _w8_320
              apply SepWP.exists_elim; intro _q1_310
              apply SepWP.exists_elim; intro _q0_300
              apply SepWP.exists_elim; intro _w8_5a0
              apply SepWP.exists_elim; intro _q1_590
              apply SepWP.exists_elim; intro _q0_580
              apply SepWP.exists_elim; intro _d1
              apply SepWP.exists_elim; intro _d0
              apply SepWP.exists_elim; intro pad
              apply SepWP.exists_elim; intro _b0
              apply SepWP.pure_elim; intro hpad
              obtain ⟨w4_pad, hw4_pad⟩ :=
                exists_unpack64_of_length_8 (bs := x.rem.device :: pad) (by simp [hpad])
              wp_steps 2
              by_vm_open (
                wp_steps
                wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, ls_blockPlacement_ρ]
                apply SepWP.fold
                  (repack_after_0x3a980_split64 s.sp ptr (BitVec.ofNat 64 x.rem.name.bytes.length)
                     w4_pad (lsmpl.ρ CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.msgDecryptStrSym) 22#64 x.rem.device pad hw4_pad)
                  (by sep_focus)
                wp_simp_pre [sepConj_assoc]
                wp_steps
                refine SepWP.done rfl (by simpa only [wp_norm, arm64_norm] using hrun4) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
                intro hvm5 hcrl5 hmf5
                let s_after2 := (fun {a b : State} (_ : VmPreserved a b) => a) hvm5
                let s_none := (fun {a b : State} (_ : VmPreserved a b) => b) hvm5
                have hpool5 : A.pool lim st2 s_none = A.pool lim st2 sf4 :=
                  (A.pool_transport lim st2 s_after2 s_none hvm5).trans
                    (A.pool_transport lim st2 sf4 s_after2 (by dsimp only [s_after2]; simp only [wp_norm, arm64_norm]))
                rw [← hpool5] at hmf5
                let A_none := A.atState lim st2 s_none
                have htr4' : sf4.trace = s.trace := htr4.trans htr2
                have hmf5' := satisfies_rodata_msgDecryptStr_placed hcrl5.2 hmf5
                rw [← sepConj_assoc] at hmf5'
                dsimp only [st2, st1] at hmf5' ⊢
                have hmf5'' : s_none.mem ⊨
                    (wsFixedVPlaced (retagSessionStore (A' := A_none) kit) (retagIdentityStore (A' := A_none) ikit) x s0 s.sp ∗
                      wsEnvPlaced A_none x s.sp ∗ wsMsgCells x s.sp ∗
                      StagedRes A_none cap
                        (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 ptr) >>> 8)))
                        (BitVec.zeroExtend 64 (BitVec.extractLsb' 0 32 ptr)) (s.sp + 0x300#64)
                        (.error (.sessionNotFound x.rem.val "message_decrypt_signal")) ∗
                      memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x120#64) 0x1a8 ∗
                      memRegion (s.sp + 0x2d0#64) 0x10 ∗ memRegion (s.sp + 0x324#64) 0xadc ∗
                      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
                      decStoreExtraPlaced (retagSessionStore (A' := A_none) kit) (retagIdentityStore (A' := A_none) ikit) st0 ist0 s0) ∗ R := by
                  refine Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq ?_)
                    (branch_none_post_entails_placed A_none ctl (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 x s0 s.sp cap ptr w4_pad pad hpad hw4_pad))) hmf5'
                  dsimp only [A_none, RustCliAllocBudget.atState, st2, st1]
                  simp only [wp_norm, arm64_norm, rep_protocolAddressAt_eq, rep_signalMessageAt_eq, rep_wsFixedRest_eq, rep_decStoreExtra_eq]
                  sep_ac_rfl
                refine Or.inr (Or.inr ⟨st2, hsb2, ?_⟩)
                dsimp only [ResultFinalStateVPlaced, wsMetaPlaced]
                refine ⟨rfl, ⟨by simpa only [wp_norm, arm64_norm] using hrun4,
                  by simpa only [wp_norm, arm64_norm] using hsp4'.trans hsp'.symm,
                  hal0, by simpa only [wp_norm, arm64_norm] using hal4, ?_, ?_, hcrl5,
                  by simpa only [wp_norm, arm64_norm] using hvregs4⟩,
                  ans, by simp [hmod], fun r hr => by simp [hload] at hr,
                  by simp only [hmod]; exact ⟨hload ▸ hloadRel, trivial⟩,
                  by simp only [hmod]; trivial, ?_, ?_⟩
                · simpa [wp_norm, arm64_norm] using hx29_4
                · simpa [wp_norm, arm64_norm] using hx27_4
                · simp only [wp_norm, arm64_norm, htr4', htrace, hmod, hload,
                    Identity.IdentityStoreSpec.traceOfWith_load]
                · rw [hsp', hmod, hdraws]
                  dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal, A_none, s_none, RustCliAllocBudget.atState] at hmf5'' ⊢
                  simpa only [wp_norm, arm64_norm, sepConj_assoc] using hmf5''
              )
          )
        · apply decSeg_of_sepWP_done_placed (st_init := st_init) hcrl2 hmm2 (target := CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced)
          dsimp only [lsProg_463, CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced]
          wp_conv_pre => rw [hload, split_120_for_some s.sp]
          dsimp only [loadPollBranchRestPlaced]
          wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_pure_left_comm]
          apply SepWP.exists_elim; intro _w8_154
          apply SepWP.exists_elim; intro _q1_144
          apply SepWP.exists_elim; intro _q0_134
          apply SepWP.exists_elim; intro _w2_130
          apply SepWP.exists_elim; intro _w1_128
          apply SepWP.exists_elim; intro _w0_120
          apply SepWP.exists_elim; intro g
          apply SepWP.pure_elim; rintro ⟨hscope, htail_inl, hlt, rfl, rfl, rfl, rfl⟩
          have hscopeAt : kit.ScopeAt Scope st0 x.rem.val rec := ⟨hscope, hload ▸ hloadRel⟩
          have hscope_in : RecordInScope rec := hH.scopeIn rec hscope
          have ⟨hne1, hne2, _⟩ := ne_neg_tags_of_lt_two_pow_63 hlt
          have hcond2 : (g.prevCap + 2#64 != 0#64) = true :=
            bne_iff_ne.mpr (fun h => hne2 (by rw [show g.prevCap = g.prevCap + 2#64 - 2#64 by bv_arith, h]; rfl))
          have hcond1 : (g.prevCap + 1#64 == 0#64) = false :=
            beq_eq_false_iff_ne.mpr (fun h => hne1 (by rw [show g.prevCap = g.prevCap + 1#64 - 1#64 by bv_arith, h]; rfl))
          apply sepWP_seq_cut (lsmpl.ρ "memcpy")
          by_vm_open (
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
            intro hvm_m2
            refine SepWP.transport_budgetPool hvm_m2 (hnext := ?_); clear hvm_m2
            wp_call hmemcpy (s.sp + 0x158#64, s.sp + 0x328#64, tail)
            refine SepWP.transport_budgetPool ?_ (hnext := ?_)
            · assumption
            refine SepWP.done hpc_sf_3 hrun_sf_3 fun hcrl3 hmf3 => ?_
            have hsp3 : sf_3.sp = s.sp := hsp_sf_2.trans hsp2
            have hal3 : sf_3.spAligned = true := by simp only [State.spAligned, hsp3]; exact hal_s
            have htr3 : sf_3.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession := by
              simp only [wp_norm, arm64_norm, *]
            have hx19_3 : sf_3.readReg64 .x19 = x.remA := by simp only [wp_norm, arm64_norm, *]
            have hx23_3 : sf_3.readReg64 .x23 = s.sp + 0x5f0#64 := by simp only [wp_norm, arm64_norm, *]
            have hx24_3 : sf_3.readReg64 .x24 = s.sp + 0xca0#64 := by simp only [wp_norm, arm64_norm, *]
            have hx27_3 : sf_3.readReg64 .x27 = x.ret := by simp only [wp_norm, arm64_norm, *]
            have hx29_3 : sf_3.readReg64 .x29 = s0.sp - 96#64 := by
              simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *]
            have hroot : rootStack ≤ s.sp.toNat := rootStack_le_sp hsp'.symm hsp_le
            have hpure3 : StoreKit.LibsignalCodeRoLoaded lsmpl sf_3.mem ∧ sf_3.spAligned = true ∧
                sf_3.readReg64 .x27 = x.ret ∧ sf_3.readReg64 .x19 = x.remA ∧
                sf_3.readReg64 .x23 = s.sp + 0x5f0#64 ∧ sf_3.readReg64 .x24 = s.sp + 0xca0#64 ∧
                rootStack ≤ s.sp.toNat :=
              ⟨hcrl3, hal3, hx27_3, hx19_3, hx23_3, hx24_3, hroot⟩
            have hmeta3 : wsMetaPlaced x s0 sf_3 :=
              ⟨hrun_sf_3, hsp3.trans hsp'.symm, hal0, hal3, hx29_3, hx27_3, hcrl3,
                by simp only [CalleeSavedPreserved, wp_norm, arm64_norm, *]⟩
            let A3 := A.atState lim st1 sf_3
            have hmf3' : sf_3.mem ⊨
                (sessionRecordAt A3 (s.sp + 0x120#64) g rec ∗
                  regionCommonBodyPlaced A3 ctl x s.sp ∗
                  wsRegionFrameRestPlaced (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 x s0 s.sp) ∗ R := by
              refine Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq ?_)
                (branch_some_common_entails_placed A3 ctl (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 x s0 s.sp g rec w4 w5 w6 tail htail_inl))) hmf3
              dsimp only [A3, RustCliAllocBudget.atState, st1]
              simp only [BitVec.zero_add, wp_norm, arm64_norm, rep_protocolAddressAt_eq, rep_signalMessageAt_eq, rep_wsFixedRest_eq, rep_decStoreExtra_eq, rep_recordHeap_eq]
              sep_ac_rfl
            cases hcur : rec.currentSession with
            | none =>
              have hsb_rn := hsb1.narrow (fun _ h => Or.inr (Or.inr (Or.inl h)))
              have hmf3'' := Satisfies.mono
                (sepConj_mono_left (regionNone_of_common_placed A3 ctl (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 x s0 sf_3 s.sp g rec hsp' hsp3 hcur hpure3)) hmf3'
              simp only [sepConj_assoc] at hmf3''
              exact Or.inr (Or.inl ⟨st1, hsb_rn, hpc_sf_3, hmeta3, rec, g.prevCap, g.prevPtr,
                hload, hscopeAt, hcur, htr3, hmf3''⟩)
            | some ses =>
              have hsb_rs : ∀ rec0 ses0, ans.loadSession = .ok (some rec0) → rec0.currentSession = some ses0 →
                  SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse Scope x) st_init st1
                    (FromRegionSomeEnv C S uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 x rec0 ses0.state) := by
                intro rec0 ses0 hload0 hcur0
                rw [hload] at hload0; cases hload0
                rw [hcur] at hcur0; cases hcur0
                exact hsb1.narrow (fun _ h => Or.inr (Or.inr (Or.inr ⟨rec, ses, hscopeAt, hcur, h⟩)))
              have hmf3'' := Satisfies.mono
                (sepConj_mono_left (regionSome_of_common_placed C A3 ctl S (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 x s0 sf_3 s.sp g rec ses hsp' hsp3 hscope_in hcur hpure3)) hmf3'
              rw [sepExists_sepConj_left, satisfies_sepExists] at hmf3''
              obtain ⟨G, hmf3''⟩ := hmf3''
              rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hmf3''
              obtain ⟨hw0, hmf3''⟩ := hmf3''
              simp only [sepConj_assoc] at hmf3''
              exact Or.inl ⟨st1, hsb_rs, hpc_sf_3, hmeta3, rec, ses, G, g.prevCap, g.prevPtr,
                hload, hscopeAt, hcur, hw0, htr3, hmf3''⟩
          )
      )
    )
  )

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchPlacedBudget
