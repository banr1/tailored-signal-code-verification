/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `SegDispatch` (`+0x8c → +0x1a8 / +0x24d4`)

Proves relocatable (`[LibsignalPlacement]`) `segDispatchGen_placed_ok` and `segDispatchVX_placed_ok`
on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch hiding wsFixedRestPlaced wsFixed_eq_active_rest_placed fold_wsFixed_assoc_placed branch_err_entails_placed wsNonePassivePlaced F_clonePlaced branch_none_pre_clone_entails_placed branch_none_post_entails_placed regionCommonBodyPlaced wsRegionFrameRestPlaced branch_some_common_entails_placed regionNone_of_common_placed regionSome_of_common_placed segDispatchVPlaced_ok apiDecResultAt_store_placed_of_words stagedRes_store_err_placed apiDecResultAt_sessionNotFound_placed_of_words stagedRes_sessionNotFound_placed messageDecrypt_of_sepWP_lscro messageDecrypt_of_sepWP_done_lscro messageDecrypt_call_panic_then_wp_lscro decSeg_of_sepWP_mid_placed decSeg_of_sepWP_done_placed decSeg_of_sepWPp_placed msgDecryptStrSym satisfies_rodata_msgDecryptStr_placed ls_hook_ok_197 stringClone_placed_ok msgDecrypt_memcpy_placed_ok msgDecrypt_dealloc_placed_ok stringClone_onPanic_entails_placed loadPollPlacedOutAt_err_entails loadPollPlacedOutAt_none_entails loadPollPlacedOutAt_some_entails loadPollBranchRestPlaced loadPollPlacedOutAt_entails_common
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch
open CryptoVerification

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] extractLsb_lo_append64 extractLsb_hi_append64

set_option maxHeartbeats 1600000 in
theorem segDispatchGen_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {SomeOut : State → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hLP : LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s)
    (hSome : ∀ (sf_3 : State) (g : RecordGhost) (rec : SessionRecord (List (BitVec 8)))
      (ses : Session (List (BitVec 8))),
      sf_3.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced →
      wsMetaPlaced x s0 sf_3 →
      ans.loadSession = .ok (some rec) →
      Scope rec →
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      sf_3.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession →
      s0.sp - 0xee0#64 = s.sp →
      sf_3.sp = s.sp →
      (StoreKit.LibsignalCodeRoLoaded lsmpl sf_3.mem ∧ sf_3.spAligned = true ∧
        sf_3.readReg64 .x27 = x.ret ∧ sf_3.readReg64 .x19 = x.remA ∧
        sf_3.readReg64 .x23 = s.sp + 0x5f0#64 ∧ sf_3.readReg64 .x24 = s.sp + 0xca0#64 ∧
        rootStack ≤ s.sp.toNat) →
      (sf_3.mem ⊨ (sessionRecordAt A (s.sp + 0x120#64) g rec ∗
        regionCommonBodyPlaced A ctl x s.sp ∗
        wsRegionFrameRestPlaced kit ikit st0 ist0 x s0 s.sp) ∗ R) →
      SomeOut sf_3) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' =>
        SomeOut s' ∨
        RegionNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s') := by
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
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx19
  have hmemcpy := msgDecrypt_memcpy_placed_ok hH.hooks.memcpy
  have hdrop : subroutine_ok (lsProg_463 H) kit.loadFutDropOff
      (StoreKit.withLsCodeRoLoaded lsmpl futDropSpec) := by
    simpa only [BitVec.zero_add] using
      StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl (hH.kit.loadFutDrop (callerBlk := 463) (by decide))
  have hdealloc := msgDecrypt_dealloc_placed_ok hH.hooks.dealloc
  have hclone := stringClone_placed_ok hH.hooks
  apply decSegVXPlaced_of_sepWP_mid hcrl hmem (mid := (blkPl_463).base + 312#64)
  dsimp only [lsProg_463, loadPolledPCPlaced] at hpc hmemcpy hdrop hdealloc hclone ⊢
  wp_conv_pre => rw [wsFixed_eq_active_rest_placed kit ikit x s0 s.sp, split_300_for_recordMove s.sp]
  unfold wsEnvPlaced
  apply SepWP.fold (loadPollPlacedOutAt_entails_common Scope A s.sp ans.loadSession)
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
  apply StoreKit.sepWP_seq_lscro hcrl (mid := kit.loadFutDropOff)
  wp_steps
  wp_call hmemcpy (s.sp + 0x328#64, s.sp + 0x628#64, tail)
  wp_steps
  refine SepWP.done rfl (by wp_norm_lhs) fun ⟨hcl_d, hro_d⟩ => ?_
  wp_apply
  simp only [hsp_sf] at h_12 ⊢
  wp_steps
  apply SepWP.fold (kit.loadBoxAt_memRegion box (s0.readReg64 .x3) x.remA 1#8) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (stack_wsCallee_dealloc s.sp)) (by sep_focus)
  have hbs_toNat : (BitVec.ofNat 64 kit.loadBoxSize).toNat = kit.loadBoxSize :=
    Nat.mod_eq_of_lt kit.loadBoxSize_lt
  wp_apply
  simp only [h_12] at hsp_sf_1 ⊢
  apply SepWP.fold (Entails.of_eq (stack_wsCallee_dealloc_back s.sp)) (by sep_focus)
  apply SepWP.fold (fold_2d0 s.sp box _) (by sep_focus)
  apply SepWP.done hpc_sf_2 hrun_sf_2
  intro hcrl2 hmm2
  have hsp2 : sf_2.sp = s.sp := hsp_sf_1
  have hal2 : (sf_2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hal_s
  have htr2 : sf_2.trace = s.trace := by rw [hpost_1, h_11, hpost]
  have hx20_2 : sf_2.readReg64 (Reg.gpr 20#5) = w0 := by rw [h_24, h_14, h_1]
  have hx21_2 : sf_2.readReg64 (Reg.gpr 21#5) = BitVec.zeroExtend 64 (w2.extractLsb' 0 32) := by
    rw [h_25, h_15, h_2]
  have hx23_2 : sf_2.readReg64 (Reg.gpr 23#5) = s.sp + 1520#64 := by rw [h_27, h_17, h_4]
  have hx27_2 : sf_2.readReg64 (Reg.gpr 27#5) = x.ret := by rw [h_31, h_21, h_8, hx27]
  have hx28_2 : sf_2.readReg64 (Reg.gpr 28#5) = w1 := by rw [h_32, h_22, h_9]
  have hx29_2 : sf_2.readReg64 (Reg.gpr 29#5) = s0.sp - 96#64 := by
    rw [hcs_sf_1, hpost_sf, hcs_sf, hx29]
  have hvregs2 : calleeSavedVRegs sf_2 = calleeSavedVRegs s0 := by
    rw [hvregs_3, hvregs_2, hvregs_1, hvregs]
  clear h_23 h_24 h_25 h_26 h_27 h_28 h_29 h_30 h_31 h_32 hcs_sf_1 hpost_1
    h_13 h_14 h_15 h_16 h_17 h_18 h_19 h_20 h_21 h_22 hpost_sf h_11
    h h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9 hcs_sf hpost hvregs_1 hvregs_2 hvregs_3
  rcases hload : ans.loadSession with ⟨⟨⟩⟩ | (_ | rec)
  · have ⟨hmod, hdraws⟩ := model_of_load_err C S x ans hload
    apply decSegVXPlaced_of_sepWP_done hcrl2 hmm2 (target := resultFinalPCPlaced)
    dsimp only [lsProg_463, resultFinalPCPlaced]
    wp_conv_pre => rw [hload, split_300_for_resultCopy s.sp, split_4b0_for_resultCopy s.sp]
    dsimp only [loadPollBranchRestPlaced]
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
      CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.pointsTo128_split64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_pure_left_comm]
    repeat' (apply SepWP.exists_elim; intro _)
    apply SepWP.pure_elim; rintro ⟨rfl, rfl, rfl, rfl⟩
    wp_steps
    refine SepWP.done rfl hrun_sf_2 fun hcrl3 hmf3 => ?_
    have hmf3'' := Satisfies.mono
      (sepConj_mono_left (Entails.trans (Entails.of_eq (by ac_rfl))
        (branch_err_entails_placed A ctl kit ikit st0 ist0 x s0 s.sp w2 w5 w6 tail htail_len))) hmf3
    refine Or.inr (Or.inr ?_)
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
      dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
      simpa only [wp_norm, arm64_norm, hx28_2, hx21_2, sepConj_assoc] using hmf3''
  · have ⟨hmod, hdraws⟩ := model_of_load_none C S x ans hload
    apply decSegVXPlaced_of_sepWP_mid hcrl2 hmm2 (mid := lsmpl.base 623)
    dsimp only [lsProg_463]
    wp_conv_pre => rw [hload]
    dsimp only [loadPollBranchRestPlaced]
    wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
    apply SepWP.pure_elim; rintro rfl
    wp_steps
    refine SepWP.done rfl hrun_sf_2 fun hcrl3 hmm3 => ?_
    apply decSegVXPlaced_of_sepWPp hmm3 (target := resultFinalPCPlaced)
    dsimp only [lsProg_463, resultFinalPCPlaced]
    have h03 : s0.trace <+: sf_2.trace := by
      rw [htr2, htrace]
      exact ⟨kit.loadEvs encRecord x.rem.val ans.loadSession, rfl⟩
    refine messageDecrypt_call_panic_then_wp_lscro hclone
      (x := (x.remA, s.sp + 0x5f0#64, x.rem.name))
      (F := F_clonePlaced A ctl kit ikit st0 ist0 x s0 s.sp)
      hcrl3 rfl
      (by simpa only [wp_norm, arm64_norm] using hrun_sf_2)
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp2]; exact hal_s)
      (by simp only [wp_norm, arm64_norm]; rfl)
      (fun R' hm' => ?_)
      (fun sf => stringClone_onPanic_entailsVX_placed (by simpa only [wp_norm, arm64_norm] using h03))
      (fun _ _ => rfl)
      ?_
    · dsimp only [CryptoVerification.withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hcrl3.1, ?_⟩
      try dsimp only [stringCloneSpec]
      rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj, ← sepConj_assoc]
      refine ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      have hpre_ent := branch_none_pre_clone_entails_placed A ctl kit ikit st0 ist0 x s0 s.sp w1 w2 w3 w4 w5 w6 tail htail_len
      simp only [BitVec.zero_add, wp_norm, hsp2] at hpre_ent hm' ⊢
      exact Satisfies.mono (sepConj_mono_left hpre_ent) hm'
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
      dsimp only [stringCloneSpec]
      wp_simp_pre [wp_norm, arm64_norm, hsp2, sepConj_assoc]
      apply SepWP.pure_elim; intro htr4
      apply SepWP.fold (vecU8_unpack_for_noRecord A s.sp x.rem.name.bytes) (by sep_focus)
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
      wp_steps
      wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, ls_blockPlacement_ρ]
      apply SepWP.fold
        (repack_after_0x3a980_split64 s.sp ptr (BitVec.ofNat 64 x.rem.name.bytes.length)
           w4_pad (lsmpl.ρ msgDecryptStrSym) 22#64 x.rem.device pad hw4_pad)
        (by sep_focus)
      wp_simp_pre [sepConj_assoc]
      wp_steps
      refine SepWP.done rfl hrun4 fun hcrl5 hmf5 => ?_
      have htr4' : sf4.trace = s.trace := htr4.trans htr2
      have hmf5' := satisfies_rodata_msgDecryptStr_placed hcrl5.2 hmf5
      rw [← sepConj_assoc] at hmf5'
      have hmf5'' := Satisfies.mono
        (sepConj_mono_left (branch_none_post_entails_placed A ctl kit ikit st0 ist0 x s0 s.sp cap ptr w4_pad pad hpad hw4_pad)) hmf5'
      refine Or.inr (Or.inr ?_)
      dsimp only [ResultFinalStateVPlaced, wsMetaPlaced]
      refine ⟨rfl, ⟨hrun4, hsp4'.trans hsp'.symm, hal0, hal4, ?_, ?_, hcrl5, hvregs4⟩,
        ans, by simp [hmod], fun r hr => by simp [hload] at hr,
        by simp only [hmod]; exact ⟨hload ▸ hloadRel, trivial⟩,
        by simp only [hmod]; trivial, ?_, ?_⟩
      · simpa [wp_norm, arm64_norm] using hx29_4
      · simpa [wp_norm, arm64_norm] using hx27_4
      · simp only [wp_norm, arm64_norm, htr4', htrace, hmod, hload,
          Identity.IdentityStoreSpec.traceOfWith_load]
      · rw [hsp', hmod, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [wp_norm, arm64_norm, sepConj_assoc] using hmf5''
  · apply decSegVXPlaced_of_sepWP_done hcrl2 hmm2 (target := CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced)
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
    have ⟨hne1, hne2, _⟩ := ne_neg_tags_of_lt_two_pow_63 hlt
    have hcond2 : (g.prevCap + 2#64 != 0#64) = true :=
      bne_iff_ne.mpr (fun h => hne2 (by rw [show g.prevCap = g.prevCap + 2#64 - 2#64 by bv_arith, h]; rfl))
    have hcond1 : (g.prevCap + 1#64 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr (fun h => hne1 (by rw [show g.prevCap = g.prevCap + 1#64 - 1#64 by bv_arith, h]; rfl))
    wp_steps
    wp_call hmemcpy (s.sp + 0x158#64, s.sp + 0x328#64, tail)
    refine SepWP.done hpc_sf_3 hrun_sf_3 fun hcrl3 hmf3 => ?_
    have hsp3 : sf_3.sp = s.sp := hsp_sf_2.trans hsp2
    have hal3 : sf_3.spAligned = true := by simp only [State.spAligned, hsp3]; exact hal_s
    have htr3 : sf_3.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession := by
      rw [hpost, htr2, htrace]
    have hx19_3 : sf_3.readReg64 .x19 = x.remA := h
    have hx23_3 : sf_3.readReg64 .x23 = s.sp + 0x5f0#64 := h_4.trans hx23_2
    have hx24_3 : sf_3.readReg64 .x24 = s.sp + 0xca0#64 := h_5
    have hx27_3 : sf_3.readReg64 .x27 = x.ret := h_8.trans hx27_2
    have hx29_3 : sf_3.readReg64 .x29 = s0.sp - 96#64 := hcs_sf.trans hx29_2
    have hroot : rootStack ≤ s.sp.toNat := rootStack_le_sp hsp'.symm hsp_le
    have hpure3 : StoreKit.LibsignalCodeRoLoaded lsmpl sf_3.mem ∧ sf_3.spAligned = true ∧
        sf_3.readReg64 .x27 = x.ret ∧ sf_3.readReg64 .x19 = x.remA ∧
        sf_3.readReg64 .x23 = s.sp + 0x5f0#64 ∧ sf_3.readReg64 .x24 = s.sp + 0xca0#64 ∧
        rootStack ≤ s.sp.toNat :=
      ⟨hcrl3, hal3, hx27_3, hx19_3, hx23_3, hx24_3, hroot⟩
    have hmeta3 : wsMetaPlaced x s0 sf_3 :=
      ⟨hrun_sf_3, hsp3.trans hsp'.symm, hal0, hal3, hx29_3, hx27_3, hcrl3,
        hvregs_1.trans hvregs2⟩
    have hsome_ent := branch_some_common_entails_placed A ctl kit ikit st0 ist0 x s0 s.sp g rec w4 w5 w6 tail htail_inl
    simp only [BitVec.zero_add, wp_norm] at hsome_ent hmf3
    have hmf3' := Satisfies.mono (sepConj_mono_left hsome_ent) hmf3
    cases hcur : rec.currentSession with
    | none =>
      have hmf3'' := Satisfies.mono
        (sepConj_mono_left (regionNone_of_common_placed A ctl kit ikit st0 ist0 x s0 sf_3 s.sp g rec hsp' hsp3 hcur hpure3)) hmf3'
      simp only [sepConj_assoc] at hmf3''
      exact Or.inr (Or.inl ⟨hpc_sf_3, hmeta3, rec, g.prevCap, g.prevPtr,
        hload, hscopeAt, hcur, htr3, hmf3''⟩)
    | some ses =>
      exact Or.inl (hSome sf_3 g rec ses hpc_sf_3 hmeta3 hload hscope hscopeAt hcur
        htr3 hsp' hsp3 hpure3 hmf3')

/-- Relocatable `SegDispatch` into `RegionSomeStateVPlaced` under `Scope ⊆ RecordInScope`. -/
theorem segDispatchVX_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hH : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hscopeIn : ∀ r, Scope r → RecordInScope r)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hLP : LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' =>
        RegionSomeStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        RegionNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s') := by
  refine segDispatchGen_placed_ok hH x ans R s0 s hLP ?_
  intro sf_3 g rec ses hpc3 hmeta3 hload hscope hscopeAt hcur htr3 hsp' hsp3 hpure3 hmf3'
  have hmf3'' := Satisfies.mono
    (sepConj_mono_left (regionSome_of_common_placed C A ctl S kit ikit st0 ist0 x s0 sf_3 s.sp g rec ses
      hsp' hsp3 (hscopeIn rec hscope) hcur hpure3)) hmf3'
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmf3''
  obtain ⟨G, hmf3''⟩ := hmf3''
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hmf3''
  obtain ⟨hw0, hmf3''⟩ := hmf3''
  simp only [sepConj_assoc] at hmf3''
  exact ⟨hpc3, hmeta3, rec, ses, G, g.prevCap, g.prevPtr, hload, hscopeAt, hcur, hw0, htr3, hmf3''⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
