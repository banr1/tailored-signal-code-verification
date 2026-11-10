/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegTrustPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExtPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `SegTrust` (`+0x1fcc → +0x2150 / +0x21b0 / +0x2294`)

Proves budget-threaded (`RustCliAllocBudget M`) relocatable `segTrustVX_placed_ok` on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExtPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoGames.LibsignalSession (Crypto IdentityKey)
open CryptoGames.LibsignalSessionApi (Session SessionRecord StoreAnswers)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt storeHookStr)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt SessionStoreSpec withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
  (decryptRecord resWord1 wsCalleeStackV wsMsgCells wsStackV)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (draws_eq_of_loadSession_eq memRegion_36_entails_cells)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
  (model_of_trust_err resWord1_trust_err trustCallStack trustCallStack_le_wsCalleeV trustPollTag)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
  (decStoreExtraPlaced wsEnvPlaced wsFixedVPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (wsMetaPlaced_of_steps)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
  (keyReady_entails_trustCallPre_placed trustCallPost_entails_common_placed
   trustPollOutPlacedRel trustPostCommon_err_entails_placed trustPostCommon_ok_entails_placed
   wsTrustCallPrePlaced wsTrustFramePlaced wsTrustPostCommonRestPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv TrustStepEnv kitSaveShimSpec kitTrustShimSpec retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI kitSavePollPlacedSpecI kitTrustPollPlacedSpecI)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromTrustedEnv FromTrustedFalseEnv FromTrustedTrueEnv WithStoresDecEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (ErrJoinStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (DecSegVXPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
  (atState_eq_of_vmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
  (BoxDeallocEnv IdentityStoreKitBudgetOkI TrustStepEnvDec
   kitSavePollBudgetSpecI kitSaveShimBudgetSpec kitTrustPollBudgetSpecI kitTrustShimBudgetSpec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegTrustPlacedBudget
  (segTrust_call_placed_wp segTrust_tail_placed_err segTrust_tail_placed_ok_false
   segTrust_tail_placed_ok_true)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
  (DecFsCtxExtPlaced DecHypsExtPlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem seamBudget_advance {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv stepEnv nextEnv : List AllocEvent → Prop} {st_init st : M.σ}
    {evs_step : List AllocEvent}
    (hs : SeamBudget M lim fullEnv st_init st (SeqEnv stepEnv nextEnv))
    (hstep : stepEnv evs_step) :
    SeamBudget M lim fullEnv st_init (M.stepEvents evs_step st) nextEnv := by
  rcases hs with ⟨hfits, evs_pre, hst, hfull⟩
  refine ⟨hfits.seq_right hstep, evs_pre ++ evs_step, by rw [M.stepEvents_append, ← hst],
    fun evs_rem hnext => ?_⟩
  rw [List.append_assoc]
  exact hfull (evs_step ++ evs_rem) (SeqEnv.append hstep hnext)

private theorem seamBudget_narrow {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv rem1 rem2 : List AllocEvent → Prop} {st_init st : M.σ}
    (hs : SeamBudget M lim fullEnv st_init st rem1)
    (himp : ∀ evs, rem2 evs → rem1 evs) :
    SeamBudget M lim fullEnv st_init st rem2 := by
  rcases hs with ⟨hfits, evs_pre, hst, hfull⟩
  exact ⟨hfits.mono himp, evs_pre, hst, fun evs h2 => hfull evs (himp evs h2)⟩

private def toTwinsIdEnv {A : CryptoVerification.RustHeap.RustAlloc} {b : BitVec 64}
    {ikit : IdentityStoreSpec A b} (e : IdentityStoreBudgetEnv ikit) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit :=
  ⟨e.trustPollEnv, e.savePollEnv⟩

private theorem ikit_to_twins [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {H : LibsignalHooks}
    (h : IdentityStoreKitPlacedOkI A lim ikit ikitEnv H) :
    IdentityStoreKitBudgetOkI A lim ikit (toTwinsIdEnv ikitEnv) H where
  trustShim hi := subroutine_ok_mono (h.trustShim hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  trustPoll hi := subroutine_ok_mono (h.trustPoll hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  trustFutDrop hi := subroutine_ok_mono (h.trustFutDrop hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  saveShim hi := subroutine_ok_mono (h.saveShim hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  savePoll hi := subroutine_ok_mono (h.savePoll hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  saveFutDrop hi := subroutine_ok_mono (h.saveFutDrop hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)

private theorem trustStepEnv_of_twins {A : CryptoVerification.RustHeap.RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState} {rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal}
    {k : IdentityKey} {evs : List AllocEvent}
    (h : TrustStepEnvDec ikit (toTwinsIdEnv ikitEnv) ist0 rem k evs) :
    TrustStepEnv ikit ikitEnv ist0 rem k .receiving evs := by
  have hpos : 0 < ikit.trustBoxSize :=
    Nat.pos_of_ne_zero (fun h0 => ikit.trustBoxSize_ne_zero (by simp [h0]))
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2a | ⟨e2a, e2b, rfl, h2a, ⟨h0, _⟩ | ⟨_, h2b⟩⟩⟩
  · exact SeqEnv.inl h1
  · exact SeqEnv.append h1 (SeqEnv.inl h2a)
  · omega
  · exact SeqEnv.append h1 (SeqEnv.append h2a h2b)

set_option maxHeartbeats 800000 in
attribute [local semireducible] SepWP in
/-- Budget-threaded relocatable `segTrustVX_placed_ok` on `lsProg_463 H`. -/
theorem segTrustVX_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExtPlaced C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 Scope)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (hstB : KeyReadyStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H
      kit kitEnv ikit ikitEnv st0 ist0 Scope Extra x st_init R s0 s
      (fun s' =>
        (∃ ans' t, TrustedStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans' t R s0 s') ∨
        ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s') := by
  intro hL
  rcases hstB with ⟨st, hsb_all, hst⟩
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htr, hm⟩
  have hsb : SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
      st_init st (FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k) :=
    hsb_all rec rec' pt ses k hload hdec hcur hrem
  have hfsAt : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, -⟩ := hq
      simp only [hl]).mono (fun _ h => h.2) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hfits : FitsEnv M lim st (TrustStepEnvDec ikit (toTwinsIdEnv ikitEnv) ist0 x.rem.val k) :=
    hsb.1.seq_left.mono (fun _ => trustStepEnv_of_twins)
  let A0 := A.atState lim st s
  let kit0 := retagSessionStore (A' := A0) kit
  let ikit0 := retagIdentityStore (A' := A0) ikit
  rw [← hsp] at hx26 hx22 hm
  obtain ⟨k0, k1, k2, k3, _, hk_unpack⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length k.publicKey.bytes)
  have hk_ca0 :
      ((s.sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) =
        (((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3)) := by
    have h := hk_unpack (s.sp + 0xca0#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hk_2a8 :
      (((s.sp + 0x2a8#64) ↦₆₄ k0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ k1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ k2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ k3)) =
        ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) := by
    have h := (hk_unpack (s.sp + 0x2a8#64)).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hm_pre : s.mem ⊨
      (⌜wsStackV kit0 ikit0 ≤ s0.sp.toNat⌝ ∗
        ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
        ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          wsTrustCallPrePlaced A0 ikit0 x s0 s.sp ist0 c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 d5 ∗
          wsTrustFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (keyReady_entails_trustCallPre_placed C A0 ctl kit0 ikit0 x ans s0 s.sp
        st0 ist0 rec' pt k k0 k1 k2 k3 hsp hk_ca0)) ?_
    dsimp only [A0, kit0, ikit0] at hm ⊢
    simpa only [sepConj_assoc] using hm
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  have htrust_lt : trustCallStack ikit ≤ 2 ^ 64 := by
    have hlt := s0.sp.isLt
    have h1 := trustCallStack_le_wsCalleeV kit0 ikit0
    have h2 : wsCalleeStackV kit0 ikit0 ≤ wsStackV kit0 ikit0 := Nat.le_add_right _ _
    change trustCallStack ikit0 ≤ 2 ^ 64
    omega
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨a0, a1, a2, a3, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segTrust_call_placed_wp hyps.hooks.dealloc (ikit_to_twins hyps.ikit) htrust_lt
      (R := wsTrustFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt ∗ R)
      hcrl hfits haddr hpc hrun hsp_align hk_2a8 hfsAt
      (wsTrustFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _, hm1_pan, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx19_1, hx22_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨evs_trust, ans_trust, box, strPtr, vt, o2, o3, o4, o5, o6, b0, b3, h1, hm1'⟩
    let st1 := M.stepEvents evs_trust st
    let A1 := A.atState lim st1 sf
    let kit1 := retagSessionStore (A' := A1) kit
    let ikit1 := retagIdentityStore (A' := A1) ikit
    have hm1_common : sf.mem ⊨
        (⌜sf.readReg64 .x28 = trustPollTag ans_trust ∧
            sf.readReg64 .x21 = b0.zeroExtend 64 ∧
            sf.readReg64 .x23 = b3.zeroExtend 64 ∧
            sf.readReg64 .x24 = h1.zeroExtend 64 ∧
            ikit.trustRel ist0 x.rem.val k .receiving ans_trust ∧
            sf.trace = s.trace ++ ikit.trustEvs x.rem.val k .receiving ans_trust ∧
            trustPollOutPlacedRel strPtr vt o2 o3 o4 o5 b0 b3 h1 ans_trust ∧
            TrustStepEnvDec ikit (toTwinsIdEnv ikitEnv) ist0 x.rem.val k evs_trust⌝ ∗
          (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
            ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
            ((s.sp + 0x510#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_trust.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          wsTrustPostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0
            (ikit.trustUpdate ist0 x.rem.val k .receiving ans_trust)
            rec' pt k) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpure
      refine Entails.pure_right hpure ?_
      exact trustCallPost_entails_common_placed C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist0
        rec' pt k ans_trust box strPtr o2 o3 o4 o5 k0 k1 k2 k3 b0 b3 h1 o6 hsp hbound
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hx28_1, hx21_1, hx23_1, hx24_1, htrustRel, htr1, hrel1, hevs_trust⟩, hm1_common⟩
    have hsb1 := seamBudget_advance hsb (trustStepEnv_of_twins hevs_trust)
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_trust with ⟨⟨⟩⟩ | t
    · let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      rcases hrel1 with ⟨hb0, hh1, hb3, hsave_rel⟩
      let o1 := strPtr.extractLsb' 0 32
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sf.sp + 0x4f8#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x500#64) ↦₆₄ o4) ∗ ((sf.sp + 0x508#64) ↦₆₄ o5) ∗
              ((sf.sp + 0x510#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗
              ((sf.sp + 0x590#64) ↦₆₄ e2) ∗ ((sf.sp + 0x598#64) ↦₆₄ e3) ∗
              ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            ((strPtr ↦ᵣ storeHookStr) ∗
              wsTrustPostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist1 rec' pt k)) ∗ R := by
        rw [hsp1]
        refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0
        apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2
        apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hvm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segTrust_tail_placed_err (H := H)
          (R := ((strPtr ↦ᵣ storeHookStr) ∗
            wsTrustPostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist1 rec' pt k) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1 hx23_1 hx24_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            wsTrustPostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist1 rec' pt k) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      let A2 := A.atState lim st1 sf2
      let kit2 := retagSessionStore (A' := A2) kit
      let ikit2 := retagIdentityStore (A' := A2) ikit
      have hA12 : A1 = A2 := atState_eq_of_vmPreserved A lim st1 hvm2
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          ((strPtr ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
              ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
              ((s.sp + 0x510#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
              ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            wsTrustPostCommonRestPlaced C A2 ctl kit2 ikit2 x ans s0 s.sp st0 ist1 rec' pt k)) ∗ R := by
        dsimp only [kit1, ikit1, kit2, ikit2] at hm2' ⊢
        rw [hA12] at hm2'
        exact Eq.mp (congrArg (sf2.mem ⊨ ·) (by sep_ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, hb0, hb3, hh1, resWord1_trust_err]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (trustPostCommon_err_entails_placed C A2 ctl kit2 ikit2 x ans s0 s.sp st0 ist1
          rec' ses hcur pt k strPtr vt
          (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hsave_rel)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ⟨st1, seamBudget_narrow hsb1 (fun _ h => Or.inl h), ?_⟩)⟩
      have hmod := model_of_trust_err C S x
        { ans with isTrustedIdentity := .error () } (kit.ScopeAt Scope st0 x.rem.val) rec rec' pt ses k
        hload hscope hdec hcur hrem rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with isTrustedIdentity := .error () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, { ans with isTrustedIdentity := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2,
          CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreSpec.traceOfWith_load_trust,
          List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, IdentityStoreSpec.idFinal, A2, kit2, ikit2, ist1] at hm2_err ⊢
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving (.ok t)
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (trustPostCommon_ok_entails_placed C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist1
          rec' pt k o2 o3 o4 o5 o6)) hm1_common
      have hm1_emp : sf.mem ⊨ emp ∗
          ((wsFixedVPlaced kit1 ikit1 x s0 s.sp ∗ wsEnvPlaced A1 x s.sp ∗ wsMsgCells x s.sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A1 (s.sp + 0x120#64) g rec') ∗
            vecU8 A1 (s.sp + 0x290#64) pt ∗ ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
            memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
            memRegion (s.sp + 0x300#64) 0xb00 ∗
            memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
            decStoreExtraPlaced kit1 ikit1 st0 ist1 s0) ∗ R) := by
        rwa [emp_sepConj]
      cases t
      · rw [hrel1] at hx21_1
        obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hvm2, hpost2, hsp2, htr2,
          hx19_2, hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
          segTrust_tail_placed_ok_false (H := H) (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1)
            (hx21 := hx21_1) _ hm1_emp hL1
        rotate_left
        · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
        have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
        let A2 := A.atState lim st1 sf2
        let kit2 := retagSessionStore (A' := A2) kit
        let ikit2 := retagIdentityStore (A' := A2) ikit
        have hA12 : A1 = A2 := atState_eq_of_vmPreserved A lim st1 hvm2
        dsimp only [kit1, ikit1] at hm2'
        rw [hA12] at hm2'
        have hsteps12 := hsteps1.trans hsteps2
        have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
          (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
        have hsb_false : ∀ rec0 rec0' pt0 ses0 k0_,
            ({ ans with isTrustedIdentity := .ok false } : StoreAnswers (List (BitVec 8)) Unit).loadSession = .ok (some rec0) →
            decryptRecord C S uuidTryParse x rec0 = .ok (pt0, rec0') →
            rec0'.currentSession = some ses0 → ses0.state.remoteIdentity = some k0_ →
            SeamBudget M lim
              (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
              st_init st1 (FromTrustedEnv kit kitEnv st0 ikit ikitEnv ist0 x false rec0' k0_) := by
          intro _ _ _ _ _ _ _ _ _
          exact seamBudget_narrow hsb1 (fun _ h => Or.inr (Or.inl h))
        refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with isTrustedIdentity := .ok false }, false, st1, hsb_false, ?_⟩)⟩
        have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
          (ans' := { ans with isTrustedIdentity := .ok false }) (ans := ans) rfl
        refine ⟨hpc2, hmeta2, ?_, ?_, ?_, rec, rec', pt, ses, k,
          hload, hscope, hdec, hcur, hrem, rfl, htrustRel, ?_, ?_⟩
        · rw [hx26_2, hx26_1, hx26, hsp]
        · rw [hx19_2, hx19_1, hsp]
        · rw [hx22_2, hx22_1, hx22, hsp]
        · rw [htr2, htr1, htr, List.append_assoc]
        · rw [hdraws]
          dsimp only [A2, kit2, ikit2, ist1] at hm2' ⊢
          simpa only [hsp, sepConj_assoc] using hm2'
      · rw [hrel1] at hx21_1
        obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hvm2, hpost2, hsp2, htr2,
          hx19_2, hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
          segTrust_tail_placed_ok_true (H := H) (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1)
            (hx21 := hx21_1) _ hm1_emp hL1
        rotate_left
        · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
        have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
        let A2 := A.atState lim st1 sf2
        let kit2 := retagSessionStore (A' := A2) kit
        let ikit2 := retagIdentityStore (A' := A2) ikit
        have hA12 : A1 = A2 := atState_eq_of_vmPreserved A lim st1 hvm2
        dsimp only [kit1, ikit1] at hm2'
        rw [hA12] at hm2'
        have hsteps12 := hsteps1.trans hsteps2
        have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
          (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
        have hsb_true : ∀ rec0 rec0' pt0 ses0 k0_,
            ({ ans with isTrustedIdentity := .ok true } : StoreAnswers (List (BitVec 8)) Unit).loadSession = .ok (some rec0) →
            decryptRecord C S uuidTryParse x rec0 = .ok (pt0, rec0') →
            rec0'.currentSession = some ses0 → ses0.state.remoteIdentity = some k0_ →
            SeamBudget M lim
              (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
              st_init st1 (FromTrustedEnv kit kitEnv st0 ikit ikitEnv ist0 x true rec0' k0_) := by
          intro rec0 rec0' pt0 ses0 k0_ hload0 hdec0 hcur0 hrem0
          dsimp only at hload0
          rw [hload] at hload0; cases hload0
          rw [hdec] at hdec0; cases hdec0
          rw [hcur] at hcur0; cases hcur0
          rw [hrem] at hrem0; cases hrem0
          exact seamBudget_narrow hsb1 (fun _ h => Or.inr (Or.inr h))
        refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with isTrustedIdentity := .ok true }, true, st1, hsb_true, ?_⟩)⟩
        have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
          (ans' := { ans with isTrustedIdentity := .ok true }) (ans := ans) rfl
        refine ⟨hpc2, hmeta2, ?_, ?_, ?_, rec, rec', pt, ses, k,
          hload, hscope, hdec, hcur, hrem, rfl, htrustRel, ?_, ?_⟩
        · rw [hx26_2, hx26_1, hx26, hsp]
        · rw [hx19_2, hx19_1, hsp]
        · rw [hx22_2, hx22_1, hx22, hsp]
        · rw [htr2, htr1, htr, List.append_assoc]
        · rw [hdraws]
          dsimp only [A2, kit2, ikit2, ist1] at hm2' ⊢
          simpa only [hsp, sepConj_assoc] using hm2'
  · exact (not_satisfies_false_sepConj (hpan_post1 hm1_pan)).elim
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegTrustExtPlacedBudget
