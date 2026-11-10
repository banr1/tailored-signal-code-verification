/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExtPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `SegSave` (`+0x2150 → +0x2388 / +0x2294`)

Proves budget-threaded (`RustCliAllocBudget M`) relocatable `segSaveVX_placed_ok` on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExtPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoGames.LibsignalSession (Crypto IdentityKey)
open CryptoGames.LibsignalSessionApi (IdentityChange SessionRecord StoreAnswers)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt storeHookStr)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsAt NoFsEv SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
  (decryptRecord resWord1 wsCalleeStackV wsMsgCells wsStackV)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (draws_eq_of_loadSession_eq memRegion_36_entails_cells model_of_save_err
   resWord1_lsr8 saveCallStack saveCallStack_le_wsCalleeV savePollTag)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
  (decStoreExtraPlaced saveCallPCPlaced wsEnvPlaced wsFixedVPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (pollOutPlacedRel saveCallPost_entails_common_placed savePostCommon_err_entails_placed
   savePostCommon_ok_entails_placed trusted_entails_saveCallPre_placed wsMetaPlaced_of_steps
   wsSaveCallPrePlaced wsSaveFramePlaced wsSavePostCommonRestPlaced)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (IdentityStoreKitPlacedOkI)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromStoreCallEnv FromTrustedEnv FromTrustedTrueEnv WithStoresDecEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (ErrJoinStateVPlaced StoreCallStateVPlaced TrustedStateVPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (DecSegVXPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
  (atState_eq_of_vmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
  (IdentityStoreKitBudgetOkI SaveStepEnvDec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudget
  (segSave_call_placed_wp segSave_tail_placed_err segSave_tail_placed_ok)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
  (DecFsCtxExtPlaced DecHypsExtPlaced)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

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

private theorem saveStepEnv_of_twins {A : CryptoVerification.RustHeap.RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist1 : ikit.IdState} {rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal}
    {k : IdentityKey} {evs : List AllocEvent}
    (h : SaveStepEnvDec ikit (toTwinsIdEnv ikitEnv) ist1 rem k evs) :
    SaveStepEnv ikit ikitEnv ist1 rem k evs := by
  have hpos : 0 < ikit.saveBoxSize :=
    Nat.pos_of_ne_zero (fun h0 => ikit.saveBoxSize_ne_zero (by simp [h0]))
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2a | ⟨e2a, e2b, rfl, h2a, ⟨h0, _⟩ | ⟨_, h2b⟩⟩⟩
  · exact SeqEnv.inl h1
  · exact SeqEnv.append h1 (SeqEnv.inl h2a)
  · omega
  · exact SeqEnv.append h1 (SeqEnv.append h2a h2b)

attribute [local semireducible] SepWP in
set_option maxHeartbeats 800000 in
/-- Budget-threaded relocatable `segSaveVX_placed_ok` on `lsProg_463 H`. -/
theorem segSaveVX_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    (hstB : TrustedStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans true R s0 s) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H
      kit kitEnv ikit ikitEnv st0 ist0 Scope Extra x st_init R s0 s
      (fun s' =>
        (∃ ans', StoreCallStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans' R s0 s') ∨
        ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s') := by
  intro hL
  rcases hstB with ⟨st, hsb_all, hst⟩
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hsb : SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
      st_init st (FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k) := by
    simpa only [FromTrustedEnv, ↓reduceIte] using
      hsb_all rec rec' pt ses k hload hdec hcur hrem
  have hfsAt : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, -⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, and_self]).mono (fun _ h => h.2) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hpc' : s.pc = saveCallPCPlaced := hpc
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  have hfits : FitsEnv M lim st (SaveStepEnvDec ikit (toTwinsIdEnv ikitEnv) ist1 x.rem.val k) := by
    dsimp only [ist1]; rw [htrust]
    exact hsb.1.seq_left.mono (fun _ => saveStepEnv_of_twins)
  let A0 := A.atState lim st s
  let kit0 := retagSessionStore (A' := A0) kit
  let ikit0 := retagIdentityStore (A' := A0) ikit
  rw [← hsp] at hx26 hx19 hx22 hm
  have hm_pre : s.mem ⊨
      (⌜wsStackV kit0 ikit0 ≤ s0.sp.toNat⌝ ∗
        ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          wsSaveCallPrePlaced A0 ikit0 x s0 s.sp ist1 k c0 c1 d0 d1 d2 d3 d5 ∗
          wsSaveFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_saveCallPre_placed C A0 ctl kit0 ikit0 x ans s0 s.sp st0 ist1 rec' pt k hsp)) ?_
    dsimp only [A0, kit0, ikit0, ist1] at hm ⊢
    simpa only [sepConj_assoc] using hm
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  have hstack_lt : saveCallStack ikit ≤ 2 ^ 64 := by
    have hlt := s0.sp.isLt
    have h1 := saveCallStack_le_wsCalleeV kit0 ikit0
    have h2 : wsCalleeStackV kit0 ikit0 ≤ wsStackV kit0 ikit0 := Nat.le_add_right _ _
    change saveCallStack ikit0 ≤ 2 ^ 64
    omega
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segSave_call_placed_wp hyps.hooks.dealloc (ikit_to_twins hyps.ikit) hstack_lt
      (R := wsSaveFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt ∗ R)
      hcrl hfits haddr hpc' hrun hsp_align hx19 hfsAt
      (wsSaveFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _, hm1_pan, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx22_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨evs_save, ans_save, box, strPtr, vt, o1, o2, o3, o4, o5, o6, hm1'⟩
    let st1 := M.stepEvents evs_save st
    let A1 := A.atState lim st1 sf
    let kit1 := retagSessionStore (A' := A1) kit
    let ikit1 := retagIdentityStore (A' := A1) ikit
    have hm1_common : sf.mem ⊨
        (⌜sf.readReg64 .x28 = savePollTag ans_save ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            ikit.saveRel ist1 x.rem.val k ans_save ∧
            sf.trace = s.trace ++ ikit.saveEvs x.rem.val k ans_save ∧
            pollOutPlacedRel strPtr vt o2 o3 o4 o5 o1 ans_save ∧
            SaveStepEnvDec ikit (toTwinsIdEnv ikitEnv) ist1 x.rem.val k evs_save⌝ ∗
          (((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
            ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
            ((s.sp + 0x540#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_save.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          wsSavePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0
            (ikit.saveUpdate ist1 x.rem.val k ans_save) rec' pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpure
      refine Entails.pure_right hpure ?_
      exact saveCallPost_entails_common_placed C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist1 rec' pt k
        ans_save box strPtr o2 o3 o4 o5 o1 o6 hsp hbound
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hx28_1, hx21_1, hsaveRel, htr1, hrel1, hevs_save⟩, hm1_common⟩
    have hevs_save' : SaveStepEnv ikit ikitEnv
        (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k evs_save := by
      dsimp only [ist1] at hevs_save
      rw [htrust] at hevs_save
      exact saveStepEnv_of_twins hevs_save
    have hsb1 := seamBudget_advance hsb hevs_save'
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_save with ⟨⟨⟩⟩ | c
    · let ist2 := ikit.saveUpdate ist1 x.rem.val k (.error ())
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x520#64) ↦₆₄ o2) ∗ ((sf.sp + 0x528#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x530#64) ↦₆₄ o4) ∗ ((sf.sp + 0x538#64) ↦₆₄ o5) ∗
              ((sf.sp + 0x540#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗
              ((sf.sp + 0x590#64) ↦₆₄ e2) ∗ ((sf.sp + 0x598#64) ↦₆₄ e3) ∗
              ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            (strPtr ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist2 rec' pt) ∗ R := by
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
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte]
        exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hvm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segSave_tail_placed_err (H := H) (R := ((strPtr ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist2 rec' pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist2 rec' pt) ∗ R) hm1_err hL1
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
            ((((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
              ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗ ((s.sp + 0x540#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            wsSavePostCommonRestPlaced C A2 ctl kit2 ikit2 x ans s0 s.sp st0 ist2 rec' pt)) ∗ R := by
        dsimp only [kit1, ikit1, kit2, ikit2] at hm2' ⊢
        rw [hA12] at hm2'
        exact Eq.mp (congrArg (sf2.mem ⊨ ·) (by sep_ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (savePostCommon_err_entails_placed C A2 ctl kit2 ikit2 x ans s0 s.sp st0 ist2 rec' ses hcur pt
          strPtr vt (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ⟨st1, seamBudget_narrow hsb1 (fun _ h => Or.inl h), ?_⟩)⟩
      have hmod := model_of_save_err C S x
        { ans with saveIdentity := .error () } rec rec' pt ses k
        hload hdec hcur hrem htrust rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with saveIdentity := .error () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, { ans with saveIdentity := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2,
          CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreSpec.traceOfWith_load_trust_save,
          List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, IdentityStoreSpec.idFinal, A2, kit2, ikit2, ist1, ist2] at hm2_err ⊢
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let ist2 := ikit.saveUpdate ist1 x.rem.val k (.ok c)
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (savePostCommon_ok_entails_placed C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist2 rec' pt o2 o3 o4 o5 o6)) hm1_common
      have hm1_emp : sf.mem ⊨ emp ∗
          ((wsFixedVPlaced kit1 ikit1 x s0 s.sp ∗ wsEnvPlaced A1 x s.sp ∗ wsMsgCells x s.sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A1 (s.sp + 0x120#64) g rec') ∗
            vecU8 A1 (s.sp + 0x290#64) pt ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗
            memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
            memRegion (s.sp + 0x300#64) 0xb00 ∗
            memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
            decStoreExtraPlaced kit1 ikit1 st0 ist2 s0) ∗ R) := by
        rwa [emp_sepConj]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hvm2, hpost2, hsp2, htr2,
        hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
        segSave_tail_placed_ok (H := H) (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1) _ hm1_emp hL1
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
      have hsb_store : ∀ rec0 pt0 rec0',
          ({ ans with saveIdentity := .ok c } : StoreAnswers (List (BitVec 8)) Unit).loadSession = .ok (some rec0) →
          decryptRecord C S uuidTryParse x rec0 = .ok (pt0, rec0') →
          SeamBudget M lim
            (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
            st_init st1 (FromStoreCallEnv kit kitEnv st0 x.rem.val rec0') := by
        intro rec0 pt0 rec0' hload0 hdec0
        dsimp only at hload0
        rw [hload] at hload0; cases hload0
        rw [hdec] at hdec0; cases hdec0
        exact seamBudget_narrow hsb1 (fun _ h => Or.inr h)
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with saveIdentity := .ok c }, st1, hsb_store, ?_⟩)⟩
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with saveIdentity := .ok c }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, rec, rec', pt, ses, k, c,
        hload, hscope, hdec, hcur, hrem, htrust, rfl, htrustRel, hsaveRel, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx22_2, hx22_1, hx22, hsp]
      · rw [htr2, htr1, htr, List.append_assoc]
      · rw [hdraws]
        dsimp only [A2, kit2, ikit2, ist1, ist2] at hm2' ⊢
        simpa only [hsp, sepConj_assoc] using hm2'
  · exact (not_satisfies_false_sepConj (hpan_post1 hm1_pan)).elim
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegSaveExtPlacedBudget
