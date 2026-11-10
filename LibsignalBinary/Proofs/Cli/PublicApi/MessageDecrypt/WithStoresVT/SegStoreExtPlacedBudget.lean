/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStorePlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExtPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `SegStore` (`+0x2388 → +0x24d4 / +0x2294`)

Proves budget-threaded (`RustCliAllocBudget M`) relocatable `segStoreVX_placed_ok` on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExtPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalHooks LibsignalPlacement)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost sessionRecordAt storeHookStr)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreSession (pollTag)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsAt NoFsEv SessionStoreSpec withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (resWord1 wsStackV)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (draws_eq_of_loadSession_eq memRegion_36_entails_cells resWord1_lsr8)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore
  (model_of_store_err model_of_store_ok storeCallStack storeCallStack_le)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
  (pollOutPlacedRel wsMetaPlaced_of_steps)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegStore
  (storeCallPost_entails_common_placed storeCall_entails_storeCallPre_placed
   storePostCommon_err_entails_placed storePostCommon_ok_pre_tail_placed
   storePost_ok_entails_placed wsStoreCallPrePlaced wsStoreFramePlaced
   wsStorePostCommonRestPlaced wsStoreTailOkFramePlaced wsStoreTailOkPost_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv StoreStepEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget TryDecryptEnvArgs)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromStoreCallEnv WithStoresDecEnv)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (DropSessionStructureLocal2PlacedOk ErrJoinStateVPlaced ResultFinalStateVPlaced
   StoreCallStateVPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (DecSegVXPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
  (atState_eq_of_vmPreserved)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
  (DropSessionStructureLocal2BudgetOk SessionOnlyKitBudgetOkSE
   dropSessionStructureLocal2BudgetSpec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStoreAuxPlacedBudget
  (segStore_call_placed_wp segStore_tail_placed_err segStore_tail_placed_ok)
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

private theorem seamBudget_advance_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv : List AllocEvent → Prop} {st_init st : M.σ} {evs : List AllocEvent}
    (hs : SeamBudget M lim fullEnv st_init st FreeOnlyEvs) (hevs : FreeOnlyEvs evs) :
    SeamBudget M lim fullEnv st_init (M.stepEvents evs st) FreeOnlyEvs :=
  hs.step (fun _ _ h1 h2 => FreeOnlyEvs.append h1 h2) hevs

private def toTwinsSsEnv {A : CryptoVerification.RustHeap.RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} (e : SessionStoreBudgetEnv kit) :
    LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins.SessionStoreBudgetEnv kit :=
  ⟨e.loadPollEnv, e.storePollEnv⟩

private theorem kit_to_twins [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (h : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H) :
    SessionOnlyKitBudgetOkSE A lim kit (toTwinsSsEnv kitEnv) Scope encRecord H where
  loadShim hi := subroutine_ok_mono (h.loadShim hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  loadPoll hi := subroutine_ok_mono (h.loadPoll hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  loadFutDrop hi := subroutine_ok_mono (h.loadFutDrop hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  storeShim hi := subroutine_ok_mono (h.storeShim hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  storePoll hi := subroutine_ok_mono (h.storePoll hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)
  storeFutDrop hi := subroutine_ok_mono (h.storeFutDrop hi)
    (fun _ _ _ hp => hp) (fun _ _ _ _ hq => hq)

private theorem dropSs_to_twins [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (h : DropSessionStructureLocal2PlacedOk A lim H) :
    DropSessionStructureLocal2BudgetOk A lim H := by
  refine subroutine_ok_mono h (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => ?_)
  · dsimp only [withLsRoCl,
      LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec,
      dropSessionStructureLocal2BudgetSpec] at hp ⊢
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hp
  · dsimp only [withLsRoCl,
      LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec,
      dropSessionStructureLocal2BudgetSpec] at hq ⊢
    exact hq

private theorem storeStepEnv_of_twins {A : CryptoVerification.RustHeap.RustAlloc}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState} {rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal}
    {rec' : SessionRecord (List (BitVec 8))} {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins.StoreStepEnv
      kit (toTwinsSsEnv kitEnv) st0 rem rec' evs) :
    StoreStepEnv kit kitEnv st0 rem rec' evs := by
  have hpos : 0 < kit.storeBoxSize :=
    Nat.pos_of_ne_zero (fun h0 => kit.storeBoxSize_ne_zero (by simp [h0]))
  rcases h with h1 | ⟨e1, e2, rfl, h1, h2a | ⟨e2a, e2b, rfl, h2a, ⟨h0, _⟩ | ⟨_, h2b⟩⟩⟩
  · exact SeqEnv.inl h1
  · exact SeqEnv.append h1 (SeqEnv.inl h2a)
  · omega
  · exact SeqEnv.append h1 (SeqEnv.append h2a h2b)

private theorem rep_wsStoreTailOkFrame_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (P1 P2 : SepProp) (ctl : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp cap ptr : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) :
    wsStoreTailOkFramePlaced C ({ pool := P1, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P1, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P1, live := A.live }) ikit) x ans s0 sp cap ptr st ist pt =
    wsStoreTailOkFramePlaced C ({ pool := P2, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P2, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P2, live := A.live }) ikit) x ans s0 sp cap ptr st ist pt := rfl

attribute [local semireducible] SepWP in
set_option maxHeartbeats 1600000 in
/-- Budget-threaded relocatable `segStoreVX_placed_ok` on `lsProg_463 H`. -/
theorem segStoreVX_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    (hdrop2 : DropSessionStructureLocal2PlacedOk A lim H)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (R : SepProp) (s0 s : State)
    (haddr : kit.addrOk x.rem.val)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (hstB : StoreCallStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H
      kit kitEnv ikit ikitEnv st0 ist0 Scope Extra x st_init R s0 s
      (fun s' =>
        ResultFinalStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s' ∨
        ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
          kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s') := by
  intro hL
  rcases hstB with ⟨st_b, hsb_all, hst⟩
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, c, hload, hscope, hdec, hcur, hrem, htrust, hsave, htrustRel, hsaveRel, htr, hm⟩
  have hsb : SeamBudget M lim
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse tdEnv Scope x)
      st_init st_b (FromStoreCallEnv kit kitEnv st0 x.rem.val rec') :=
    hsb_all rec pt rec' hload hdec
  have hfits : FitsEnv M lim st_b
      (LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins.StoreStepEnv
        kit (toTwinsSsEnv kitEnv) st0 x.rem.val rec') :=
    hsb.1.seq_left.mono (fun _ => storeStepEnv_of_twins)
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, hs⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, hs, and_self]).mono (fun _ h => h.1) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hrecOk : kit.RecOk rec' := hyps.recOk x rec pt rec' haddr hscope hdec
  let A0 := A.atState lim st_b s
  let kit0 := retagSessionStore (A' := A0) kit
  let ikit0 := retagIdentityStore (A' := A0) ikit
  rw [← hsp] at hx26 hx22 hm
  let ist2 := ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
    x.rem.val k ans.saveIdentity
  have hm_pre : s.mem ⊨
      (∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          ⌜wsStackV kit0 ikit0 ≤ s0.sp.toNat⌝ ∗
          wsStoreCallPrePlaced A0 kit0 x s0 s.sp (s.readReg64 .x26) g rec' st0 c0 c1 d0 d1 d2 d3 d5 ∗
          wsStoreFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp ist2 pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (storeCall_entails_storeCallPre_placed C A0 ctl kit0 ikit0 x ans s0 s.sp (s.readReg64 .x26)
        st0 ist2 rec' pt hsp hx26)) ?_
    dsimp only [A0, kit0, ikit0, ist2] at hm ⊢
    simpa only [sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨g, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  have hstack_lt : storeCallStack kit ≤ 2 ^ 64 := by
    have h1 := storeCallStack_le kit0 ikit0
    have := s0.sp.isLt; unfold wsStackV at hbound; change storeCallStack kit0 ≤ 2 ^ 64; omega
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segStore_call_placed_wp hyps.hooks.dealloc (kit_to_twins hyps.kit) hstack_lt
      (self := s0.readReg64 .x3) (addrA := x.remA) (addr := x.rem)
      (g := g) (record := rec') (st := st0)
      (c0 := c0) (c1 := c1) (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d5 := d5)
      (R := wsStoreFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp ist2 pt ∗ R)
      hcrl hfits haddr hrecOk hpc hrun hsp_align hfsAt
      (wsStoreFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp ist2 pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _, hm1_pan, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx22_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨evs_store, ans_store, box, strPtr, vt, o1, o2, o3, o4, o5, o6, hm1'⟩
    let st_b1 := M.stepEvents evs_store st_b
    let A1 := A.atState lim st_b1 sf
    let kit1 := retagSessionStore (A' := A1) kit
    let ikit1 := retagIdentityStore (A' := A1) ikit
    have hm1_common : sf.mem ⊨
        (⌜kit.storeRel st0 x.rem.val rec' ans_store ∧
            sf.readReg64 .x28 = pollTag ans_store ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord x.rem.val rec' ans_store ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 ans_store ∧
            LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins.StoreStepEnv
              kit (toTwinsSsEnv kitEnv) st0 x.rem.val rec' evs_store⌝ ∗
          (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
            ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          sessionRecordAt A1 (s.sp + 0x120#64) g rec' ∗
          wsStorePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp
            (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      rw [sepConj_assoc]; apply Entails.pure_left; intro hpure
      refine Entails.pure_right hpure ?_
      exact storeCallPost_entails_common_placed C A1 ctl kit1 ikit1 x ans s0 s.sp (s.readReg64 .x26) g rec'
        (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt
        ans_store box strPtr o2 o3 o4 o5 o1 o6 hsp hx26 hbound
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hstoreRel, hx28_1, htr1, hx21_1, hrel1, hevs_store⟩, hm1_common⟩
    have hsb1 := seamBudget_advance hsb (storeStepEnv_of_twins hevs_store)
    have hL1 := hsteps1.codeLoaded hL
    have hcrl1 := hcrl.of_keepsFrozen hsteps1.keepsFrozen
    rcases ans_store with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x550#64) ↦₆₄ o2) ∗ ((sf.sp + 0x558#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x560#64) ↦₆₄ o4) ∗ ((sf.sp + 0x568#64) ↦₆₄ o5) ∗ ((sf.sp + 0x570#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗ ((sf.sp + 0x590#64) ↦₆₄ e2) ∗
              ((sf.sp + 0x598#64) ↦₆₄ e3) ∗ ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            ((strPtr ↦ᵣ storeHookStr) ∗
              sessionRecordAt A1 (s.sp + 0x120#64) g rec' ∗
              wsStorePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st1 ist2 pt)) ∗ R := by
        rw [hsp1]; refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0; apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2; apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hvm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_placed_err (H := H) (R := ((strPtr ↦ᵣ storeHookStr) ∗
            sessionRecordAt A1 (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st1 ist2 pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            sessionRecordAt A1 (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st1 ist2 pt) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      let A2 := A.atState lim st_b1 sf2
      let kit2 := retagSessionStore (A' := A2) kit
      let ikit2 := retagIdentityStore (A' := A2) ikit
      have hA12 : A1 = A2 := atState_eq_of_vmPreserved A lim st_b1 hvm2
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          ((strPtr ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
              ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            sessionRecordAt A2 (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A2 ctl kit2 ikit2 x ans s0 s.sp st1 ist2 pt)) ∗ R := by
        dsimp only [kit1, ikit1, kit2, ikit2] at hm2' ⊢
        rw [hA12] at hm2'
        exact Eq.mp (congrArg (sf2.mem ⊨ ·) (by sep_ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (storePostCommon_err_entails_placed C A2 ctl kit2 ikit2 x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt strPtr vt (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ⟨st_b1, hsb1, ?_⟩)⟩
      have hmod := model_of_store_err C S x
        { ans with storeSession := .error () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .error () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, { ans with storeSession := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, IdentityStoreSpec.idFinal, A2, kit2, ikit2, ist2] at hm2_err ⊢
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.ok ())
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (storePostCommon_ok_pre_tail_placed C A1 ctl kit1 ikit1 x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt o2 o3 o4 o5 o6 hsp)) hm1_common
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_ok
      rcases hm1_ok with ⟨G, cap, ptr, s0_580, s1_588, s2_lo, s2_hi, s3_598, s4_5a0,
        t0_300, t1_308, t2_310, t3_318, t4_320, hm1_ok⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_ok
      rcases hm1_ok with ⟨⟨_, hprev_lt, hprev_ptr⟩, hm1_ok⟩
      rw [sepConj_assoc, ← hsp1] at hm1_ok
      have hx26_sf : sf.readReg64 .x26 = sf.sp + 0xa0#64 := by rw [hx26_1, hx26, hsp1]
      have hx22_sf : sf.readReg64 .x22 = sf.sp + 0x294#64 := by rw [hx22_1, hx22, hsp1]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_placed_ok (st_b := st_b1) hyps.hooks.dealloc (dropSs_to_twins hdrop2)
          (R := wsStoreTailOkFramePlaced C A1 ctl kit1 ikit1 x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R)
          hcrl1 hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx26_sf hx22_sf hprev_lt hprev_ptr
          (wsStoreTailOkFramePlaced C A1 ctl kit1 ikit1 x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R) hm1_ok hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm2'
      rcases hm2' with ⟨evs_tail, hm2'⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm2'
      rcases hm2' with ⟨hevs_tail, hm2'⟩
      have hsb2 := seamBudget_advance_freeOnly hsb1 hevs_tail
      let st_b2 := M.stepEvents evs_tail st_b1
      let A2 := A.atState lim st_b2 sf2
      let kit2 := retagSessionStore (A' := A2) kit
      let ikit2 := retagIdentityStore (A' := A2) ikit
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1, ← sepConj_assoc] at hm2'
      have hm2_a2 : sf2.mem ⊨
          (wsStoreTailOkPost_placed A2 s.sp g.prevCap g.prevPtr
            (cap.extractLsb' 0 32)
            (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
            ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
            ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
            s2_hi s3_598 s4_5a0 ∗
            wsStoreTailOkFramePlaced C A2 ctl kit2 ikit2 x ans s0 s.sp cap ptr st1 ist2 pt) ∗ R := by
        unfold wsStoreTailOkPost_placed
        dsimp only [A1, A2, kit1, ikit1, kit2, ikit2, st_b2, RustCliAllocBudget.atState] at hm2' ⊢
        rw [rep_wsStoreTailOkFrame_eq (P1 := A.pool lim st_b1 sf)
          (P2 := A.pool lim (M.stepEvents evs_tail st_b1) sf2)] at hm2'
        simpa only [sepConj_assoc] using hm2'
      have hm2_ok := Satisfies.mono (sepConj_mono_left
        (storePost_ok_entails_placed C A2 ctl kit2 ikit2 x ans s0 s.sp g.prevCap g.prevPtr cap ptr
          st1 ist2 pt
          (cap.extractLsb' 0 32)
          (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
          s2_hi s3_598 s4_5a0 (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          hx28_2 hx20_2 hx21_2 rfl rfl rfl rfl hsp hbound)) hm2_a2
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨st_b2, hsb2, ?_⟩)⟩
      have hmod := model_of_store_ok C S x
        { ans with storeSession := .ok () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .ok () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, { ans with storeSession := .ok () }, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, IdentityStoreSpec.idFinal, A2, kit2, ikit2, st1, ist2] at hm2_ok ⊢
        simpa only [hsp, sepConj_assoc] using hm2_ok
  · exact (not_satisfies_false_sepConj (hpan_post1 hm1_pan)).elim
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegStoreExtPlacedBudget
