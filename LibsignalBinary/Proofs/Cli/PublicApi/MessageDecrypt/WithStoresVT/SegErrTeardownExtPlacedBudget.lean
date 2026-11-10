/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegErrTeardownPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExtPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `SegErrTeardown` (`+0x2294 / +0x22a8 → +0x24d4`)

Proves budget-threaded (`RustCliAllocBudget M`) relocatable `segErrTeardownVX_placed_ok` on
`lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExtPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoGames.LibsignalSession (Crypto SessionState)
open CryptoGames.LibsignalSessionApi (ApiError SessionRecord StoreAnswers StoreCall)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal apiDecResultAt)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
  (StagedRes droppableRecordAt wsCalleeStack wsMsgCells)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
  (decStoreExtraPlaced wsEnvPlaced wsFixedVPlaced)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (wsMetaPlaced_of_steps)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown
  (curPre ptPost ptPre resOk teardownPost teardownPre)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown
  (ej_false_expose_placed ej_true_expose_placed ptFramePlaced pt_post_entails_placed
   teardownFramePlaced teardown_post_entails_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv retagIdentityStore)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget TryDecryptEnvArgs)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (DropSessionStructureLocal2PlacedOk ErrJoinStateVPlaced ResultFinalStateVPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget (DecSegVXPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
  (DecHypsExtPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
  (DropSessionStructureLocal2BudgetOk dropSessionStructureLocal2BudgetSpec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegErrTeardownPlacedBudget
  (teardown_pt_placed_ok teardown_tail_placed_ok)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

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

private theorem seamBudget_advance_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv : List AllocEvent → Prop} {st_init st : M.σ} {evs : List AllocEvent}
    (hs : SeamBudget M lim fullEnv st_init st FreeOnlyEvs) (hevs : FreeOnlyEvs evs) :
    SeamBudget M lim fullEnv st_init (M.stepEvents evs st) FreeOnlyEvs :=
  hs.step (fun _ _ h1 h2 => FreeOnlyEvs.append h1 h2) hevs

private theorem rep_curPre_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (ss : BitVec 64) (cs : Option (SessionGhost × SessionState (List (BitVec 8)))) :
    curPre ({ pool := P, live := A.live }) ss cs = curPre A.repAlloc ss cs := by
  rcases cs with _ | ⟨_, _⟩ <;> rfl

private theorem rep_droppableRecordAt_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (r : BitVec 64) (cs : Option (SessionGhost × SessionState (List (BitVec 8)))) :
    droppableRecordAt ({ pool := P, live := A.live }) r cs = droppableRecordAt A.repAlloc r cs := by
  rcases cs with _ | ⟨_, _⟩ <;> rfl

private theorem rep_apiDecResultAt_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (r : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) :
    apiDecResultAt ({ pool := P, live := A.live }) r res = apiDecResultAt A.repAlloc r res := by
  rcases res with e | _
  · cases e <;> rfl
  · rfl

private theorem rep_resOk_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P1 P2 : SepProp)
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) (F : SepProp) :
    resOk ({ pool := P1, live := A.live }) x28 w20 w21 res w0 w1 w2 w3 w4 F =
    resOk ({ pool := P2, live := A.live }) x28 w20 w21 res w0 w1 w2 w3 w4 F := by
  unfold resOk
  simp only [rep_apiDecResultAt_eq]

private theorem rep_stagedRes_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (x28 w20 w21 src : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) :
    StagedRes ({ pool := P, live := A.live }) x28 w20 w21 src res =
    StagedRes A.repAlloc x28 w20 w21 src res := by
  unfold StagedRes
  simp only [rep_apiDecResultAt_eq]

private theorem rep_ptFrame_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (P1 P2 : SepProp) (ctl : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) :
    ptFramePlaced C ({ pool := P1, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P1, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P1, live := A.live }) ikit)
      x ans s0 sp cs x28 w20 w21 res =
    ptFramePlaced C ({ pool := P2, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P2, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P2, live := A.live }) ikit)
      x ans s0 sp cs x28 w20 w21 res := by
  unfold ptFramePlaced
  simp only [rep_droppableRecordAt_eq, rep_stagedRes_eq]
  rfl

private theorem rep_teardownFrame_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (P1 P2 : SepProp) (ctl : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (F : SepProp) :
    teardownFramePlaced C ({ pool := P1, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P1, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P1, live := A.live }) ikit)
      x ans s0 sp F =
    teardownFramePlaced C ({ pool := P2, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P2, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P2, live := A.live }) ikit)
      x ans s0 sp F := rfl

private theorem rep_decStoreExtra_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    decStoreExtraPlaced (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit) st ist s0 =
    decStoreExtraPlaced kit ikit st ist s0 := rfl

private theorem rep_storeFinal_eq {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagSessionStore (A' := A') kit).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, retagSessionStore, ih]

private theorem rep_callsRel_eq {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagSessionStore (A' := A') kit).callsRel st0 ans calls = kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.callsRel, retagSessionStore, ih]

private theorem rep_idFinal_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).idFinal ist0 ans calls = ikit.idFinal ist0 ans calls := by
  induction calls generalizing ist0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [IdentityStoreSpec.idFinal, retagIdentityStore, ih]

private theorem rep_idCallsRel_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).idCallsRel ist0 ans calls = ikit.idCallsRel ist0 ans calls := by
  induction calls generalizing ist0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [IdentityStoreSpec.idCallsRel, retagIdentityStore, ih]

private theorem rep_callEvs_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    (retagIdentityStore (A' := A') ikit).callEvs (retagSessionStore (A' := A') kit) encRecord ans =
      ikit.callEvs kit encRecord ans := by
  ext c; cases c <;> rfl

private theorem rep_traceOfWith_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).traceOfWith (retagSessionStore (A' := A') kit) encRecord ans calls =
      ikit.traceOfWith kit encRecord ans calls := by
  simp only [IdentityStoreSpec.traceOfWith, rep_callEvs_eq]

attribute [local semireducible] SepWP in
theorem segErrTeardownVX_false_placed [LibsignalPlacement] {M : AllocCostModel}
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
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    (hstB : ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init false R s0 s) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H
      kit kitEnv ikit ikitEnv st0 ist0 Scope Extra x st_init R s0 s
      (fun s' => ResultFinalStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s') := by
  intro hL
  rcases hstB with ⟨st_b, hsb, hst⟩
  rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, _hnok, hscope, hcalls, hid_calls, htr, hm⟩
  rw [rep_callsRel_eq] at hcalls
  rw [rep_idCallsRel_eq] at hid_calls
  rw [rep_traceOfWith_eq] at htr
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  let A0 := A.atState lim st_b s
  let kit0 := retagSessionStore (A' := A0) kit
  let ikit0 := retagIdentityStore (A' := A0) ikit
  rw [← hsp] at hx26 hm
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  let R' : SepProp :=
    decStoreExtraPlaced kit ikit
      (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
      (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
  have hm_r' : s.mem ⊨ wsFixedVPlaced kit0 ikit0 x s0 s.sp ∗ wsEnvPlaced A0 x s.sp ∗ wsMsgCells x s.sp ∗
      droppableRecordAt A0 (s.sp + 0x120#64) cs ∗ memRegion (s.sp + 0x290#64) 24 ∗
      StagedRes A0 (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
        (x.model C S uuidTryParse ans).1 ∗
      memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
      memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
    dsimp only [A0, kit0, ikit0, R', RustCliAllocBudget.atState] at hm ⊢
    simpa only [rep_decStoreExtra_eq, rep_storeFinal_eq, rep_idFinal_eq, sepConj_assoc] using hm
  have hm_pre := Satisfies.mono (ej_false_expose_placed C A0 ctl kit0 ikit0 x ans s0 s.sp cs _ _ _ _ R') hm_r'
  simp only [satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨prevCap, prevPtr, w0, w1, w2, w3, w4, F, t0, t1, t2, t3, t4, hm_pre⟩
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hprev_lt, hm_pre⟩ := hm_pre
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hres, hm_pre⟩ := hm_pre
  have hm_pre' : s.mem ⊨
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        curPre A.repAlloc (s.sp + 0x138#64) cs ∗
        ((s.sp + 0x300#64) ↦₆₄ t0) ∗ ((s.sp + 0x308#64) ↦₆₄ t1) ∗ ((s.sp + 0x310#64) ↦₆₄ t2) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3) ∗ ((s.sp + 0x320#64) ↦₃₂ t4) ∗
        ((s.sp + 0x580#64) ↦₆₄ w0) ∗ ((s.sp + 0x588#64) ↦₆₄ w1) ∗ ((s.sp + 0x590#64) ↦₆₄ w2) ∗
        ((s.sp + 0x598#64) ↦₆₄ w3) ∗ ((s.sp + 0x5a0#64) ↦₃₂ w4) ∗
        A.pool lim st_b s ∗ stackAt s.sp wsCalleeStack) ∗
      (teardownFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp F ∗ R') := by
    unfold teardownPre at hm_pre
    dsimp only [A0, RustCliAllocBudget.atState] at hm_pre ⊢
    simpa only [rep_curPre_eq] using hm_pre
  obtain ⟨sf, hsteps, ⟨hpc2, hrun2, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ :=
    teardown_tail_placed_ok (st_b := st_b) (cs := cs) (prevCap := prevCap) (prevPtr := prevPtr)
      (s0_580 := w0) (s1_588 := w1) (s2_590 := w2) (s3_598 := w3) (s4_5a0 := w4)
      (t0_300 := t0) (t1_308 := t1) (t2_310 := t2) (t3_318 := t3) (t4_320 := t4)
      (R := teardownFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp F ∗ R')
      hyps.hooks.dealloc (dropSs_to_twins hdrop2) hcrl hpc hrun hsp_align hx28 hx26 hprev_lt
      (teardownFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp F ∗ R') hm_pre' hL
  rotate_left
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hmf', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost hmf
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf'
  rcases hmf' with ⟨evs_td, hmf'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hmf'
  rcases hmf' with ⟨hevs_td, hmf'⟩
  have hsb1 := seamBudget_advance_freeOnly hsb hevs_td
  let st_b1 := M.stepEvents evs_td st_b
  let A1 := A.atState lim st_b1 sf
  let kit1 := retagSessionStore (A' := A1) kit
  let ikit1 := retagIdentityStore (A' := A1) ikit
  have hres1 : resOk A1 (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21)
      (x.model C S uuidTryParse ans).1 w0 w1 w2 w3 w4 F := by
    dsimp only [A0, A1, RustCliAllocBudget.atState] at hres ⊢
    rwa [rep_resOk_eq (P1 := A.pool lim st_b s) (P2 := A.pool lim st_b1 sf)] at hres
  have hmf_a1 : sf.mem ⊨
      teardownPost A1 s.sp prevCap prevPtr w0 w1 w2 w3 w4 ∗
        (teardownFramePlaced C A1 ctl kit1 ikit1 x ans s0 s.sp F ∗ R') := by
    unfold teardownPost
    dsimp only [A0, A1, kit0, ikit0, kit1, ikit1, st_b1, RustCliAllocBudget.atState] at hmf' ⊢
    rwa [rep_teardownFrame_eq (P1 := A.pool lim st_b s) (P2 := A.pool lim st_b1 sf)] at hmf'
  have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps hrun2 hsp2 hx29_2 hx27_2 hvregs_2
  have hm_fin := Satisfies.mono (teardown_post_entails_placed C A1 ctl kit1 ikit1 x ans s0 s.sp prevCap prevPtr
    (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (x.model C S uuidTryParse ans).1
    w0 w1 w2 w3 w4 F R' hres1) hmf_a1
  refine ⟨sf, hsteps, Or.inl ⟨st_b1, hsb1, hpc2, hmeta2, ans, hpan, hscope, ?_, ?_, ?_, ?_⟩⟩
  · rwa [rep_callsRel_eq]
  · rwa [rep_idCallsRel_eq]
  · rw [htr2, htr]; exact congrArg (s0.trace ++ ·) (rep_traceOfWith_eq _ _ _ _ _).symm
  · rw [hx28_2, hx20_2, hx21_2, ← hsp]
    dsimp only [A1, kit1, ikit1, R', RustCliAllocBudget.atState] at hm_fin ⊢
    simpa only [rep_decStoreExtra_eq, rep_storeFinal_eq, rep_idFinal_eq, sepConj_assoc] using hm_fin

attribute [local semireducible] SepWP in
theorem segErrTeardownVX_placed_ok [LibsignalPlacement] {M : AllocCostModel}
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
    (x : DecryptGhost) (st_init : M.σ) (pt : Bool) (R : SepProp) (s0 s : State)
    (hstB : ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init pt R s0 s) :
    DecSegVXPlaced C A lim ctl uuidTryParse S tdEnv encRecord H
      kit kitEnv ikit ikitEnv st0 ist0 Scope Extra x st_init R s0 s
      (fun s' => ResultFinalStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s') := by
  cases pt with
  | false => exact segErrTeardownVX_false_placed hyps hdrop2 hstB
  | true =>
    intro hL
    rcases hstB with ⟨st_b, hsb, hst⟩
    rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, htr, hm⟩
    rw [rep_callsRel_eq] at hcalls
    rw [rep_idCallsRel_eq] at hid_calls
    rw [rep_traceOfWith_eq] at htr
    have hmeta0 := hmeta
    rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hcrl, _hvregs⟩
    have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
    let A0 := A.atState lim st_b s
    let kit0 := retagSessionStore (A' := A0) kit
    let ikit0 := retagIdentityStore (A' := A0) ikit
    rw [← hsp] at hx26 hm
    simp only [↓reduceIte] at hm
    let R' : SepProp :=
      decStoreExtraPlaced kit ikit
        (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
        (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
    have hm_r' : s.mem ⊨ wsFixedVPlaced kit0 ikit0 x s0 s.sp ∗ wsEnvPlaced A0 x s.sp ∗ wsMsgCells x s.sp ∗
        droppableRecordAt A0 (s.sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), CryptoVerification.RustHeap.vecU8 A0 (s.sp + 0x290#64) p) ∗
        StagedRes A0 (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
          (x.model C S uuidTryParse ans).1 ∗
        memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
        memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
      dsimp only [A0, kit0, ikit0, R', RustCliAllocBudget.atState] at hm ⊢
      simpa only [rep_decStoreExtra_eq, rep_storeFinal_eq, rep_idFinal_eq, sepConj_assoc] using hm
    have hm_pre := Satisfies.mono (ej_true_expose_placed C A0 ctl kit0 ikit0 x ans s0 s.sp cs _ _ _ _ R') hm_r'
    simp only [satisfies_sepExists] at hm_pre
    rcases hm_pre with ⟨cap, ptr, len, hm_pre⟩
    have hm_pre' : s.mem ⊨
        (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗ ((s.sp + 0x2a0#64) ↦₆₄ len) ∗
          (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
          A.pool lim st_b s ∗ stackAt s.sp wsCalleeStack) ∗
        (ptFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') := by
      unfold ptPre at hm_pre
      dsimp only [A0, RustCliAllocBudget.atState] at hm_pre
      exact hm_pre
    obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ :=
      teardown_pt_placed_ok (st_b := st_b) (cap := cap) (ptr := ptr) (len := len)
        (R := ptFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R')
        hyps.hooks.dealloc hpc hrun hsp_align
        (ptFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') hm_pre' hL
    rotate_left
    · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
    obtain ⟨hm1', hsp1, htr1, hx28_1, hx20_1, hx21_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨evs_pt, hm1'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1'
    rcases hm1' with ⟨hevs_pt, hm1'⟩
    have hsb1 := seamBudget_advance_freeOnly hsb hevs_pt
    let st_b1 := M.stepEvents evs_pt st_b
    let A1 := A.atState lim st_b1 s1
    let kit1 := retagSessionStore (A' := A1) kit
    let ikit1 := retagIdentityStore (A' := A1) ikit
    have hm1_a1 : s1.mem ⊨
        ptPost A1 s.sp cap ptr len ∗
          (ptFramePlaced C A1 ctl kit1 ikit1 x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
            (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') := by
      unfold ptPost
      dsimp only [A0, A1, kit0, ikit0, kit1, ikit1, st_b1, RustCliAllocBudget.atState] at hm1' ⊢
      rwa [rep_ptFrame_eq (P1 := A.pool lim st_b s) (P2 := A.pool lim st_b1 s1)] at hm1'
    have hmeta1 := wsMetaPlaced_of_steps hmeta hsteps1 hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hm1_f := Satisfies.mono
      (pt_post_entails_placed C A1 ctl kit1 ikit1 x ans s0 s.sp cs _ _ _ _ R' cap ptr len) hm1_a1
    have hstB1 : ErrJoinStateVPlaced C A lim ctl uuidTryParse S tdEnv encRecord
        kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init false R s0 s1 := by
      refine ⟨st_b1, hsb1, hpc1, hmeta1, ?_, ?_, ans, cs, hpan, hnok, hscope, ?_, ?_, ?_, ?_⟩
      · rw [hx26_1, hx26, hsp]
      · rw [hx28_1]; exact hx28
      · rwa [rep_callsRel_eq]
      · rwa [rep_idCallsRel_eq]
      · rw [htr1, htr]; exact congrArg (s0.trace ++ ·) (rep_traceOfWith_eq _ _ _ _ _).symm
      · rw [hx28_1, hx20_1, hx21_1, ← hsp]
        dsimp only [A1, kit1, ikit1, R', RustCliAllocBudget.atState] at hm1_f ⊢
        simpa only [Bool.false_eq_true, ↓reduceIte, rep_decStoreExtra_eq, rep_storeFinal_eq, rep_idFinal_eq, sepConj_assoc] using hm1_f
    obtain ⟨s2, hsteps2, hout⟩ := segErrTeardownVX_false_placed hyps hdrop2 hstB1 (hsteps1.codeLoaded hL)
    exact ⟨s2, hsteps1.trans hsteps2, hout⟩

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegErrTeardownExtPlacedBudget
