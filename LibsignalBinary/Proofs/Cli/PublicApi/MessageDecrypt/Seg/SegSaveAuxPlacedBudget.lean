/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlaced
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import ProofLib
public meta import Lean
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Budget-Threaded `MessageDecrypt` Store Shims, Envelopes, and Seam Specifications

Defines allocation envelopes, budget-threaded store/identity shim and poll specifications, and
relocatable seam/segment predicates for `session_message_decrypt_signal_with_stores` on `lsProg_463`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification
open LibsignalBinary.Heap LibsignalBinary.Proofs.Placed.BudgetPoolSync LibsignalBinary.Proofs.Placed.BudgetVmSteps
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (
  stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err
  stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro
  shim_463 box_lscro_463 futDrop_463 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro
  clearLscroInvHyps wsMetaPlaced_of_steps)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem false_onPanic_entails {F Q : SepProp} : ⌜False⌝ ∗ F ⊢ Q :=
  Entails.pure_left False.elim

open Lean Elab Tactic in
scoped elab "cli_messageDecrypt_call_panic_budget_lscro " hcall:term:max hcrl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlId := mkIdent `hcrl_poll
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_lscro $hcall $hcrl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "cli_messageDecrypt_call_panic_lscro: unexpected subgoals"
  let gPre ← clearLscroInvHyps gPre
  let gPanic ← clearLscroInvHyps gPanic
  let gErr ← clearLscroInvHyps gErr
  let gOom ← clearLscroInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; first
      | exact false_onPanic_entails
      | exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId
  wpElimSpatialContext hspId

open Lean Elab Tactic in
scoped elab "cli_messageDecrypt_call_panic_p_budget_lscro " hcall:term:max hcrl:term:max a:term:max : tactic => do
  let sfId ← freshIdent `sf
  let hpcId ← freshIdent `hpc_sf
  let hrunId ← freshIdent `hrun_sf
  let hspId ← freshIdent `hsp_sf
  let hcsId ← freshIdent `hcs_sf
  let hcrlId ← freshIdent `hcrl_sf
  evalTactic (← `(tactic| (
    apply (sepWPp_call_panic_p_lscro $hcall $hcrl (x := $a))
    wp_focus_close (first | wp_norm_goal | wp_norm_lhs)
    wp_focus_close wp_norm_lhs
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
    wp_focus_close (first | wp_norm_lhs | wp_norm_goal)
  )))
  let gs ← getGoals
  let gPre :: gPanic :: gErr :: gOom :: gCont :: rest := gs
    | throwError "cli_messageDecrypt_call_panic_p_lscro: unexpected subgoals"
  let gPre ← clearLscroInvHyps gPre
  let gPanic ← clearLscroInvHyps gPanic
  let gErr ← clearLscroInvHyps gErr
  let gOom ← clearLscroInvHyps gOom
  setGoals [gPre]
  evalTactic (← `(tactic| intro _R' _hmR'))
  let ghostMVars ← etaExpandGoalProdMVarsWithNames
  evalTactic (← `(tactic| (
    wp_unfold_specs
    try dsimp only
    try simp (config := { decide := true }) only [
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
      satisfies_pure_sepConj, sepConj_assoc, wp_norm, arm64_norm] at _hmR' ⊢
  )))
  evalTactic (← `(tactic| repeat' (first | apply And.intro | arm64_instantiate_sep_exists)))
  wpDischargeCallSubgoalsCore ghostMVars none
  setGoals (gPanic :: gErr :: gOom :: gCont :: rest)
  evalTactic (← `(tactic| (
    wp_focus_close (wp_unfold_specs; intro _; first
      | exact false_onPanic_entails
      | exact shim_onPanic_entails (by first | wp_norm_lhs | simp_all [wp_norm, arm64_norm]))
    wp_focus_close (wp_unfold_specs; intro _ _; rfl)
    wp_focus_close (wp_unfold_specs; intro _; rfl)
    intro $sfId:ident $hpcId:ident $hrunId:ident $hspId:ident $hcsId:ident $hcrlId:ident
  )))
  foldStructEtaTarget
  wpNormAndSplitHyp hspId
  wpNormAndSplitHyp hcsId


namespace TempTwins
/-! ## Budget-threaded callee contracts, envelopes, and seam specifications -/

def SeamBudget {M : AllocCostModel} (lim : BudgetLimits) (TopEnv : List AllocEvent → Prop)
    (st_init st : M.σ) (RemEnv : List AllocEvent → Prop) : Prop :=
  FitsEnv M lim st RemEnv ∧ ∃ evs_pre : List AllocEvent,
    st = M.stepEvents evs_pre st_init ∧ ∀ evs_rem, RemEnv evs_rem → TopEnv (evs_pre ++ evs_rem)

theorem SeamBudget.init {M : AllocCostModel} {lim : BudgetLimits} {TopEnv : List AllocEvent → Prop}
    {st_init : M.σ} (h : FitsEnv M lim st_init TopEnv) : SeamBudget lim TopEnv st_init st_init TopEnv :=
  ⟨h, [], rfl, fun _ hr => hr⟩

theorem SeamBudget.narrow {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv RemEnv RemEnv' : List AllocEvent → Prop} {st_init st : M.σ}
    (h : SeamBudget lim TopEnv st_init st RemEnv) (himp : ∀ evs, RemEnv' evs → RemEnv evs) :
    SeamBudget lim TopEnv st_init st RemEnv' := by
  rcases h with ⟨hfits, evs_pre, hst, htop⟩
  exact ⟨fun evs hr => hfits evs (himp evs hr), evs_pre, hst, fun evs hr => htop evs (himp evs hr)⟩

theorem SeamBudget.advance {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv StepEnv NextEnv : List AllocEvent → Prop} {st_init st : M.σ} {evs_step : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st (SeqEnv StepEnv NextEnv)) (hstep : StepEnv evs_step) :
    SeamBudget lim TopEnv st_init (M.stepEvents evs_step st) NextEnv := by
  rcases h with ⟨hfits, evs_pre, hst, htop⟩
  refine ⟨hfits.seq_right hstep, evs_pre ++ evs_step, by rw [M.stepEvents_append, ← hst], fun evs_rem hnext => ?_⟩
  rw [List.append_assoc]; exact htop (evs_step ++ evs_rem) (SeqEnv.append hstep hnext)

theorem SeamBudget.advance_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv : List AllocEvent → Prop} {st_init st : M.σ} {evs_step : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st FreeOnlyEvs) (hstep : FreeOnlyEvs evs_step) :
    SeamBudget lim TopEnv st_init (M.stepEvents evs_step st) FreeOnlyEvs :=
  SeamBudget.advance (StepEnv := FreeOnlyEvs)
    (h.narrow fun _ h' => h'.elim id fun ⟨_, _, heq, h1, h2⟩ => heq ▸ FreeOnlyEvs.append h1 h2) hstep

theorem SeamBudget.finish {M : AllocCostModel} {lim : BudgetLimits} {TopEnv RemEnv : List AllocEvent → Prop}
    {st_init st : M.σ} {evs_end : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st RemEnv) (hend : RemEnv evs_end) :
    ∃ evs_tot : List AllocEvent, TopEnv evs_tot ∧ M.stepEvents evs_end st = M.stepEvents evs_tot st_init := by
  rcases h with ⟨_, evs_pre, hst, htop⟩
  exact ⟨evs_pre ++ evs_end, htop evs_end hend, by rw [M.stepEvents_append, ← hst]⟩

theorem freeOnlyEvs_rustDeallocEvents (sz al : Nat) : FreeOnlyEvs (rustDeallocEvents sz al) :=
  FreeOnlyEvs.singleton al sz

abbrev retagSessionStore {A A' : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : SessionStoreSpec A' b := { kit with }
abbrev retagIdentityStore {A A' : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : IdentityStoreSpec A' b := { ikit with }

def BoxAllocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  (boxSize = 0 ∧ evs = []) ∨ (0 < boxSize ∧ evs = rustAllocEvents boxSize 8)

def BoxDeallocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  (boxSize = 0 ∧ evs = []) ∨ (0 < boxSize ∧ evs = rustDeallocEvents boxSize 8)

theorem BoxDeallocEnv.freeOnly {boxSize : Nat} {evs : List AllocEvent} (h : BoxDeallocEnv boxSize evs) : FreeOnlyEvs evs := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact FreeOnlyEvs.nil
  · exact freeOnlyEvs_rustDeallocEvents boxSize 8

def StringCloneEnv (g : VecGhost) (evs : List AllocEvent) : Prop :=
  (g.bytes.length = 0 ∧ evs = []) ∨ (0 < g.bytes.length ∧ evs = rustAllocEvents g.bytes.length 1)

def DecBoundedRustEvs (maxCount maxReq : Nat) (evs : List AllocEvent) : Prop :=
  evs.length ≤ maxCount ∧
  ∀ ev ∈ evs,
    ev.withinMaxAlloc ∧
    ev.reqBytes ≤ maxReq ∧
    (∀ al r, ev = .aligned al r → al ≤ 16) ∧
    (∀ al o n, ev = .realloc al o n → al ≤ 16)

def RecordDecryptCoreEnv (_C : Crypto) (_S : SpqrModel) (_uuidParse : UuidParser)
    (ses_st : SessionState (List (BitVec 8))) (_msg : SignalMessage)
    (_loc _rem : AddrGhost) (rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  SeqEnv
    (DecBoundedRustEvs 64 (2 * (rest.length + ses_st.pqRatchetState.length + 1024)))
    FreeOnlyEvs evs

def RecordDecryptEnv (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) (x : RecordDecryptGhost) (evs : List AllocEvent) : Prop :=
  RecordDecryptCoreEnv C S uuidParse x.st x.msg x.loc x.rem x.rest evs

structure SessionStoreBudgetEnv {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) where
  loadPollEnv : kit.StoreState → AddrVal → List AllocEvent → Prop
  storePollEnv : kit.StoreState → AddrVal → SessionRecord (List (BitVec 8)) → List AllocEvent → Prop

structure IdentityStoreBudgetEnv {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) where
  trustPollEnv : ikit.IdState → AddrVal → IdentityKey → Direction → List AllocEvent → Prop
  savePollEnv : ikit.IdState → AddrVal → IdentityKey → List AllocEvent → Prop

/-- Budget-threaded `<String as Clone>::clone` contract. -/
def stringCloneBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × VecGhost × M.σ) where
  pre := fun (p, ret, g, st) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧ FitsEnv M lim st (StringCloneEnv g)⌝ ∗
      vecGhostAt A.repAlloc g p ∗ memRegion ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (p, ret, g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ StringCloneEnv g evs⌝ ∗
      vecGhostAt A.repAlloc g p ∗ vecU8 A.repAlloc ret g.bytes ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-- Budget-threaded no-op future drop contract (zero allocations, preserves VM state). -/
def futDropBudgetSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝

/-- Budget-threaded `load_session` shim contract. -/
def kitLoadShimBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SessionStoreSpec A.repAlloc b) :
    Spec (LoadShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧
      FitsEnv M lim st (BoxAllocEnv kit.loadBoxSize)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp kit.loadShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.readReg64 .x1 = b + kit.loadFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
        BoxAllocEnv kit.loadBoxSize evs⌝ ∗
      A.live (sf.readReg64 .x0) kit.loadBoxSize 8 ∗
      kit.loadBoxAt (sf.readReg64 .x0) x.self x.addrA 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.loadShimStack

/-- Budget-threaded `store_session` shim contract. -/
def kitStoreShimBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (kit : SessionStoreSpec A.repAlloc b) :
    Spec (StoreShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.recA ∧
      FitsEnv M lim st (BoxAllocEnv kit.storeBoxSize)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp kit.storeShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.readReg64 .x1 = b + kit.storeFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧
        BoxAllocEnv kit.storeBoxSize evs⌝ ∗
      A.live (sf.readReg64 .x0) kit.storeBoxSize 8 ∗
      kit.storeBoxAt (sf.readReg64 .x0) x.self x.addrA x.recA 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.storeShimStack

def kitLoadPollBudgetSpecS (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (LoadPollCall × BitVec 64 × kit.StoreState × M.σ) where
  pre := fun (x, self, st0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ kit.addrOk x.addr.val ∧ FitsEnv M lim st (kitEnv.loadPollEnv st0 x.addr.val)⌝ ∗
      kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st0 ∗ memRegion x.out 368 ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗ A.pool lim st s ∗ stackAt s.sp kit.loadPollStack
  post := fun (x, self, st0, st) s0 sf =>
    ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))), ∃∗ evs : List AllocEvent,
      ⌜kit.loadRel st0 x.addr.val ans ∧ sf.trace = s0.trace ++ kit.loadEvs encRecord x.addr.val ans ∧ kitEnv.loadPollEnv st0 x.addr.val evs⌝ ∗
      kit.loadBoxAt x.fut self x.addrA 1#8 ∗ kit.storeAt self st0 ∗ loadPollPlacedOutAtS Scope A.repAlloc x.out ans ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.loadPollStack

abbrev kitLoadPollBudgetSpecSE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :=
  withEnvPre (kitLoadPollBudgetSpecS M A lim kit kitEnv Scope encRecord) fun s => kit.envOk s.fs.files

def kitStorePollBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (StorePollCall × BitVec 64 × kit.StoreState × M.σ) where
  pre := fun (x, self, st0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ kit.RecOk x.call.record ∧ kit.addrOk x.call.addr.val ∧
      FitsEnv M lim st (kitEnv.storePollEnv st0 x.call.addr.val x.call.record)⌝ ∗
      kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗ kit.storeAt self st0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗ sessionRecordAt A.repAlloc x.call.recA x.call.g x.call.record ∗
      A.pool lim st s ∗ stackAt s.sp kit.storePollStack
  post := fun (x, self, st0, st) s0 sf =>
    ∃∗ ans : Except Unit Unit, ∃∗ evs : List AllocEvent,
      ⌜kit.storeRel st0 x.call.addr.val x.call.record ans ∧ sf.trace = s0.trace ++ kit.storeEvs encRecord x.call.addr.val x.call.record ans ∧
        kitEnv.storePollEnv st0 x.call.addr.val x.call.record evs⌝ ∗
      kit.storeBoxAt x.fut self x.call.addrA x.call.recA 1#8 ∗ kit.storeAt self (kit.storeUpdate st0 x.call.addr.val x.call.record ans) ∗
      storePollPlacedOutAt x.out ans ∗ protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      sessionRecordAt A.repAlloc x.call.recA x.call.g x.call.record ∗ A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kit.storePollStack

abbrev kitStorePollBudgetSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :=
  withEnvPre (kitStorePollBudgetSpec M A lim kit kitEnv encRecord) fun s => kit.envOk s.fs.files

def kitTrustShimBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b) : Spec (IdentityShimCall × BitVec 8 × M.σ) where
  pre := fun (x, d, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧
      (s.readReg64 .x3).setWidth 8 = d ∧ FitsEnv M lim st (BoxAllocEnv ikit.trustBoxSize)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp ikit.trustShimStack
  post := fun (x, d, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.readReg64 .x1 = b + ikit.trustFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧ BoxAllocEnv ikit.trustBoxSize evs⌝ ∗
      A.live (sf.readReg64 .x0) ikit.trustBoxSize 8 ∗ ikit.trustBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 d ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.trustShimStack

def kitSaveShimBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {b : BitVec 64} (ikit : IdentityStoreSpec A.repAlloc b) : Spec (IdentityShimCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x1 = x.addrA ∧ s.readReg64 .x2 = x.keyA ∧ FitsEnv M lim st (BoxAllocEnv ikit.saveBoxSize)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp ikit.saveShimStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.readReg64 .x1 = b + ikit.saveFutVtOff ∧ sf.readReg64 .x0 ≠ 0#64 ∧
        (sf.readReg64 .x0).toNat % 8 = 0 ∧ sf.trace = s0.trace ∧ BoxAllocEnv ikit.saveBoxSize evs⌝ ∗
      A.live (sf.readReg64 .x0) ikit.saveBoxSize 8 ∗ ikit.saveBoxAt (sf.readReg64 .x0) x.self x.addrA x.keyA 0#8 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.saveShimStack

def kitTrustPollBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState × M.σ) where
  pre := fun (x, d, self, ist0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val ∧
      FitsEnv M lim st (ikitEnv.trustPollEnv ist0 x.call.addr.val x.call.key d)⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗ ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗ (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim st s ∗ stackAt s.sp ikit.trustPollStack
  post := fun (x, d, self, ist0, st) s0 sf =>
    ∃∗ ans : Except Unit Bool, ∃∗ evs : List AllocEvent,
      ⌜ikit.trustRel ist0 x.call.addr.val x.call.key d ans ∧ sf.trace = s0.trace ++ ikit.trustEvs x.call.addr.val x.call.key d ans ∧
        ikitEnv.trustPollEnv ist0 x.call.addr.val x.call.key d evs⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
      ikit.identityAt self (ikit.trustUpdate ist0 x.call.addr.val x.call.key d ans) ∗ trustPollPlacedOutAt x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗ (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp ikit.trustPollStack

abbrev kitTrustPollBudgetSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :=
  withEnvPre (kitTrustPollBudgetSpec M A lim ikit ikitEnv) fun s => ikit.envOk s.fs.files

abbrev kitTrustPollBudgetSpecI [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :=
  withLsLogOff (kitTrustPollBudgetSpecE M A lim ikit ikitEnv)

/-- Budget-threaded relocatable `save_identity` poll contract. -/
def kitSavePollBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) where
  pre := fun (x, self, ist0, st) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val ∧
      FitsEnv M lim st (ikitEnv.savePollEnv ist0 x.call.addr.val x.call.key)⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool lim st s ∗
      stackAt s.sp ikit.savePollStack
  post := fun (x, self, ist0, st) s0 sf =>
    ∃∗ ans : Except Unit IdentityChange, ∃∗ evs : List AllocEvent,
      ⌜ikit.saveRel ist0 x.call.addr.val x.call.key ans ∧
        sf.trace = s0.trace ++ ikit.saveEvs x.call.addr.val x.call.key ans ∧
        ikitEnv.savePollEnv ist0 x.call.addr.val x.call.key evs⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
      ikit.identityAt self (ikit.saveUpdate ist0 x.call.addr.val x.call.key ans) ∗
      savePollPlacedOutAt x.out ans ∗
      protocolAddressAt A.repAlloc x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp ikit.savePollStack

abbrev kitSavePollBudgetSpecE (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) :=
  withEnvPre (kitSavePollBudgetSpec M A lim ikit ikitEnv) fun s => ikit.envOk s.fs.files

abbrev kitSavePollBudgetSpecI [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (ikitEnv : IdentityStoreBudgetEnv ikit) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState × M.σ) :=
  withLsLogOff (kitSavePollBudgetSpecE M A lim ikit ikitEnv)

structure SessionOnlyKitBudgetOkSE [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks) : Prop where
  loadShim : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + kit.loadShimOff) (withLsRoCl lsmpl (kitLoadShimBudgetSpec M A lim kit))
  loadPoll : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + kit.loadPollOff) (withLsRoCl lsmpl (kitLoadPollBudgetSpecSE M A lim kit kitEnv Scope encRecord))
  loadFutDrop : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + kit.loadFutDropOff) (withLsRoCl lsmpl futDropBudgetSpec)
  storeShim : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + kit.storeShimOff) (withLsRoCl lsmpl (kitStoreShimBudgetSpec M A lim kit))
  storePoll : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + kit.storePollOff) (withLsRoCl lsmpl (kitStorePollBudgetSpecE M A lim kit kitEnv encRecord))
  storeFutDrop : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + kit.storeFutDropOff) (withLsRoCl lsmpl futDropBudgetSpec)

structure IdentityStoreKitBudgetOkI [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (H : LibsignalHooks) : Prop where
  trustShim : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + ikit.trustShimOff) (withLsRoCl lsmpl (kitTrustShimBudgetSpec M A lim ikit))
  trustPoll : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + ikit.trustPollOff) (withLsRoCl lsmpl (kitTrustPollBudgetSpecI M A lim ikit ikitEnv))
  trustFutDrop : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + ikit.trustFutDropOff) (withLsRoCl lsmpl futDropBudgetSpec)
  saveShim : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + ikit.saveShimOff) (withLsRoCl lsmpl (kitSaveShimBudgetSpec M A lim ikit))
  savePoll : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + ikit.savePollOff) (withLsRoCl lsmpl (kitSavePollBudgetSpecI M A lim ikit ikitEnv))
  saveFutDrop : ∀ {p : Program} {i : Nat} [IsLsBlockProg p i H], i < 619 →
    subroutine_ok p (0#64 + ikit.saveFutDropOff) (withLsRoCl lsmpl futDropBudgetSpec)

def remoteIdentityKeyBudgetSpec [LibsignalPlacement] (A : RustAlloc) :
    Spec Getters.RemoteIdentityKeyGhost :=
  let base := Getters.remoteIdentityKeyPlacedSpec A
  { base with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ base.post x s0 sf }

abbrev RemoteIdentityKeyBudgetOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_463 H) (lsmpl.base 29)
    (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyBudgetSpec A))

def dropSessionStructureLocal2BudgetSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FromRecordCallees.DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗ A.pool lim st s ∗
      stackAt s.sp FromRecordCallees.dropSessionStructureLocal2Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp FromRecordCallees.dropSessionStructureLocal2Stack

abbrev DropSessionStructureLocal2BudgetOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_463 H) (lsmpl.base 442)
    (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec A lim))

def recordDecryptBudgetSpec [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec (RecordDecryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (RecordDecryptEnv C S uuidParse x)⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C
        (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ⌜RecordDecryptEnv C S uuidParse x evs⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C
        (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S.recvPanics x.st.pqRatchetState x.msg.pqRatchet)) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

def sessionShimBudgetSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝

def sessionMemcpyRegionBudgetSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := memcpyRegionSpec.pre
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

structure PublicApiDecHooksBudget [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec
  alloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)
  memcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec
  stringClone : HookSat H lsStringCloneSym (stringCloneBudgetSpec M A lim)
  handleError : H lsHandleErrorSym = some Rust.panicked
  expectFailed : H lsExpectFailedSym = some Rust.panicked

structure DecHypsVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (ss : SessionStoreSpec A.repAlloc 0#64) (ssEnv : SessionStoreBudgetEnv ss)
    (id : IdentityStoreSpec A.repAlloc 0#64) (idEnv : IdentityStoreBudgetEnv id)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  hooks : PublicApiDecHooksBudget A lim H
  kit : SessionOnlyKitBudgetOkSE A lim ss ssEnv Scope encRecord H
  ikit : IdentityStoreKitBudgetOkI A lim id idEnv H
  scopeIn : ∀ r, Scope r → RecordInScope r
  recOk : DecModelRecOk ss C S parse Scope

def LoadStepEnv {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState) (rem : AddrVal) :=
  SeqEnv (BoxAllocEnv kit.loadBoxSize) (kitEnv.loadPollEnv st0 rem)

def StoreStepEnv {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (rem : AddrVal) (rec' : SessionRecord (List (BitVec 8))) :=
  SeqEnv (BoxAllocEnv kit.storeBoxSize)
    (SeqEnv (kitEnv.storePollEnv st0 rem rec') (BoxDeallocEnv kit.storeBoxSize))

def TrustStepEnvDec {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState) (rem : AddrVal) (k : IdentityKey) :=
  SeqEnv (BoxAllocEnv ikit.trustBoxSize)
    (SeqEnv (ikitEnv.trustPollEnv ist0 rem k .receiving) (BoxDeallocEnv ikit.trustBoxSize))

def SaveStepEnvDec {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (ikitEnv : IdentityStoreBudgetEnv ikit) (ist1 : ikit.IdState) (rem : AddrVal) (k : IdentityKey) :=
  SeqEnv (BoxAllocEnv ikit.saveBoxSize)
    (SeqEnv (ikitEnv.savePollEnv ist1 rem k) (BoxDeallocEnv ikit.saveBoxSize))

def FromStoreCallEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (rem : AddrVal) (rec' : SessionRecord (List (BitVec 8))) :=
  SeqEnv (StoreStepEnv kit kitEnv st0 rem rec') FreeOnlyEvs

def FromTrustedFalseEnv (x : DecryptGhost) : List AllocEvent → Prop :=
  SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs

def FromTrustedTrueEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : DecryptGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (SaveStepEnvDec ikit ikitEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k)
    (fun evs => FreeOnlyEvs evs ∨ FromStoreCallEnv kit kitEnv st0 x.rem.val rec' evs)

def FromTrustedEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : DecryptGhost) (t : Bool)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  if t then FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k else FromTrustedFalseEnv x

def FromKeyReadyEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : DecryptGhost)
    (rec' : SessionRecord (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (TrustStepEnvDec ikit ikitEnv ist0 x.rem.val k)
    (fun evs => FreeOnlyEvs evs ∨ FromTrustedFalseEnv x evs ∨
      FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs)

def FromPostSomeEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ ∃ pt rec' ses k, decryptRecord C S parse x rec = .ok (pt, rec') ∧
    rec'.currentSession = some ses ∧ ses.state.remoteIdentity = some k ∧
    FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs

def FromRegionSomeEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8))) (ses_st : SessionState (List (BitVec 8))) :=
  SeqEnv (RecordDecryptCoreEnv C S parse ses_st x.msg x.loc x.rem x.rest)
    (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec)

def FromRegionNoneEnv : List AllocEvent → Prop :=
  SeqEnv (· = rustAllocEvents 17 1) FreeOnlyEvs

def FromLoadPolledEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) : List AllocEvent → Prop :=
  SeqEnv (BoxDeallocEnv kit.loadBoxSize)
    (fun evs => FreeOnlyEvs evs ∨ SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
      FromRegionNoneEnv evs ∨ ∃ rec ses, kit.ScopeAt Scope st0 x.rem.val rec ∧
        rec.currentSession = some ses ∧
        FromRegionSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec ses.state evs)

/-- End-to-end allocation envelope for `session_message_decrypt_signal_with_stores`. -/
def WithStoresDecEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) : List AllocEvent → Prop :=
  SeqEnv (LoadStepEnv kit kitEnv st0 x.rem.val)
    (FromLoadPolledEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 Scope x)

def withStoresDecBudgetSpecV [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) where
  pre := fun (x, st_init) s =>
    ⌜FitsEnv M lim st_init (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x)⌝ ∗
      (withStoresDecPlacedSpecV C (A.atState lim st_init s) ctl parse S encRecord (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 Scope).pre x s
  post := fun (x, st_init) s0 sf =>
    ∃∗ evs : List AllocEvent, ⌜WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x evs⌝ ∗
      (withStoresDecPlacedSpecV C (A.atState lim (M.stepEvents evs st_init) sf) ctl parse S encRecord (retagSessionStore kit) (retagIdentityStore ikit) st0 ist0 Scope).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜s0.trace <+: sf.trace ∧ (∃ answers : StoreAnswers (List (BitVec 8)) Unit, kit.loadRel st0 x.rem.val answers.loadSession ∧
      s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
      ((x.model C S parse answers).1 = .error .panic ∨ x.recvPanics S answers))⌝ ∗ anyHeap

def DecSegVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 s : State) (Out : State → Prop) : Prop :=
  (lsProg_463 H).CodeLoaded s.mem → ∃ s', Steps (lsProg_463 H) s s' ∧
    (Out s' ∨ SubroutineOutcome (withStoresDecBudgetSpecV C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 s')

def LoadPolledStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st (FromLoadPolledEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 Scope x) ∧
    LoadPolledStateVPlaced ctl encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans R s0 s

def RegionSomeStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, (∀ rec ses, ans.loadSession = .ok (some rec) → rec.currentSession = some ses →
      SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st (FromRegionSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec ses.state)) ∧
    RegionSomeStateVPlaced C ctl parse S encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans R s0 s

def RegionNoneStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st FromRegionNoneEnv ∧
    RegionNoneStateVPlaced ctl encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans R s0 s

def PostSomeStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, (∀ rec, ans.loadSession = .ok (some rec) →
      SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec)) ∧
    PostSomeStateVPlaced C ctl parse S encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans R s0 s

def PostNoneStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st FreeOnlyEvs ∧
    PostNoneStateVPlaced ctl encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans R s0 s

def KeyReadyStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, (∀ rec rec' pt ses k, ans.loadSession = .ok (some rec) → decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses → ses.state.remoteIdentity = some k →
      SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st (FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)) ∧
    KeyReadyStateVPlaced C ctl parse S encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans R s0 s

def TrustedStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, (∀ rec rec' pt ses k, ans.loadSession = .ok (some rec) → decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses → ses.state.remoteIdentity = some k →
      SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st (FromTrustedEnv kit kitEnv st0 ikit ikitEnv ist0 x t rec' k)) ∧
    TrustedStateVPlaced C ctl parse S encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans t R s0 s

def StoreCallStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, (∀ rec pt rec', ans.loadSession = .ok (some rec) → decryptRecord C S parse x rec = .ok (pt, rec') →
      SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st (FromStoreCallEnv kit kitEnv st0 x.rem.val rec')) ∧
    StoreCallStateVPlaced C ctl parse S encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x ans R s0 s

def ErrJoinStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (pt : Bool) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st FreeOnlyEvs ∧
    ErrJoinStateVPlaced C ctl parse S encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x pt R s0 s

def ResultFinalStateVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 s : State) : Prop :=
  ∃ st : M.σ, SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse Scope x) st_init st FreeOnlyEvs ∧
    ResultFinalStateVPlaced C ctl parse S encRecord (retagSessionStore (A' := A.atState lim st s) kit) (retagIdentityStore (A' := A.atState lim st s) ikit) st0 ist0 Scope x R s0 s

def SegLoadSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
    DecFsCtxPlaced kit ikit H s0 s0 → s0.pc = wsEntryPCPlaced → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (withStoresDecBudgetSpecV C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope).pre (x, st_init) s0 ∗ R) →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s0
      (fun s' => ∃ ans, LoadPolledStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s')

def SegDispatchSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    LoadPolledStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => RegionSomeStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s' ∨
        RegionNoneStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s' ∨
        ResultFinalStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s')

def SegRegionSomeSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope → ∀ (Q : List (BitVec 8) → Prop),
  region_ok (lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
    ((recordDecryptBudgetSpec C A lim ctl uuidTryParse S).withVRegs.restrictPre (fun p => Q p.1.st.pqRatchetState)) →
  ScopePq kit st0 Scope Q → ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionSomeStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => PostSomeStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s')

def SegRegionNoneSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionNoneStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => PostNoneStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s')

def SegPostSomeSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope → RemoteIdentityKeyBudgetOk A.repAlloc H →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostSomeStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => KeyReadyStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s' ∨
        ErrJoinStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init false R s0 s')

def SegPostNoneSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostNoneStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => ErrJoinStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init false R s0 s')

def SegTrustSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val → DecFsCtxPlaced kit ikit H s0 s →
    KeyReadyStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => (∃ ans' t, TrustedStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans' t R s0 s') ∨
        ErrJoinStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s')

def SegUntrustedSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    TrustedStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans false R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => ErrJoinStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s')

def SegSaveSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val → DecFsCtxPlaced kit ikit H s0 s →
    TrustedStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans true R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => (∃ ans', StoreCallStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans' R s0 s') ∨
        ErrJoinStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s')

def SegStoreSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope → DropSessionStructureLocal2BudgetOk A lim H →
  ∀ (x : DecryptGhost) (st_init : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    kit.addrOk x.rem.val → DecFsCtxPlaced kit ikit H s0 s →
    StoreCallStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init ans R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => ResultFinalStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s' ∨
        ErrJoinStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init true R s0 s')

def SegErrTeardownSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope → DropSessionStructureLocal2BudgetOk A lim H →
  ∀ (x : DecryptGhost) (st_init : M.σ) (pt : Bool) (R : SepProp) (s0 s : State),
    ErrJoinStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init pt R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => ResultFinalStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s')

def SegWriteSpecVBudget [LibsignalPlacement] {M : AllocCostModel} (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (H : LibsignalHooks)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVBudget C A lim parse S encRecord H kit kitEnv ikit ikitEnv Scope →
  ∀ (x : DecryptGhost) (st_init : M.σ) (R : SepProp) (s0 s : State),
    ResultFinalStateVBudget C A lim ctl parse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s →
    DecSegVBudget C A lim ctl parse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s (fun _ => False)

end TempTwins

open TempTwins

theorem futDropBudget_463 [LibsignalPlacement] {H : LibsignalHooks} {off : BitVec 64}
    (h : subroutine_ok (lsProg_463 H) (0#64 + off) (StoreKit.withLsRoCl lsmpl futDropBudgetSpec)) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) off (StoreKit.withLsCodeRoLoaded lsmpl futDropBudgetSpec) := by
  rw [BitVec.zero_add] at h
  exact StoreKit.subroutine_ok_withLsCodeRoLoaded_of_rocl h

theorem deallocBudget_463 [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hsat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsρ lsRustDeallocSym)
      (rustCliDeallocBudgetExternSpecWithStack M A lim allocHookStack) :=
  IfaceBudgetLemmas.subroutine_ok_deallocBudget_externWithStack_of_hookSat (stk := allocHookStack) hsat
    (ls_externAt?_of_mem (prog := (blkPC_463).rebase (blkPl_463).base H) (i := 463) (sym := lsRustDeallocSym) (by decide))

theorem allocNoOom_463 [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hsat : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsρ lsRustAllocSym)
      (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
  IfaceBudgetLemmas.subroutine_ok_allocNoOom_externWithStack_of_hookSat (stk := allocHookStack) hsat
    (ls_externAt?_of_mem (prog := (blkPC_463).rebase (blkPl_463).base H) (i := 463) (sym := lsRustAllocSym) (by decide))

theorem sepWP_with_vm {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (h : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) mid s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧ (VmPreserved s sm → post sm Pm))) :
    SepWP (P.rebase b Hk) mid s Pre post :=
  SepWP.mono (sepWP_rebase_vmPreserved h) fun _ _ _ _ ⟨hvm, hp⟩ => hp hvm

scoped syntax "by_vm_open " tacticSeq : tactic
scoped elab_rules : tactic
  | `(tactic| by_vm_open $tac:tacticSeq) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_with_vm))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      unless rem.isEmpty do
        throwError "by_vm_open: inner tactic left {rem.length} unsolved goal(s)"
      Lean.Elab.Tactic.setGoals savedGoals.tail!
      let prf1 ← Lean.instantiateMVars g1
      let prf2 := prf1.replace fun sub =>
        if sub.eqv e2 then some e2 else if sub.eqv e1 then some e2 else none
      g.assign prf2

theorem atState_eq_of_vmPreserved {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {s sf : State} (hvm : VmPreserved s sf) :
    A.atState lim st s = A.atState lim st sf :=
  congrArg (fun p => ({ pool := p, live := A.live } : RustAlloc)) (A.pool_transport lim st s sf hvm).symm

theorem sepWP_cut_here {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => SepWP prog target sm Pm post)) :
    SepWP prog target s P post := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hs1, ⟨_, _, Pm, hPm, h2⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h1 hm hL
  · obtain ⟨sf, hs2, hout⟩ := SepWP.to_reaches_pc h2 hPm (hs1.codeLoaded hL)
    exact ⟨sf, hs1.trans hs2, hout⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem panic_outcome_of_decBudget [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State} (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (withStoresDecBudgetSpecV C A lim ctl uuidTryParse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope).onPanic (x, st_init) s0 sf ∗ R) :
    SubroutineOutcome (withStoresDecBudgetSpecV C A lim ctl uuidTryParse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope) (x, st_init) R s0 sf :=
  Or.inr (Or.inl ⟨hpan, hm⟩)

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
