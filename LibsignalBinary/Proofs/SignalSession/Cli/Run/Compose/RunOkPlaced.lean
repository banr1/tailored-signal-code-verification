/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOk
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureFrozenPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `signal_session::run` Meets `runSpecPlaced` at `runRel S`

Relocatable (`[LibsignalPlacement]`) counterpart of `RunOk.lean`, composing
`run_hop_dropSpeOwned_placed` and the nine arm hop contracts (`RunArmsPlaced` / `RunArmsFrozenPlaced`)
into `run_ok_placed`, `run_ok_frozen_placed`, and cross-block transfers from Block `579`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Arm64.Process
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.E2E.Record.Placed

/-- Bundle of the 9 relocatable (`[LibsignalPlacement]`) arm hop contracts of `signal_session::run`
(Block `579`). -/
structure RunArmsPlaced [LibsignalPlacement] (CodeOk : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop where
  join : RunHopJoinPlaced CodeOk A H B S needs resStack
  pre : RunHopPrePlaced CodeOk A H B S needs resStack
  init1 : RunHopInit1Placed CodeOk A H B S needs resStack
  init2 : RunHopInit2Placed CodeOk A H B S needs resStack
  init3 : RunHopInit3Placed CodeOk A H B S needs resStack
  send : RunHopSendPlaced CodeOk A H B S needs resStack
  recvW : RunHopRecvWPlaced CodeOk A H B S needs resStack
  recvP : RunHopRecvPPlaced CodeOk A H B S needs resStack
  recvBad : RunHopRecvBadPlaced CodeOk A H B S needs resStack

/-- `signal_session::run` (Block `579`) meets `runSpecPlaced` at `runRel S` under
`[LibsignalPlacement]`. -/
theorem run_ok_placed [LibsignalPlacement] {CodeOk : Memory → Prop} {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsPlaced CodeOk A H B S needs resStack)
    (hh : RunHooksPlaced A H)
    (hc : RunCalleesPlaced A H B (slotsOfPlaced A S needs))
    (hpksm : subroutine_ok (runProgPlaced H) (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced A S))
    (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (runSpecPlaced CodeOk A uuidTryParse (runRel S) cliWrOk resStack) := by
  apply subroutine_ok_of_sepWPp_init
  intro g R s0 hpc hrun hpre hsp
  have hspb : resStack ≤ s0.sp.toNat := by
    have hpre' := hpre
    simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    rcases hpre' with ⟨⟨_, _, _, _, _, _, _, _, _, _, hspb⟩, _⟩
    exact hspb
  rcases runEntry_of_placed_pre hpc hrun hpre hsp with ⟨he, hmem⟩
  refine ⟨runEntryMemPlaced A g s0 resStack, hmem, ?_⟩
  let Q : State → SepProp → Prop := fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlaced CodeOk A uuidTryParse (runRel S) cliWrOk resStack).post g s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
  let Qp : State → SepProp → Prop := fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlaced CodeOk A uuidTryParse (runRel S) cliWrOk resStack).onPanic g s0 sf ∗ R)
  have hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A :=
    run_hop_dropSpeOwned_placed hh.alloc
  have hpanic : PanicK g s0 Qp := fun _ _ hpan hmf =>
    placed_onPanic_of_runPanic (CodeOk := CodeOk) (S := S) (A := A) (resStack := resStack) hpan hmf
  have hpost_mono : ∀ {sf Pf}, runPostPlaced CodeOk A g resStack s0 sf Pf → Q sf Pf :=
    fun hp => ⟨fun hmf => (placed_post_of_runPost he.fs he.stdout hp hmf).1, hp.2.1, hp.2.2.1⟩
  have hjoin : JoinKPlaced CodeOk H A g s0 resStack Q Qp := fun s g' out hj =>
    sepWPp_mono_post (fun _ _ hp => hpost_mono hp)
      (harms.join hh hres hres64 (Or.inl ⟨g', out, hj, rfl⟩))
  have hrej : RejectKPlaced CodeOk H A g s0 resStack Q Qp := fun s g' rk hr =>
    sepWPp_mono_post (fun _ _ hp => hpost_mono hp)
      (harms.join hh hres hres64 (Or.inr ⟨g', rk, hr, rfl⟩))
  rw [placed_onOom_eq (CodeOk := CodeOk) (S := S) (A := A) g resStack s0]
  refine harms.pre hh hc hdrop hres hres64 he hpanic hrej fun s me hd => ?_
  cases hcall : g.c with
  | keygen meK nK =>
    have htag : g.c.tag ≠ 0 := runRel_not_keygen he.rel he.parse
    rw [hcall] at htag
    exact absurd rfl htag
  | send peerV =>
    exact harms.send hh hc hdrop hres hres64 hspb he hd hcall hpanic hrej hjoin
  | init peerV dir =>
    exact harms.init1 hh hc hdrop hres hres64 he hd hcall hpanic hrej fun s1 d1 hi1 =>
      harms.init2 hh hc hdrop hres hres64 he hi1 hpanic hrej fun s2 d2 hi2 =>
        harms.init3 hh hc hdrop hres hres64 hspb he hi2 hpanic hrej hjoin
  | recv peerV =>
    cases hstdin : g.i.stdin with
    | nil =>
      exact harms.recvBad hh hres hres64 he hd hcall (Or.inl hstdin) hrej
    | cons t rest =>
      by_cases ht2 : t = 2#8
      · subst ht2
        exact harms.recvW hh hc hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin
      · by_cases ht3 : t = 3#8
        · subst ht3
          exact harms.recvP hh hc hpksm hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin
        · exact harms.recvBad hh hres hres64 he hd hcall
            (Or.inr ⟨t, rest, hstdin, ht2, ht3⟩) hrej

/-- `signal_session::run` (Block `579`) meets `withLsCodeRoLoaded (runSpecPlaced ...)` under
`[LibsignalPlacement]`, enabling cross-block transfer via `ls_subroutine_ok_rocl_of_block`. -/
theorem run_ok_withLsCodeRoLoaded_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack)
    (hh : RunHooksPlaced A H)
    (hc : RunCalleesPlaced A H B (slotsOfPlaced A S needs))
    (hpksm : subroutine_ok (runProgPlaced H) (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced A S))
    (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (runSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          A uuidTryParse (runRel S) cliWrOk resStack)) := by
  refine subroutine_ok_mono (run_ok_placed harms hh hc hpksm hres hres64) ?_ (fun _ _ _ _ h => h)
  intro g R s0 hpre
  exact Satisfies.drop_mid (by
    simpa only [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, sepConj_assoc] using hpre)

/-- Cross-block transfer of `run_ok_withLsCodeRoLoaded_placed` from Block `579` (`runProgPlaced H`)
to any caller block `i < 619` (`callerProg`, e.g. Block `617` `mProgPlaced H`). -/
theorem run_ok_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    (harms : RunArmsPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
      A H B S needs resStack)
    (hh : RunHooksPlaced A H)
    (hc : RunCalleesPlaced A H B (slotsOfPlaced A S needs))
    (hpksm : subroutine_ok (runProgPlaced H) (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced A S))
    (hres : runNeed B (slotsOfPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 579)
      (runSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
        A uuidTryParse (runRel S) cliWrOk resStack) := by
  have h579 : IsLsBlockProg (runProgPlaced H) 579 H := inferInstance
  have hrocl := @LibsignalPublicApi.StoreKit.ls_subroutine_ok_rocl_of_block _ _ callerProg
    (runProgPlaced H) i 579 H hcaller h579 (lsmpl.base 579) _
    (run_ok_withLsCodeRoLoaded_placed harms hh hc hpksm hres hres64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl ?_ ?_
  · intro g R s0 hpre
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl]
    have hpre' := hpre
    simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    have hcomm :
        (runSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
          A uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗
          ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R =
        ⌜LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          ((runSpecPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl)
            A uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗ R) := by
      ac_rfl
    rw [sepConj_assoc, hcomm, satisfies_pure_sepConj]
    exact ⟨hpre'.1.1, hpre⟩
  · intro g R s0 sf hpost
    dsimp only [LibsignalPublicApi.StoreKit.withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

/-! ## Frozen (`LibsignalFrozen lsmpl` / `slotsOfSigPkFrozenPlaced`) Assembly -/

theorem AtRunEntryPlaced.toRoCl [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {S : RunSem} {g : RunCall} {s0 : State} (he : AtRunEntryPlaced CodeOk S g s0) :
    AtRunEntryPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) S g s0 :=
  { he with inv := hCI.toRoCl he.inv }

theorem AtDispatchPlaced.toRoCl [LibsignalPlacement] {CodeOk : Memory → Prop} [hCI : LsCodeInv CodeOk]
    {g : RunCall} {me : MeAtDispatch} {s0 s : State} (hd : AtDispatchPlaced CodeOk g me s0 s) :
    AtDispatchPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) g me s0 s :=
  { hd with base := { hd.base with inv := hCI.toRoCl hd.base.inv } }

/-- Bundle of the relocatable (`[LibsignalPlacement]`) arm hop contracts of `signal_session::run`
(Block `579`) for `slotsOfSigPkFrozenPlaced` under `LibsignalFrozen lsmpl`. -/
structure RunArmsFrozenPlaced [LibsignalPlacement] (A : RustAlloc)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop where
  join : RunHopJoinPlaced (LibsignalFrozen lsmpl) A H B S needs resStack
  joinRo : RunHopJoinPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A H B S needs resStack
  pre : RunHopPrePlacedOf (LibsignalFrozen lsmpl) A H B S (slotsOfSigPkFrozenPlaced A S needs) resStack
  init1 : RunHopInit1PlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A H B S
    (slotsOfSigPkFrozenPlaced A S needs) resStack
  init2 : RunHopInit2PlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A H B S
    (slotsOfSigPkFrozenPlaced A S needs) resStack
  init3 : RunHopInit3PlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A H B S
    (slotsOfSigPkFrozenPlaced A S needs) resStack
  send : RunHopSendPlacedOf (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A H B S
    (slotsOfSigPkFrozenPlaced A S needs) resStack
  recvW : RunHopRecvWPlacedOf (LibsignalFrozen lsmpl) A H B S (slotsOfSigPkFrozenPlaced A S needs) resStack
  recvP : RunHopRecvPPlacedOf (LibsignalFrozen lsmpl) A H B S (slotsOfSigPkFrozenPlaced A S needs) resStack
  recvBad : RunHopRecvBadPlaced (LibsignalFrozen lsmpl) A H B S needs resStack

/-- `signal_session::run` (Block `579`) meets `runSpecPlaced (LibsignalFrozen lsmpl)` for
`slotsOfSigPkFrozenPlaced` under `[LibsignalPlacement]`. -/
theorem run_ok_frozen_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsFrozenPlaced A H B S needs resStack)
    (hh : RunHooksPlaced A H)
    (hc : RunCalleesPlaced A H B (slotsOfSigPkFrozenPlaced A S needs))
    (hpksm : subroutine_ok (runProgPlaced H) (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced A S))
    (hres : runNeed B (slotsOfSigPkFrozenPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (runSpecPlaced (LibsignalFrozen lsmpl) A uuidTryParse (runRel S) cliWrOk resStack) := by
  have hres_base : runNeed B (slotsOfPlaced A S needs) ≤ resStack := hres
  apply subroutine_ok_of_sepWPp_init
  intro g R s0 hpc hrun hpre hsp
  have hspb : resStack ≤ s0.sp.toNat := by
    have hpre' := hpre
    simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    rcases hpre' with ⟨⟨_, _, _, _, _, _, _, _, _, _, hspb⟩, _⟩
    exact hspb
  rcases runEntry_of_placed_pre hpc hrun hpre hsp with ⟨he, hmem⟩
  refine ⟨runEntryMemPlaced A g s0 resStack, hmem, ?_⟩
  let Q : State → SepProp → Prop := fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlaced (LibsignalFrozen lsmpl) A uuidTryParse (runRel S) cliWrOk resStack).post g s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
  let Qp : State → SepProp → Prop := fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlaced (LibsignalFrozen lsmpl) A uuidTryParse (runRel S) cliWrOk resStack).onPanic g s0 sf ∗ R)
  have hdrop : RunDrop.DropSpeOwnedOkAtBlock (runProgPlaced H) A :=
    run_hop_dropSpeOwned_placed hh.alloc
  have hpanic : PanicK g s0 Qp := fun _ _ hpan hmf =>
    placed_onPanic_of_runPanic (CodeOk := LibsignalFrozen lsmpl) (S := S) (A := A)
      (resStack := resStack) hpan hmf
  have hpost_mono : ∀ {sf Pf}, runPostPlaced (LibsignalFrozen lsmpl) A g resStack s0 sf Pf → Q sf Pf :=
    fun hp => ⟨fun hmf => (placed_post_of_runPost he.fs he.stdout hp hmf).1, hp.2.1, hp.2.2.1⟩
  have hpost_mono_ro :
      ∀ {sf Pf},
        runPostPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) A g resStack s0 sf Pf →
          Q sf Pf :=
    fun hp => ⟨fun hmf => (placed_post_of_runPost (S := S) he.fs he.stdout hp hmf).1, hp.2.1, hp.2.2.1⟩
  have hjoin : JoinKPlaced (LibsignalFrozen lsmpl) H A g s0 resStack Q Qp := fun s g' out hj =>
    sepWPp_mono_post (fun _ _ hp => hpost_mono hp)
      (harms.join hh hres_base hres64 (Or.inl ⟨g', out, hj, rfl⟩))
  have hrej : RejectKPlaced (LibsignalFrozen lsmpl) H A g s0 resStack Q Qp := fun s g' rk hr =>
    sepWPp_mono_post (fun _ _ hp => hpost_mono hp)
      (harms.join hh hres_base hres64 (Or.inr ⟨g', rk, hr, rfl⟩))
  have hjoin_ro :
      JoinKPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) H A g s0 resStack Q Qp :=
    fun s g' out hj =>
      sepWPp_mono_post (fun _ _ hp => hpost_mono_ro hp)
        (harms.joinRo hh hres_base hres64 (Or.inl ⟨g', out, hj, rfl⟩))
  have hrej_ro :
      RejectKPlaced (LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl) H A g s0 resStack Q Qp :=
    fun s g' rk hr =>
      sepWPp_mono_post (fun _ _ hp => hpost_mono_ro hp)
        (harms.joinRo hh hres_base hres64 (Or.inr ⟨g', rk, hr, rfl⟩))
  rw [placed_onOom_eq (CodeOk := LibsignalFrozen lsmpl) (S := S) (A := A) g resStack s0]
  refine harms.pre hh hc hdrop hres hres64 he hpanic hrej fun s me hd => ?_
  cases hcall : g.c with
  | keygen meK nK =>
    have htag : g.c.tag ≠ 0 := runRel_not_keygen he.rel he.parse
    rw [hcall] at htag
    exact absurd rfl htag
  | send peerV =>
    exact harms.send hh hc hdrop hres hres64 hspb he.toRoCl hd.toRoCl hcall hpanic hrej_ro hjoin_ro
  | init peerV dir =>
    exact harms.init1 hh hc hdrop hres hres64 he.toRoCl hd.toRoCl hcall hpanic hrej_ro fun s1 d1 hi1 =>
      harms.init2 hh hc hdrop hres hres64 he.toRoCl hi1 hpanic hrej_ro fun s2 d2 hi2 =>
        harms.init3 hh hc hdrop hres hres64 hspb he.toRoCl hi2 hpanic hrej_ro hjoin_ro
  | recv peerV =>
    cases hstdin : g.i.stdin with
    | nil =>
      exact harms.recvBad hh hres_base hres64 he hd hcall (Or.inl hstdin) hrej
    | cons t rest =>
      by_cases ht2 : t = 2#8
      · subst ht2
        exact harms.recvW hh hc hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin
      · by_cases ht3 : t = 3#8
        · subst ht3
          exact harms.recvP hh hc hpksm hdrop hres hres64 hspb he hd hcall hstdin hpanic hrej hjoin
        · exact harms.recvBad hh hres_base hres64 he hd hcall
            (Or.inr ⟨t, rest, hstdin, ht2, ht3⟩) hrej

/-- `signal_session::run` (Block `579`) meets `withLsFrozen lsmpl (runSpecPlaced ...)` under
`[LibsignalPlacement]`. -/
theorem run_ok_withLsFrozen_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsFrozenPlaced A H B S needs resStack)
    (hh : RunHooksPlaced A H)
    (hc : RunCalleesPlaced A H B (slotsOfSigPkFrozenPlaced A S needs))
    (hpksm : subroutine_ok (runProgPlaced H) (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced A S))
    (hres : runNeed B (slotsOfSigPkFrozenPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (withLsFrozen lsmpl
        (runSpecPlaced (LibsignalFrozen lsmpl) A uuidTryParse (runRel S) cliWrOk resStack)) :=
  LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.subroutine_ok_withLsFrozen_of_plain
    (run_ok_frozen_placed harms hh hc hpksm hres hres64)

/-- Cross-block transfer of `run_ok_withLsFrozen_placed` from Block `579` (`runProgPlaced H`)
to any caller block `i < 624` (`callerProg`, e.g. Block `617` `mProgPlaced H`) under
`[LibsignalFullPlacement]`. -/
theorem run_ok_frozen_placed_at_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    (harms : RunArmsFrozenPlaced A H B S needs resStack)
    (hh : RunHooksPlaced A H)
    (hc : RunCalleesPlaced A H B (slotsOfSigPkFrozenPlaced A S needs))
    (hpksm : subroutine_ok (runProgPlaced H) (CryptoVerification.blkPl_111).base
      (pksmSlotSpecPlaced A S))
    (hres : runNeed B (slotsOfSigPkFrozenPlaced A S needs) ≤ resStack) (hres64 : resStack ≤ 2 ^ 63)
    (_hi : i < 624 := by decide) :
    subroutine_ok callerProg (lsmpl.base 579)
      (runSpecPlaced (LibsignalFrozen lsmpl) A uuidTryParse (runRel S) cliWrOk resStack) := by
  have h579 : IsLsBlockProg (runProgPlaced H) 579 H := inferInstance
  have hfr := @LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
    _ _ callerProg (runProgPlaced H) i 579 H hcaller h579 (lsmpl.base 579) _
    (run_ok_withLsFrozen_placed harms hh hc hpksm hres hres64) (by decide)
  refine subroutine_ok_mono hfr ?_ (fun _ _ _ _ h => h)
  intro g R s0 hpre
  dsimp only [withLsFrozen]
  have hpre' := hpre
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hcomm :
      (runSpecPlaced (LibsignalFrozen lsmpl)
        A uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗
        ⌜LibsignalFrozen lsmpl s0.mem⌝ ∗ R =
      ⌜LibsignalFrozen lsmpl s0.mem⌝ ∗
        ((runSpecPlaced (LibsignalFrozen lsmpl)
          A uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗ R) := by
    ac_rfl
  rw [sepConj_assoc, hcomm, satisfies_pure_sepConj]
  exact ⟨hpre'.1.1, hpre⟩

end CryptoVerification.SignalSession.Cli.RunCompose
