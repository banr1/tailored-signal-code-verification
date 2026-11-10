/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# `FdsGe3Closed`-Threaded `signal_session::run` Composition

Bundles the nine `FdsGe3Closed`-threaded arm hop contracts (`RunArmsPlacedFd` /
`RunArmsFrozenPlacedFd`) on Block `579` (`signal_session::run`) and proves `run_ok_placed_fd`,
`run_ok_frozen_placed_fd`, and their cross-block transfers against `runSpecPlacedPreFd`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification
  (IsLsBlockProg LibsignalFrozen LibsignalFullPlacement LibsignalHooks LibsignalPlacement
   blkPl_111 lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded ls_subroutine_ok_rocl_of_block withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (withLsFrozen)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV RunCall cliWrOk)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtInit1Placed AtInit2Placed Init1Data Init2Data MeAtDispatch
   PanicK RunNeeds RunSem addrValOf readBundleV runFiles runProgPlaced runRel runRel_not_keygen
   sepWPp_mono_post)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
  (RunHopInit1PlacedFd RunHopInit1PlacedFdOf RunHopInit2PlacedFd RunHopInit2PlacedFdOf
   RunHopInit3PlacedFd RunHopInit3PlacedFdOf RunHopPrePlacedFd RunHopPrePlacedFdOf
   RunHopRecvPPlacedFd RunHopRecvPPlacedFdOf RunHopRecvWPlacedFd RunHopRecvWPlacedFdOf
   RunHopSendPlacedFd RunHopSendPlacedFdOf pksmSlotSpecPlacedOkFs tryFromPlacedSpecOkFs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
  (RunHopJoinPlaced runPostPlaced_of_joinPost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
  (RunHopRecvBadPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv run_hop_dropSpeOwned_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmAtMeEnv RunArmEnvs RunCoreEnv RunDispatchEnv RunEnv RunInit2ChainEnv RunInit3Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced slotsOfSigPkFrozenPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (runEntryMemPlaced runPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
  (AtDispatchPlacedFd placed_onPanic_of_runPanic_preFd placed_post_of_runPost_preFd
   runEntryFd_of_placed_pre runSpecAnyPlacedPreFd runSpecPlacedPreFd sp_lr_of_placed_preFd
   subroutine_ok_runSpecAnyPlacedPreFd_of_placed subroutine_ok_runSpecPlacedPreFd_mono_env)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd extract_withPreFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (runSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees
  (ls_subroutine_ok_withLsFrozen_of_block_frc subroutine_ok_withLsFrozen_of_plain)

export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
  (RunArmAtMeEnv RunArmEnvs RunCoreEnv RunDispatchEnv RunEnv RunInit2ChainEnv RunInit3Env)
export LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
  (subroutine_ok_runSpecAnyPlacedPreFd_of_placed subroutine_ok_runSpecPlacedPreFd_mono_env)

/-! ## Section 1: Arm Hop Bundle (`RunArmsPlacedFd`) -/

/-- Bundle of the 9 `FdsGe3Closed`-threaded arm hop contracts of `signal_session::run`
(Block `579`) under `[LibsignalPlacement]`. -/
structure RunArmsPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs) (aEnvs : RunArmEnvs)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) :
    Prop where
  join : RunHopJoinPlaced CodeOk A lim sEnvs H B S needs resStack
  pre : RunHopPrePlacedFd CodeOk A lim cEnvs sEnvs aEnvs.pre H B S needs resStack
  init1 : RunHopInit1PlacedFd CodeOk A lim cEnvs sEnvs aEnvs.init1 H B S needs resStack
  init2 : RunHopInit2PlacedFd CodeOk A lim cEnvs sEnvs aEnvs.init2 H B S needs resStack
  init3 : RunHopInit3PlacedFd CodeOk A lim cEnvs sEnvs aEnvs.init3 H B S needs resStack
  send : RunHopSendPlacedFd CodeOk A lim cEnvs sEnvs aEnvs.send H B S needs resStack
  recvW : RunHopRecvWPlacedFd CodeOk A lim cEnvs sEnvs aEnvs.recvW H B S needs resStack
  recvP : RunHopRecvPPlacedFd CodeOk A lim cEnvs sEnvs aEnvs.pksmTryFrom aEnvs.recvP H B S needs
    resStack
  recvBad : RunHopRecvBadPlaced CodeOk A lim sEnvs H B S needs resStack

/-! ## Section 2: Internal Seam Projection Lemmas -/

private theorem dispatchFd_toRoCl [LibsignalPlacement] {g : RunCall} {me : MeAtDispatch}
    {s0 s : State}
    (hd : AtDispatchPlacedFd (LibsignalFrozen lsmpl) g me s0 s) :
    AtDispatchPlacedFd (LibsignalCodeRoLoaded lsmpl) g me s0 s :=
  ⟨hd.1.toRoCl, hd.2⟩

private theorem dispatchEnv_of_armAtMe [LibsignalPlacement] {CodeOk : Memory → Prop}
    {aEnvs : RunArmEnvs} {g : RunCall} {me : MeAtDispatch} {s0 s : State}
    (hd : AtDispatchPlaced CodeOk g me s0 s) {evs : List AllocEvent}
    (h : RunArmAtMeEnv aEnvs g me evs) :
    RunDispatchEnv aEnvs g evs := by
  rcases hd.ownSem with ⟨ownB, hget, hparse⟩
  cases me with
  | none =>
    simpa only [RunDispatchEnv, hget, hparse] using h
  | some meV meG =>
    rcases hd.meRegs with ⟨_, _, hbytes, hcap, hdev⟩
    simp only [RunDispatchEnv, hget, hparse]
    exact ⟨meG, hdev, hbytes, hcap, h⟩

private theorem init1_impossible_of_none [LibsignalPlacement] {CodeOk : Memory → Prop}
    {g : RunCall} {d1 : Init1Data} {s0 s s1 : State}
    (hd : AtDispatchPlaced CodeOk g .none s0 s)
    (hi1 : AtInit1Placed CodeOk g d1 s0 s1) : False := by
  rcases hd.ownSem with ⟨ownB, hget0, hnone⟩
  rcases hi1.ownSem with ⟨ownB', hget1, hsome⟩
  cases hget0.symm.trans hget1
  cases hnone.symm.trans hsome

private theorem init2ChainEnv_of_atInit1 [LibsignalPlacement] {CodeOk : Memory → Prop}
    {aEnvs : RunArmEnvs} {g : RunCall} {meV : AddrV} {meG : AddrGhost}
    {peerV : AddrV} {dir : List (BitVec 8)} {d1 : Init1Data} {s0 s s1 : State}
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .init peerV dir)
    (hi1 : AtInit1Placed CodeOk g d1 s0 s1) {evs : List AllocEvent}
    (h : SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir) evs) :
    RunInit2ChainEnv aEnvs g meV peerV dir evs := by
  have hcd : CallV.init d1.peerV d1.dir = CallV.init peerV dir := hi1.callEq.symm.trans hcall
  injection hcd with hpeer hdir
  rcases hd.ownSem with ⟨ownB, hget0, hme0⟩
  rcases hi1.ownSem with ⟨ownB', hget1, hme1⟩
  cases hget0.symm.trans hget1
  have hme : d1.meV = meV := Option.some.inj (hme1.symm.trans hme0)
  rcases hi1.ikSem with ⟨ikB, hbf, hdec⟩
  rw [hdir] at hbf
  simp only [RunInit2ChainEnv, hbf, hdec]
  exact ⟨d1, hpeer, hdir, hme, rfl,
    hi1.peerVal.trans (congrArg addrValOf hpeer),
    hi1.meVal.trans (congrArg addrValOf hme),
    hi1.ikWords, h⟩

private theorem init3Env_of_atInit2 [LibsignalPlacement] {CodeOk : Memory → Prop}
    {aEnvs : RunArmEnvs} {g : RunCall} {meV : AddrV} {meG : AddrGhost}
    {peerV : AddrV} {dir : List (BitVec 8)} {d2 : Init2Data} {s0 s s2 : State}
    (hd : AtDispatchPlaced CodeOk g (.some meV meG) s0 s)
    (hcall : g.c = .init peerV dir)
    (hi2 : AtInit2Placed CodeOk g d2 s0 s2) {evs : List AllocEvent}
    (h : aEnvs.init3 g d2 evs) :
    RunInit3Env aEnvs g meV peerV dir evs := by
  have hcd : CallV.init d2.peerV d2.dir = CallV.init peerV dir := hi2.callEq.symm.trans hcall
  injection hcd with hpeer hdir
  rcases hd.ownSem with ⟨ownB, hget0, hme0⟩
  rcases hi2.ownSem with ⟨ownB', hget1, hme1⟩
  cases hget0.symm.trans hget1
  have hme : d2.meV = meV := Option.some.inj (hme1.symm.trans hme0)
  have hbun : readBundleV (runFiles g.i) dir peerV.device = some d2.bundle := by
    simpa only [hdir, hpeer] using hi2.bundleSem
  simp only [RunInit3Env, hbun]
  exact ⟨d2, hpeer, hdir, hme, rfl,
    hi2.peerVal.trans (congrArg addrValOf hpeer),
    hi2.meVal.trans (congrArg addrValOf hme),
    hi2.ptrsNeZero.1, hi2.ptrsNeZero.2.1, hi2.ptrsNeZero.2.2, h⟩

/-! ## Section 3: Top-Level `run_ok_placed_fd` & Cross-Block Transfers -/

/-- `signal_session::run` (Block `579`) meets `runSpecPlacedPreFd` at `runRel S` and `RunEnv aEnvs`
under `[LibsignalPlacement]`. -/
theorem run_ok_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsPlacedFd CodeOk A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (htry : subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (runSpecPlacedPreFd CodeOk A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack) := by
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨g, st⟩ R s0 hpc hrun hpre hsp
  obtain ⟨hspb, hlr_ls⟩ := sp_lr_of_placed_preFd (S := S) hpre
  rcases runEntryFd_of_placed_pre (S := S) hpc hrun hpre hsp with ⟨he, hfits, hmem⟩
  refine ⟨runEntryMemPlaced A lim st g s0 resStack, hmem, ?_⟩
  let Q : State → SepProp → Prop := fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlacedPreFd CodeOk A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk
          resStack).post (g, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
  let Qp : State → SepProp → Prop := fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlacedPreFd CodeOk A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk
          resStack).onPanic (g, st) s0 sf ∗ R)
  have hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim :=
    run_hop_dropSpeOwned_placed hh.alloc
  have hpanic : PanicK g s0 Qp := fun _ _ hpan hmf =>
    placed_onPanic_of_runPanic_preFd (CodeOk := CodeOk) (S := S) (A := A) (lim := lim)
      (RunEnv := RunEnv aEnvs) (st := st) (resStack := resStack) hpan hmf
  have hpost_mono :
      ∀ {sf Pf}, runPostPlaced CodeOk A lim (RunEnv aEnvs) g st resStack s0 sf Pf → Q sf Pf :=
    fun hp =>
      ⟨fun hmf => (placed_post_of_runPost_preFd (S := S) he.1.fs he.1.stdout hp hmf).1,
        hp.2.1, hp.2.2.1⟩
  have mkRej : ∀ {st_cur : M.σ} {evs_pref : List AllocEvent} {ArmEnv : List AllocEvent → Prop},
      st_cur = M.stepEvents evs_pref st →
      (∀ evs_a, ArmEnv evs_a → RunCoreEnv aEnvs g (evs_pref ++ evs_a)) →
      RejectKPlacedEnv CodeOk H A lim
        (fun _ _ st' => ∃ evs, ArmEnv evs ∧ st' = M.stepEvents evs st_cur)
        g s0 resStack Q Qp := by
    intro st_cur evs_pref ArmEnv hst_cur hCore sr st' g' rk hr ⟨evs_a, harm, hst'⟩
    have hst_tot : st' = M.stepEvents (evs_pref ++ evs_a) st := by
      rw [hst', hst_cur, ← M.stepEvents_append]
    exact sepWPp_mono_post
      (fun _ _ hp => hpost_mono
        (runPostPlaced_of_joinPost hst_tot
          (fun evs_j hfj => SeqEnv.append (hCore evs_a harm) hfj) hp))
      (harms.join hh hres hres64 hlr_ls (Or.inr ⟨g', rk, hr, rfl⟩))
  have mkJoin : ∀ {st_cur : M.σ} {evs_pref : List AllocEvent} {ArmEnv : List AllocEvent → Prop},
      st_cur = M.stepEvents evs_pref st →
      (∀ evs_a, ArmEnv evs_a → RunCoreEnv aEnvs g (evs_pref ++ evs_a)) →
      JoinKPlacedEnv CodeOk H A lim
        (fun _ _ st' => ∃ evs, ArmEnv evs ∧ st' = M.stepEvents evs st_cur)
        g s0 resStack Q Qp := by
    intro st_cur evs_pref ArmEnv hst_cur hCore sj st' g' out hj ⟨evs_a, harm, hst'⟩
    have hst_tot : st' = M.stepEvents (evs_pref ++ evs_a) st := by
      rw [hst', hst_cur, ← M.stepEvents_append]
    exact sepWPp_mono_post
      (fun _ _ hp => hpost_mono
        (runPostPlaced_of_joinPost hst_tot
          (fun evs_j hfj => SeqEnv.append (hCore evs_a harm) hfj) hp))
      (harms.join hh hres hres64 hlr_ls (Or.inl ⟨g', out, hj, rfl⟩))
  have hfits_core : FitsEnv M lim st (RunCoreEnv aEnvs g) := hfits.seq_left
  change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s0
    (runEntryMemPlaced A lim st g s0 resStack) Q Qp (fun _ => ⌜False⌝)
  refine harms.pre hh hc hdrop hres hres64 he hfits_core.seq_left hpanic
    (mkRej (evs_pref := []) rfl fun _ h => SeqEnv.inl h) fun s evs₀ me hd hpre₀ => ?_
  have hsub_me : ∀ evs₁, RunArmAtMeEnv aEnvs g me evs₁ → RunDispatchEnv aEnvs g evs₁ :=
    fun _ h => dispatchEnv_of_armAtMe hd.1 h
  have hfits_arm : FitsEnv M lim (M.stepEvents evs₀ st) (RunArmAtMeEnv aEnvs g me) :=
    (hfits_core.seq_right hpre₀).mono hsub_me
  have hCore1 : ∀ evs₁, RunArmAtMeEnv aEnvs g me evs₁ → RunCoreEnv aEnvs g (evs₀ ++ evs₁) :=
    fun evs₁ h => SeqEnv.append hpre₀ (hsub_me evs₁ h)
  cases hcall : g.c with
  | keygen meK nK =>
    have htag : g.c.tag ≠ 0 := runRel_not_keygen he.1.rel he.1.parse
    rw [hcall] at htag
    exact absurd rfl htag
  | send peerV =>
    have hsub_s : ∀ evs₁, aEnvs.send g me peerV evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
      intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
    exact harms.send hh hc hdrop hres hres64 hspb he.1 hd hcall (hfits_arm.mono hsub_s) hpanic
      (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_s evs₁ h))
      (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_s evs₁ h))
  | init peerV dir =>
    cases me with
    | none =>
      have hsub_i0 :
          ∀ evs₁, aEnvs.init1 g .none peerV dir evs₁ → RunArmAtMeEnv aEnvs g .none evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
      exact harms.init1 hh hc hdrop hres hres64 he.1 hd hcall (hfits_arm.mono hsub_i0) hpanic
        (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_i0 evs₁ h))
        fun _ _ _ hi1 _ => (init1_impossible_of_none hd.1 hi1.1).elim
    | some meV meG =>
      have hsub_is :
          ∀ evs₁,
            SeqEnv (aEnvs.init1 g (.some meV meG) peerV dir)
              (RunInit2ChainEnv aEnvs g meV peerV dir) evs₁ →
              RunArmAtMeEnv aEnvs g (.some meV meG) evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
      have hfits_i12 :
          FitsEnv M lim (M.stepEvents evs₀ st)
            (SeqEnv (aEnvs.init1 g (.some meV meG) peerV dir)
              (RunInit2ChainEnv aEnvs g meV peerV dir)) :=
        hfits_arm.mono hsub_is
      refine harms.init1 hh hc hdrop hres hres64 he.1 hd hcall hfits_i12.seq_left hpanic
        (mkRej rfl fun evs₁ h1 => hCore1 evs₁ (hsub_is evs₁ (SeqEnv.inl h1)))
        fun s1 evs₁ d1 hi1 hinit1 => ?_
      have hst₂ : M.stepEvents evs₁ (M.stepEvents evs₀ st) = M.stepEvents (evs₀ ++ evs₁) st :=
        (M.stepEvents_append evs₀ evs₁ st).symm
      have hsub_d1 :
          ∀ evs₂,
            SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir) evs₂ →
              RunInit2ChainEnv aEnvs g meV peerV dir evs₂ :=
        fun _ h => init2ChainEnv_of_atInit1 hd.1 hcall hi1.1 h
      have hfits_i23 :
          FitsEnv M lim (M.stepEvents evs₁ (M.stepEvents evs₀ st))
            (SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir)) :=
        (hfits_i12.seq_right hinit1).mono hsub_d1
      refine harms.init2 hh hc hdrop hres hres64 he.1 hi1 hfits_i23.seq_left hpanic
        (mkRej hst₂ fun evs₂ h2 => by
          rw [List.append_assoc]
          exact hCore1 (evs₁ ++ evs₂)
            (hsub_is _ (SeqEnv.append hinit1 (hsub_d1 evs₂ (SeqEnv.inl h2)))))
        fun s2 evs₂ d2 hi2 hinit2 => ?_
      have hst₃ :
          M.stepEvents evs₂ (M.stepEvents evs₁ (M.stepEvents evs₀ st)) =
            M.stepEvents ((evs₀ ++ evs₁) ++ evs₂) st := by
        rw [hst₂, ← M.stepEvents_append]
      have hsub_d2 : ∀ evs₃, aEnvs.init3 g d2 evs₃ → RunInit3Env aEnvs g meV peerV dir evs₃ :=
        fun _ h => init3Env_of_atInit2 hd.1 hcall hi2.1 h
      have hCore3 :
          ∀ evs₃, aEnvs.init3 g d2 evs₃ →
            RunCoreEnv aEnvs g (((evs₀ ++ evs₁) ++ evs₂) ++ evs₃) := by
        intro evs₃ h3
        simp only [List.append_assoc]
        exact hCore1 (evs₁ ++ (evs₂ ++ evs₃))
          (hsub_is _ (SeqEnv.append hinit1 (hsub_d1 (evs₂ ++ evs₃)
            (SeqEnv.append hinit2 (hsub_d2 evs₃ h3)))))
      exact harms.init3 hh hc hdrop hres hres64 hspb he.1 hi2
        ((hfits_i23.seq_right hinit2).mono hsub_d2) hpanic
        (mkRej hst₃ hCore3) (mkJoin hst₃ hCore3)
  | recv peerV =>
    cases hstdin : g.i.stdin with
    | nil =>
      have hsub_r0 : ∀ evs₁, FreeOnlyEvs evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin] using h
      exact harms.recvBad hh hres hres64 he.1 hd.1 hcall (Or.inl hstdin)
        (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_r0 evs₁ h))
    | cons t rest =>
      by_cases ht2 : t = 2#8
      · subst ht2
        have hsub_rw : ∀ evs₁, aEnvs.recvW g me peerV rest evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
          intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ↓reduceIte] using h
        exact harms.recvW hh hc htry hdrop hres hres64 hspb he.1 hd hcall hstdin
          (hfits_arm.mono hsub_rw) hpanic
          (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rw evs₁ h))
          (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_rw evs₁ h))
      · by_cases ht3 : t = 3#8
        · subst ht3
          have hsub_rp :
              ∀ evs₁, aEnvs.recvP g me peerV rest evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
            intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ht2, ↓reduceIte] using h
          exact harms.recvP hh hc hpksm hdrop hres hres64 hspb he.1 hd hcall hstdin
            (hfits_arm.mono hsub_rp) hpanic
            (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rp evs₁ h))
            (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_rp evs₁ h))
        · have hsub_rb : ∀ evs₁, FreeOnlyEvs evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
            intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ht2, ht3, ↓reduceIte] using h
          exact harms.recvBad hh hres hres64 he.1 hd.1 hcall
            (Or.inr ⟨t, rest, hstdin, ht2, ht3⟩)
            (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rb evs₁ h))

/-- `signal_session::run` (Block `579`) meets `withLsCodeRoLoaded (runSpecPlacedPreFd ...)` under
`[LibsignalPlacement]`, enabling cross-block transfer via `ls_subroutine_ok_rocl_of_block`. -/
theorem run_ok_withLsCodeRoLoaded_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsPlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs aEnvs H B S needs
      resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (htry : subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (withLsCodeRoLoaded lsmpl
        (runSpecPlacedPreFd (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs)
          uuidTryParse (runRel S) cliWrOk resStack)) := by
  refine subroutine_ok_mono (run_ok_placed_fd harms hh hc htry hpksm hres hres64) ?_
    (fun _ _ _ _ h => h)
  intro g R s0 hpre
  exact Satisfies.drop_mid (by
    simpa only [withLsCodeRoLoaded, sepConj_assoc] using hpre)

/-- Cross-block transfer of `run_ok_withLsCodeRoLoaded_placed_fd` from Block `579`
(`runProgPlaced H`) to any caller block `i < 619` (`callerProg`, e.g. Block `617`
`mProgPlaced H`). -/
theorem run_ok_placed_at_block_fd [LibsignalPlacement] {M : AllocCostModel}
    {callerProg : Program} {i : Nat} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    (harms : RunArmsPlacedFd (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs aEnvs H B S needs
      resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (htry : subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 579)
      (runSpecPlacedPreFd (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs)
        uuidTryParse (runRel S) cliWrOk resStack) := by
  have h579 : IsLsBlockProg (runProgPlaced H) 579 H := inferInstance
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    (runProgPlaced H) i 579 H hcaller h579 (lsmpl.base 579) _
    (run_ok_withLsCodeRoLoaded_placed_fd harms hh hc htry hpksm hres hres64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl ?_ ?_
  · intro g R s0 hpre
    dsimp only [withLsRoCl]
    obtain ⟨_, hpre0⟩ := extract_withPreFdsGe3Closed hpre
    simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre0
    have hcomm :
        (runSpecPlacedPreFd (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs)
          uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          ((runSpecPlacedPreFd (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs)
            uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗ R) := by
      sep_ac_rfl
    rw [sepConj_assoc, hcomm, satisfies_pure_sepConj]
    exact ⟨hpre0.1.1, hpre⟩
  · intro g R s0 sf hpost
    dsimp only [withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

/-! ## Section 4: `LibsignalFrozen` / `[LibsignalFullPlacement]` Composition -/

/-- Bundle of the `FdsGe3Closed`-threaded arm hop contracts of `signal_session::run` (Block `579`)
upgraded to `LibsignalFrozen lsmpl` at `slotsOfSigPkFrozenPlaced` (with `init1..3`, `send`, and
`recvBad` proved at `LibsignalCodeRoLoaded lsmpl` and lifted via `toRoCl` + `joinRo`). -/
structure RunArmsFrozenPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs) (aEnvs : RunArmEnvs)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) :
    Prop where
  join : RunHopJoinPlaced (LibsignalFrozen lsmpl) A lim sEnvs H B S needs resStack
  joinRo : RunHopJoinPlaced (LibsignalCodeRoLoaded lsmpl) A lim sEnvs H B S needs resStack
  pre : RunHopPrePlacedFdOf (LibsignalFrozen lsmpl) A lim cEnvs aEnvs.pre H B S
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack
  init1 : RunHopInit1PlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim cEnvs aEnvs.init1 H B S
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack
  init2 : RunHopInit2PlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim cEnvs aEnvs.init2 H B S
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack
  init3 : RunHopInit3PlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim cEnvs aEnvs.init3 H B S
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack
  send : RunHopSendPlacedFdOf (LibsignalCodeRoLoaded lsmpl) A lim cEnvs aEnvs.send H B S
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack
  recvW : RunHopRecvWPlacedFdOf (LibsignalFrozen lsmpl) A lim cEnvs aEnvs.recvW H B S
    (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack
  recvP : RunHopRecvPPlacedFdOf (LibsignalFrozen lsmpl) A lim cEnvs aEnvs.pksmTryFrom aEnvs.recvP
    H B S (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) resStack
  recvBad : RunHopRecvBadPlaced (LibsignalCodeRoLoaded lsmpl) A lim sEnvs H B S needs resStack

/-- `signal_session::run` (Block `579`) meets `runSpecPlacedPreFd (LibsignalFrozen lsmpl)` at
`slotsOfSigPkFrozenPlaced` under `[LibsignalPlacement]`. -/
theorem run_ok_frozen_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsFrozenPlacedFd A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B (slotsOfSigPkFrozenPlaced A lim sEnvs S needs))
    (htry : subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (runSpecPlacedPreFd (LibsignalFrozen lsmpl)
        A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack) := by
  have hres_base : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack := hres
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨g, st⟩ R s0 hpc hrun hpre hsp
  obtain ⟨hspb, hlr_ls⟩ := sp_lr_of_placed_preFd (S := S) hpre
  rcases runEntryFd_of_placed_pre (S := S) hpc hrun hpre hsp with ⟨he, hfits, hmem⟩
  refine ⟨runEntryMemPlaced A lim st g s0 resStack, hmem, ?_⟩
  let Q : State → SepProp → Prop := fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlacedPreFd (LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).post
          (g, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
  let Qp : State → SepProp → Prop := fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlacedPreFd (LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).onPanic
          (g, st) s0 sf ∗ R)
  have hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim :=
    run_hop_dropSpeOwned_placed hh.alloc
  have hpanic : PanicK g s0 Qp := fun _ _ hpan hmf =>
    placed_onPanic_of_runPanic_preFd
      (CodeOk := LibsignalFrozen lsmpl)
      (S := S) (A := A) (lim := lim) (RunEnv := RunEnv aEnvs) (st := st) (resStack := resStack)
      hpan hmf
  have hpost_mono :
      ∀ {sf Pf},
        runPostPlaced (LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) g st resStack s0 sf Pf → Q sf Pf :=
    fun hp =>
      ⟨fun hmf => (placed_post_of_runPost_preFd (S := S) he.1.fs he.1.stdout hp hmf).1,
        hp.2.1, hp.2.2.1⟩
  have hpost_mono_ro :
      ∀ {sf Pf},
        runPostPlaced (LibsignalCodeRoLoaded lsmpl)
          A lim (RunEnv aEnvs) g st resStack s0 sf Pf → Q sf Pf :=
    fun hp =>
      ⟨fun hmf => (placed_post_of_runPost_preFd (S := S) he.1.fs he.1.stdout hp hmf).1,
        hp.2.1, hp.2.2.1⟩
  have mkRej : ∀ {st_cur : M.σ} {evs_pref : List AllocEvent} {ArmEnv : List AllocEvent → Prop},
      st_cur = M.stepEvents evs_pref st →
      (∀ evs_a, ArmEnv evs_a → RunCoreEnv aEnvs g (evs_pref ++ evs_a)) →
      RejectKPlacedEnv (LibsignalFrozen lsmpl) H A lim
        (fun _ _ st' => ∃ evs, ArmEnv evs ∧ st' = M.stepEvents evs st_cur)
        g s0 resStack Q Qp := by
    intro st_cur evs_pref ArmEnv hst_cur hCore sr st' g' rk hr ⟨evs_a, harm, hst'⟩
    have hst_tot : st' = M.stepEvents (evs_pref ++ evs_a) st := by
      rw [hst', hst_cur, ← M.stepEvents_append]
    exact sepWPp_mono_post
      (fun _ _ hp => hpost_mono
        (runPostPlaced_of_joinPost hst_tot
          (fun evs_j hfj => SeqEnv.append (hCore evs_a harm) hfj) hp))
      (harms.join hh hres_base hres64 hlr_ls (Or.inr ⟨g', rk, hr, rfl⟩))
  have mkJoin : ∀ {st_cur : M.σ} {evs_pref : List AllocEvent} {ArmEnv : List AllocEvent → Prop},
      st_cur = M.stepEvents evs_pref st →
      (∀ evs_a, ArmEnv evs_a → RunCoreEnv aEnvs g (evs_pref ++ evs_a)) →
      JoinKPlacedEnv (LibsignalFrozen lsmpl) H A lim
        (fun _ _ st' => ∃ evs, ArmEnv evs ∧ st' = M.stepEvents evs st_cur)
        g s0 resStack Q Qp := by
    intro st_cur evs_pref ArmEnv hst_cur hCore sj st' g' out hj ⟨evs_a, harm, hst'⟩
    have hst_tot : st' = M.stepEvents (evs_pref ++ evs_a) st := by
      rw [hst', hst_cur, ← M.stepEvents_append]
    exact sepWPp_mono_post
      (fun _ _ hp => hpost_mono
        (runPostPlaced_of_joinPost hst_tot
          (fun evs_j hfj => SeqEnv.append (hCore evs_a harm) hfj) hp))
      (harms.join hh hres_base hres64 hlr_ls (Or.inl ⟨g', out, hj, rfl⟩))
  have mkRejRo : ∀ {st_cur : M.σ} {evs_pref : List AllocEvent} {ArmEnv : List AllocEvent → Prop},
      st_cur = M.stepEvents evs_pref st →
      (∀ evs_a, ArmEnv evs_a → RunCoreEnv aEnvs g (evs_pref ++ evs_a)) →
      RejectKPlacedEnv (LibsignalCodeRoLoaded lsmpl) H A lim
        (fun _ _ st' => ∃ evs, ArmEnv evs ∧ st' = M.stepEvents evs st_cur)
        g s0 resStack Q Qp := by
    intro st_cur evs_pref ArmEnv hst_cur hCore sr st' g' rk hr ⟨evs_a, harm, hst'⟩
    have hst_tot : st' = M.stepEvents (evs_pref ++ evs_a) st := by
      rw [hst', hst_cur, ← M.stepEvents_append]
    exact sepWPp_mono_post
      (fun _ _ hp => hpost_mono_ro
        (runPostPlaced_of_joinPost hst_tot
          (fun evs_j hfj => SeqEnv.append (hCore evs_a harm) hfj) hp))
      (harms.joinRo hh hres_base hres64 hlr_ls (Or.inr ⟨g', rk, hr, rfl⟩))
  have mkJoinRo : ∀ {st_cur : M.σ} {evs_pref : List AllocEvent} {ArmEnv : List AllocEvent → Prop},
      st_cur = M.stepEvents evs_pref st →
      (∀ evs_a, ArmEnv evs_a → RunCoreEnv aEnvs g (evs_pref ++ evs_a)) →
      JoinKPlacedEnv (LibsignalCodeRoLoaded lsmpl) H A lim
        (fun _ _ st' => ∃ evs, ArmEnv evs ∧ st' = M.stepEvents evs st_cur)
        g s0 resStack Q Qp := by
    intro st_cur evs_pref ArmEnv hst_cur hCore sj st' g' out hj ⟨evs_a, harm, hst'⟩
    have hst_tot : st' = M.stepEvents (evs_pref ++ evs_a) st := by
      rw [hst', hst_cur, ← M.stepEvents_append]
    exact sepWPp_mono_post
      (fun _ _ hp => hpost_mono_ro
        (runPostPlaced_of_joinPost hst_tot
          (fun evs_j hfj => SeqEnv.append (hCore evs_a harm) hfj) hp))
      (harms.joinRo hh hres_base hres64 hlr_ls (Or.inl ⟨g', out, hj, rfl⟩))
  have hfits_core : FitsEnv M lim st (RunCoreEnv aEnvs g) := hfits.seq_left
  change SepWPp (runProgPlaced H) (s0.readReg64 .lr) s0
    (runEntryMemPlaced A lim st g s0 resStack) Q Qp (fun _ => ⌜False⌝)
  refine harms.pre hh hc hdrop hres hres64 he hfits_core.seq_left hpanic
    (mkRej (evs_pref := []) rfl fun _ h => SeqEnv.inl h) fun s evs₀ me hd hpre₀ => ?_
  have hsub_me : ∀ evs₁, RunArmAtMeEnv aEnvs g me evs₁ → RunDispatchEnv aEnvs g evs₁ :=
    fun _ h => dispatchEnv_of_armAtMe hd.1 h
  have hfits_arm : FitsEnv M lim (M.stepEvents evs₀ st) (RunArmAtMeEnv aEnvs g me) :=
    (hfits_core.seq_right hpre₀).mono hsub_me
  have hCore1 : ∀ evs₁, RunArmAtMeEnv aEnvs g me evs₁ → RunCoreEnv aEnvs g (evs₀ ++ evs₁) :=
    fun evs₁ h => SeqEnv.append hpre₀ (hsub_me evs₁ h)
  cases hcall : g.c with
  | keygen meK nK =>
    have htag : g.c.tag ≠ 0 := runRel_not_keygen he.1.rel he.1.parse
    rw [hcall] at htag
    exact absurd rfl htag
  | send peerV =>
    have hsub_s : ∀ evs₁, aEnvs.send g me peerV evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
      intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
    exact harms.send hh hc hdrop hres hres64 hspb he.1.toRoCl (dispatchFd_toRoCl hd) hcall
      (hfits_arm.mono hsub_s) hpanic
      (mkRejRo rfl fun evs₁ h => hCore1 evs₁ (hsub_s evs₁ h))
      (mkJoinRo rfl fun evs₁ h => hCore1 evs₁ (hsub_s evs₁ h))
  | init peerV dir =>
    cases me with
    | none =>
      have hsub_i0 :
          ∀ evs₁, aEnvs.init1 g .none peerV dir evs₁ → RunArmAtMeEnv aEnvs g .none evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
      exact harms.init1 hh hc hdrop hres hres64 he.1.toRoCl (dispatchFd_toRoCl hd) hcall
        (hfits_arm.mono hsub_i0) hpanic
        (mkRejRo rfl fun evs₁ h => hCore1 evs₁ (hsub_i0 evs₁ h))
        fun _ _ _ hi1 _ => (init1_impossible_of_none hd.1.toRoCl hi1.1).elim
    | some meV meG =>
      have hsub_is :
          ∀ evs₁,
            SeqEnv (aEnvs.init1 g (.some meV meG) peerV dir)
              (RunInit2ChainEnv aEnvs g meV peerV dir) evs₁ →
              RunArmAtMeEnv aEnvs g (.some meV meG) evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
      have hfits_i12 :
          FitsEnv M lim (M.stepEvents evs₀ st)
            (SeqEnv (aEnvs.init1 g (.some meV meG) peerV dir)
              (RunInit2ChainEnv aEnvs g meV peerV dir)) :=
        hfits_arm.mono hsub_is
      refine harms.init1 hh hc hdrop hres hres64 he.1.toRoCl (dispatchFd_toRoCl hd) hcall
        hfits_i12.seq_left hpanic
        (mkRejRo rfl fun evs₁ h1 => hCore1 evs₁ (hsub_is evs₁ (SeqEnv.inl h1)))
        fun s1 evs₁ d1 hi1 hinit1 => ?_
      have hst₂ : M.stepEvents evs₁ (M.stepEvents evs₀ st) = M.stepEvents (evs₀ ++ evs₁) st :=
        (M.stepEvents_append evs₀ evs₁ st).symm
      have hsub_d1 :
          ∀ evs₂,
            SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir) evs₂ →
              RunInit2ChainEnv aEnvs g meV peerV dir evs₂ :=
        fun _ h => init2ChainEnv_of_atInit1 hd.1.toRoCl hcall hi1.1 h
      have hfits_i23 :
          FitsEnv M lim (M.stepEvents evs₁ (M.stepEvents evs₀ st))
            (SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir)) :=
        (hfits_i12.seq_right hinit1).mono hsub_d1
      refine harms.init2 hh hc hdrop hres hres64 he.1.toRoCl hi1 hfits_i23.seq_left hpanic
        (mkRejRo hst₂ fun evs₂ h2 => by
          rw [List.append_assoc]
          exact hCore1 (evs₁ ++ evs₂)
            (hsub_is _ (SeqEnv.append hinit1 (hsub_d1 evs₂ (SeqEnv.inl h2)))))
        fun s2 evs₂ d2 hi2 hinit2 => ?_
      have hst₃ :
          M.stepEvents evs₂ (M.stepEvents evs₁ (M.stepEvents evs₀ st)) =
            M.stepEvents ((evs₀ ++ evs₁) ++ evs₂) st := by
        rw [hst₂, ← M.stepEvents_append]
      have hsub_d2 : ∀ evs₃, aEnvs.init3 g d2 evs₃ → RunInit3Env aEnvs g meV peerV dir evs₃ :=
        fun _ h => init3Env_of_atInit2 hd.1.toRoCl hcall hi2.1 h
      have hCore3 :
          ∀ evs₃, aEnvs.init3 g d2 evs₃ →
            RunCoreEnv aEnvs g (((evs₀ ++ evs₁) ++ evs₂) ++ evs₃) := by
        intro evs₃ h3
        simp only [List.append_assoc]
        exact hCore1 (evs₁ ++ (evs₂ ++ evs₃))
          (hsub_is _ (SeqEnv.append hinit1 (hsub_d1 (evs₂ ++ evs₃)
            (SeqEnv.append hinit2 (hsub_d2 evs₃ h3)))))
      exact harms.init3 hh hc hdrop hres hres64 hspb he.1.toRoCl hi2
        ((hfits_i23.seq_right hinit2).mono hsub_d2) hpanic
        (mkRejRo hst₃ hCore3) (mkJoinRo hst₃ hCore3)
  | recv peerV =>
    cases hstdin : g.i.stdin with
    | nil =>
      have hsub_r0 : ∀ evs₁, FreeOnlyEvs evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin] using h
      exact harms.recvBad hh hres_base hres64 he.1.toRoCl hd.1.toRoCl hcall (Or.inl hstdin)
        (mkRejRo rfl fun evs₁ h => hCore1 evs₁ (hsub_r0 evs₁ h))
    | cons t rest =>
      by_cases ht2 : t = 2#8
      · subst ht2
        have hsub_rw : ∀ evs₁, aEnvs.recvW g me peerV rest evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
          intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ↓reduceIte] using h
        exact harms.recvW hh hc htry hdrop hres hres64 hspb he.1 hd hcall hstdin
          (hfits_arm.mono hsub_rw) hpanic
          (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rw evs₁ h))
          (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_rw evs₁ h))
      · by_cases ht3 : t = 3#8
        · subst ht3
          have hsub_rp :
              ∀ evs₁, aEnvs.recvP g me peerV rest evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
            intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ht2, ↓reduceIte] using h
          exact harms.recvP hh hc hpksm hdrop hres hres64 hspb he.1 hd hcall hstdin
            (hfits_arm.mono hsub_rp) hpanic
            (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rp evs₁ h))
            (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_rp evs₁ h))
        · have hsub_rb : ∀ evs₁, FreeOnlyEvs evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
            intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ht2, ht3, ↓reduceIte] using h
          exact harms.recvBad hh hres_base hres64 he.1.toRoCl hd.1.toRoCl hcall
            (Or.inr ⟨t, rest, hstdin, ht2, ht3⟩)
            (mkRejRo rfl fun evs₁ h => hCore1 evs₁ (hsub_rb evs₁ h))

/-- `signal_session::run` (Block `579`) meets `withLsFrozen lsmpl (runSpecPlacedPreFd ...)` under
`[LibsignalPlacement]`. -/
theorem run_ok_withLsFrozen_placed_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsFrozenPlacedFd A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B (slotsOfSigPkFrozenPlaced A lim sEnvs S needs))
    (htry : subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (withLsFrozen lsmpl
        (runSpecPlacedPreFd (LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack)) :=
  subroutine_ok_withLsFrozen_of_plain
    (run_ok_frozen_placed_fd harms hh hc htry hpksm hres hres64)

/-- Cross-block transfer of `run_ok_withLsFrozen_placed_fd` from Block `579` (`runProgPlaced H`)
to any caller block `i < 624` (`callerProg`, e.g. Block `617` `mProgPlaced H`) under
`[LibsignalFullPlacement]`. -/
theorem run_ok_frozen_placed_at_block_fd [LibsignalFullPlacement]
    {M : AllocCostModel}
    {callerProg : Program} {i : Nat} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    (harms : RunArmsFrozenPlacedFd A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlacedFd A lim cEnvs H B (slotsOfSigPkFrozenPlaced A lim sEnvs S needs))
    (htry : subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfSigPkFrozenPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (_hi : i < 624 := by decide) :
    subroutine_ok callerProg (lsmpl.base 579)
      (runSpecPlacedPreFd (LibsignalFrozen lsmpl)
        A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack) := by
  have h579 : IsLsBlockProg (runProgPlaced H) 579 H := inferInstance
  have hfr := @ls_subroutine_ok_withLsFrozen_of_block_frc
    _ _ callerProg (runProgPlaced H) i 579 H hcaller h579 (lsmpl.base 579) _
    (run_ok_withLsFrozen_placed_fd harms hh hc htry hpksm hres hres64) (by decide)
  refine subroutine_ok_mono hfr ?_ (fun _ _ _ _ h => h)
  intro g R s0 hpre
  dsimp only [withLsFrozen]
  obtain ⟨_, hpre0⟩ := extract_withPreFdsGe3Closed hpre
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre0
  have hcomm :
      (runSpecPlacedPreFd (LibsignalFrozen lsmpl)
        A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗
        ⌜LibsignalFrozen lsmpl s0.mem⌝ ∗ R =
      ⌜LibsignalFrozen lsmpl s0.mem⌝ ∗
        ((runSpecPlacedPreFd (LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗ R) := by
    sep_ac_rfl
  rw [sepConj_assoc, hcomm, satisfies_pure_sepConj]
  exact ⟨hpre0.1.1, hpre⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudgetFd
