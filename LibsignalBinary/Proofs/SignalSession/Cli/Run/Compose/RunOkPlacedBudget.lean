/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `signal_session::run` Composition

Bundles the nine budget-threaded arm hop contracts (`RunArmsPlaced` / `RunArmsFrozenPlaced`) on
Block `579` (`signal_session::run`), assembles the sequential allocation-event envelope `RunEnv`
over `RunArmEnvs`, and proves `run_ok_placed`, `run_ok_frozen_placed`, cross-block transfers, and
envelope-monotonicity / `runSpecAnyPlaced` corollaries.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget

open Arm64 Arm64.Process ProofLib SepProp
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPl_111 lsmpl)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded ls_subroutine_ok_rocl_of_block withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RecordCodecs (decodeIdentityKey)
open CryptoVerification.SignalSession (Inputs)
open CryptoVerification.SignalSession.Cli (RunAnswer StoresGhost utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV RunCall addrParse cliIo cliWrOk inputOf runResAt)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtDispatchPlaced AtInit1Placed AtInit2Placed AtRunEntryPlaced Init1Data Init2Data MeAtDispatch
   PanicK PksmGhost RunNeeds RunSem Words32Eq addrValOf bundleFile exceptOpt readBundleV runFiles
   runProgPlaced runRel runRel_not_keygen sepWPp_mono_post)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets runNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.JPlacedBudget
  (RunHopJoinPlaced runPostPlaced_of_joinPost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget (RunHopPrePlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget (RunHopInit1Placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget (RunHopInit2Placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget (RunHopInit3Placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget (RunHopSendPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlacedBudget (RunHopRecvWPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
  (RunHopRecvBadPlaced RunHopRecvPPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv run_hop_dropSpeOwned_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (placed_onPanic_of_runPanic placed_post_of_runPost runEntryMemPlaced runEntry_of_placed_pre
   runPostPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (pksmSlotSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunCalleesPlaced RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (runSpecAnyPlaced runSpecPlaced)

/-! ## Section 1: Arm Envelope Bundle (`RunArmEnvs`) & Exact `RunEnv` Composition -/

/-- Per-arm allocation-event envelopes of `signal_session::run` (Block `579`). -/
structure RunArmEnvs where
  pre : RunCall → List AllocEvent → Prop
  init1 : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop
  init2 : RunCall → Init1Data → List AllocEvent → Prop
  init3 : RunCall → Init2Data → List AllocEvent → Prop
  send : RunCall → MeAtDispatch → AddrV → List AllocEvent → Prop
  recvW : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop
  pksmTryFrom : PksmGhost → List AllocEvent → Prop
  recvP : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop

/-- Bundle of the 9 budget-threaded relocatable (`[LibsignalPlacement]`) arm hop contracts of
`signal_session::run` (Block `579`). -/
structure RunArmsPlaced [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs) (aEnvs : RunArmEnvs)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) :
    Prop where
  join : RunHopJoinPlaced CodeOk A lim sEnvs H B S needs resStack
  pre : RunHopPrePlaced CodeOk A lim cEnvs sEnvs aEnvs.pre H B S needs resStack
  init1 : RunHopInit1Placed CodeOk A lim cEnvs sEnvs aEnvs.init1 H B S needs resStack
  init2 : RunHopInit2Placed CodeOk A lim cEnvs sEnvs aEnvs.init2 H B S needs resStack
  init3 : RunHopInit3Placed CodeOk A lim cEnvs sEnvs aEnvs.init3 H B S needs resStack
  send : RunHopSendPlaced CodeOk A lim cEnvs sEnvs aEnvs.send H B S needs resStack
  recvW : RunHopRecvWPlaced CodeOk A lim cEnvs sEnvs aEnvs.recvW H B S needs resStack
  recvP :
    RunHopRecvPPlaced CodeOk A lim cEnvs sEnvs aEnvs.pksmTryFrom aEnvs.recvP H B S
      needs resStack
  recvBad : RunHopRecvBadPlaced CodeOk A lim sEnvs H B S needs resStack

/-- Allocation-event envelope of Arm `R1c` (`init3`) once `readBundleV` succeeds on `(dir, peerV)`. -/
def RunInit3Env (aEnvs : RunArmEnvs) (g : RunCall) (meV peerV : AddrV)
    (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  match readBundleV (runFiles g.i) dir peerV.device with
  | none => False
  | some bundle =>
    ∃ d2 : Init2Data,
      d2.peerV = peerV ∧ d2.dir = dir ∧ d2.meV = meV ∧ d2.bundle = bundle ∧
      d2.peerG.val = addrValOf peerV ∧ d2.meG.val = addrValOf meV ∧
      d2.spkSigPtr ≠ 0 ∧ d2.kpkSigPtr ≠ 0 ∧ d2.kpkPtr ≠ 0 ∧
      aEnvs.init3 g d2 evs

/-- Sequential allocation-event envelope of Arms `R1b` (`init2`) followed by `R1c` (`init3`) once
`identity-key` is read and decoded. -/
def RunInit2ChainEnv (aEnvs : RunArmEnvs) (g : RunCall) (meV peerV : AddrV)
    (dir : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  match bundleFile (runFiles g.i) dir "identity-key" with
  | none => False
  | some ikB =>
    match exceptOpt (decodeIdentityKey ikB) with
    | none => False
    | some idKey =>
      ∃ d1 : Init1Data,
        d1.peerV = peerV ∧ d1.dir = dir ∧ d1.meV = meV ∧ d1.idKey = idKey ∧
        d1.peerG.val = addrValOf peerV ∧ d1.meG.val = addrValOf meV ∧
        Words32Eq idKey.publicKey.bytes.toList d1.ikW0 d1.ikW1 d1.ikW2 d1.ikW3 ∧
        SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir) evs

/-- Post-dispatch (`R+0x214`) allocation-event envelope at own-address ghost `me : MeAtDispatch`. -/
def RunArmAtMeEnv (aEnvs : RunArmEnvs) (g : RunCall) (me : MeAtDispatch)
    (evs : List AllocEvent) : Prop :=
  match g.c with
  | .keygen _ _ => False
  | .send peerV => aEnvs.send g me peerV evs
  | .init peerV dir =>
    match me with
    | .none => aEnvs.init1 g .none peerV dir evs
    | .some meV meG =>
      SeqEnv (aEnvs.init1 g (.some meV meG) peerV dir)
        (RunInit2ChainEnv aEnvs g meV peerV dir) evs
  | .recv peerV =>
    match g.i.stdin with
    | [] => FreeOnlyEvs evs
    | t :: rest =>
      if t = 2#8 then aEnvs.recvW g me peerV rest evs
      else if t = 3#8 then aEnvs.recvP g me peerV rest evs
      else FreeOnlyEvs evs

/-- Post-dispatch (`R+0x214`) allocation-event envelope determined by `Stores::identity.own`. -/
def RunDispatchEnv (aEnvs : RunArmEnvs) (g : RunCall) (evs : List AllocEvent) : Prop :=
  match StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "address") with
  | .error () => False
  | .ok ownB =>
    match addrParse uuidTryParse ownB with
    | none => RunArmAtMeEnv aEnvs g .none evs
    | some meV =>
      ∃ meG : AddrGhost,
        meG.device = meV.device ∧
        meG.name.bytes = meV.name ∧
        meG.name.cap = BitVec.ofNat 64 meV.name.length ∧
        RunArmAtMeEnv aEnvs g (.some meV meG) evs

/-- Pre-epilogue (`R0` followed by dispatch arm) allocation-event envelope of `signal_session::run`. -/
def RunCoreEnv (aEnvs : RunArmEnvs) (g : RunCall) (evs : List AllocEvent) : Prop :=
  SeqEnv (aEnvs.pre g) (RunDispatchEnv aEnvs g) evs

/-- Exact end-to-end allocation-event envelope of `signal_session::run` (Block `579`), composing
`RunCoreEnv aEnvs g` with the pure-deallocation epilogue (`FreeOnlyEvs`) of Arm `J`. -/
def RunEnv (aEnvs : RunArmEnvs) (g : RunCall) (evs : List AllocEvent) : Prop :=
  SeqEnv (RunCoreEnv aEnvs g) FreeOnlyEvs evs

/-! ## Section 2: Internal Seam Projection Lemmas -/

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

/-! ## Section 3: Top-Level `run_ok_placed` & Cross-Block Transfers -/

/-- `signal_session::run` (Block `579`) meets budget-threaded `runSpecPlaced` at `runRel S` and
`RunEnv aEnvs` under `[LibsignalPlacement]`. -/
theorem run_ok_placed [LibsignalPlacement] {M : AllocCostModel}
    {CodeOk : Memory → Prop} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsPlaced CodeOk A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (runSpecPlaced CodeOk A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack) := by
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨g, st⟩ R s0 hpc hrun hpre hsp
  have ⟨hspb, hlr_ls⟩ : resStack ≤ s0.sp.toNat ∧ LsRetAddr624 (s0.readReg64 .x30) := by
    have hpre' := hpre
    simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    rcases hpre' with ⟨⟨_, _, _, _, _, _, _, _, _, _, hspb, _, hlr_ls⟩, _⟩
    exact ⟨hspb, hlr_ls⟩
  rcases runEntry_of_placed_pre hpc hrun hpre hsp with ⟨he, hfits, hmem⟩
  refine ⟨runEntryMemPlaced A lim st g s0 resStack, hmem, ?_⟩
  let Q : State → SepProp → Prop := fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlaced CodeOk A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).post
          (g, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
  let Qp : State → SepProp → Prop := fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlaced CodeOk A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).onPanic
          (g, st) s0 sf ∗ R)
  have hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim :=
    run_hop_dropSpeOwned_placed hh.alloc
  have hpanic : PanicK g s0 Qp := fun _ _ hpan hmf =>
    placed_onPanic_of_runPanic (CodeOk := CodeOk) (S := S) (A := A) (lim := lim)
      (RunEnv := RunEnv aEnvs) (st := st) (resStack := resStack) hpan hmf
  have hpost_mono :
      ∀ {sf Pf}, runPostPlaced CodeOk A lim (RunEnv aEnvs) g st resStack s0 sf Pf → Q sf Pf :=
    fun hp => ⟨fun hmf => (placed_post_of_runPost he.fs he.stdout hp hmf).1, hp.2.1, hp.2.2.1⟩
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
    fun _ h => dispatchEnv_of_armAtMe hd h
  have hfits_arm : FitsEnv M lim (M.stepEvents evs₀ st) (RunArmAtMeEnv aEnvs g me) :=
    (hfits_core.seq_right hpre₀).mono hsub_me
  have hCore1 : ∀ evs₁, RunArmAtMeEnv aEnvs g me evs₁ → RunCoreEnv aEnvs g (evs₀ ++ evs₁) :=
    fun evs₁ h => SeqEnv.append hpre₀ (hsub_me evs₁ h)
  cases hcall : g.c with
  | keygen meK nK =>
    have htag : g.c.tag ≠ 0 := runRel_not_keygen he.rel he.parse
    rw [hcall] at htag
    exact absurd rfl htag
  | send peerV =>
    have hsub_s : ∀ evs₁, aEnvs.send g me peerV evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
      intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
    exact harms.send hh hc hdrop hres hres64 hspb he hd hcall (hfits_arm.mono hsub_s) hpanic
      (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_s evs₁ h))
      (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_s evs₁ h))
  | init peerV dir =>
    cases me with
    | none =>
      have hsub_i0 : ∀ evs₁, aEnvs.init1 g .none peerV dir evs₁ → RunArmAtMeEnv aEnvs g .none evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
      exact harms.init1 hh hc hdrop hres hres64 he hd hcall (hfits_arm.mono hsub_i0) hpanic
        (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_i0 evs₁ h))
        fun _ _ _ hi1 _ => (init1_impossible_of_none hd hi1).elim
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
      refine harms.init1 hh hc hdrop hres hres64 he hd hcall hfits_i12.seq_left hpanic
        (mkRej rfl fun evs₁ h1 => hCore1 evs₁ (hsub_is evs₁ (SeqEnv.inl h1)))
        fun s1 evs₁ d1 hi1 hinit1 => ?_
      have hst₂ : M.stepEvents evs₁ (M.stepEvents evs₀ st) = M.stepEvents (evs₀ ++ evs₁) st :=
        (M.stepEvents_append evs₀ evs₁ st).symm
      have hsub_d1 :
          ∀ evs₂,
            SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir) evs₂ →
              RunInit2ChainEnv aEnvs g meV peerV dir evs₂ :=
        fun _ h => init2ChainEnv_of_atInit1 hd hcall hi1 h
      have hfits_i23 :
          FitsEnv M lim (M.stepEvents evs₁ (M.stepEvents evs₀ st))
            (SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir)) :=
        (hfits_i12.seq_right hinit1).mono hsub_d1
      refine harms.init2 hh hc hdrop hres hres64 he hi1 hfits_i23.seq_left hpanic
        (mkRej hst₂ fun evs₂ h2 => by
          rw [List.append_assoc]
          exact hCore1 (evs₁ ++ evs₂) (hsub_is _ (SeqEnv.append hinit1 (hsub_d1 evs₂ (SeqEnv.inl h2)))))
        fun s2 evs₂ d2 hi2 hinit2 => ?_
      have hst₃ :
          M.stepEvents evs₂ (M.stepEvents evs₁ (M.stepEvents evs₀ st)) =
            M.stepEvents ((evs₀ ++ evs₁) ++ evs₂) st := by
        rw [hst₂, ← M.stepEvents_append]
      have hsub_d2 : ∀ evs₃, aEnvs.init3 g d2 evs₃ → RunInit3Env aEnvs g meV peerV dir evs₃ :=
        fun _ h => init3Env_of_atInit2 hd hcall hi2 h
      have hCore3 :
          ∀ evs₃, aEnvs.init3 g d2 evs₃ → RunCoreEnv aEnvs g (((evs₀ ++ evs₁) ++ evs₂) ++ evs₃) := by
        intro evs₃ h3
        simp only [List.append_assoc]
        exact hCore1 (evs₁ ++ (evs₂ ++ evs₃))
          (hsub_is _ (SeqEnv.append hinit1 (hsub_d1 (evs₂ ++ evs₃)
            (SeqEnv.append hinit2 (hsub_d2 evs₃ h3)))))
      exact harms.init3 hh hc hdrop hres hres64 hspb he hi2
        ((hfits_i23.seq_right hinit2).mono hsub_d2) hpanic
        (mkRej hst₃ hCore3) (mkJoin hst₃ hCore3)
  | recv peerV =>
    cases hstdin : g.i.stdin with
    | nil =>
      have hsub_r0 : ∀ evs₁, FreeOnlyEvs evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin] using h
      exact harms.recvBad hh hres hres64 he hd hcall (Or.inl hstdin)
        (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_r0 evs₁ h))
    | cons t rest =>
      by_cases ht2 : t = 2#8
      · subst ht2
        have hsub_rw : ∀ evs₁, aEnvs.recvW g me peerV rest evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
          intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ↓reduceIte] using h
        exact harms.recvW hh hc hdrop hres hres64 hspb he hd hcall hstdin
          (hfits_arm.mono hsub_rw) hpanic
          (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rw evs₁ h))
          (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_rw evs₁ h))
      · by_cases ht3 : t = 3#8
        · subst ht3
          have hsub_rp : ∀ evs₁, aEnvs.recvP g me peerV rest evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
            intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ht2, ↓reduceIte] using h
          exact harms.recvP hh hc hpksm hdrop hres hres64 hspb he hd hcall hstdin
            (hfits_arm.mono hsub_rp) hpanic
            (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rp evs₁ h))
            (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_rp evs₁ h))
        · have hsub_rb : ∀ evs₁, FreeOnlyEvs evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
            intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ht2, ht3, ↓reduceIte] using h
          exact harms.recvBad hh hres hres64 he hd hcall
            (Or.inr ⟨t, rest, hstdin, ht2, ht3⟩)
            (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rb evs₁ h))

/-- `signal_session::run` (Block `579`) meets `withLsCodeRoLoaded (runSpecPlaced ...)` under
`[LibsignalPlacement]`, enabling cross-block transfer via `ls_subroutine_ok_rocl_of_block`. -/
theorem run_ok_withLsCodeRoLoaded_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (withLsCodeRoLoaded lsmpl
        (runSpecPlaced (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs)
          uuidTryParse (runRel S) cliWrOk resStack)) := by
  refine subroutine_ok_mono (run_ok_placed harms hh hc hpksm hres hres64) ?_ (fun _ _ _ _ h => h)
  intro g R s0 hpre
  exact Satisfies.drop_mid (by
    simpa only [withLsCodeRoLoaded, sepConj_assoc] using hpre)

/-- Cross-block transfer of `run_ok_withLsCodeRoLoaded_placed` from Block `579` (`runProgPlaced H`)
to any caller block `i < 619` (`callerProg`, e.g. Block `617` `mProgPlaced H`). -/
theorem run_ok_placed_at_block [LibsignalPlacement] {M : AllocCostModel}
    {callerProg : Program} {i : Nat} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    (harms : RunArmsPlaced (LibsignalCodeRoLoaded lsmpl) A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 579)
      (runSpecPlaced (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs)
        uuidTryParse (runRel S) cliWrOk resStack) := by
  have h579 : IsLsBlockProg (runProgPlaced H) 579 H := inferInstance
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    (runProgPlaced H) i 579 H hcaller h579 (lsmpl.base 579) _
    (run_ok_withLsCodeRoLoaded_placed harms hh hc hpksm hres hres64)
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl ?_ ?_
  · intro g R s0 hpre
    dsimp only [withLsRoCl]
    have hpre' := hpre
    simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    have hcomm :
        (runSpecPlaced (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs)
          uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗
          ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ R =
        ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗
          ((runSpecPlaced (LibsignalCodeRoLoaded lsmpl) A lim (RunEnv aEnvs)
            uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗ R) := by
      sep_ac_rfl
    rw [sepConj_assoc, hcomm, satisfies_pure_sepConj]
    exact ⟨hpre'.1.1, hpre⟩
  · intro g R s0 sf hpost
    dsimp only [withLsRoCl] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2

/-- Envelope monotonicity of `runSpecPlaced`: any coarser envelope `Env₂` containing `Env₁`
(`∀ g evs, Env₁ g evs → Env₂ g evs`) inherits `subroutine_ok` (`FitsEnv` is contravariant in
`pre` and `Env` is covariant in `post`). -/
theorem subroutine_ok_runSpecPlaced_mono_env [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {entry : BitVec 64} {CodeOk : Memory → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env₁ Env₂ : RunCall → List AllocEvent → Prop}
    {uuidParse : CryptoVerification.LibsignalTripleRatchetRepr.UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (hsub : ∀ g evs, Env₁ g evs → Env₂ g evs)
    (hok : subroutine_ok P entry (runSpecPlaced CodeOk A lim Env₁ uuidParse Run wrOk resStack)) :
    subroutine_ok P entry (runSpecPlaced CodeOk A lim Env₂ uuidParse Run wrOk resStack) := by
  refine subroutine_ok_mono hok ?_ ?_ (fun _ _ _ _ hp => hp)
  · rintro ⟨g, st⟩ R s0 hpre
    simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hc, hr, hp, hx0, hx1, hx2, hx3, hx4, hfs, hout, hspb, hfits, hlr⟩, hmem⟩
    exact ⟨⟨hc, hr, hp, hx0, hx1, hx2, hx3, hx4, hfs, hout, hspb, hfits.mono (hsub g), hlr⟩, hmem⟩
  · rintro ⟨g, st⟩ R s0 sf hpost
    dsimp only [runSpecPlaced] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨evs, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hsub g evs hpost.1.1, hpost.1.2⟩, hpost.2⟩

/-- Specialize `runSpecPlaced` to the envelope-erased `runSpecAnyPlaced` whenever `Env g` fits at
every `(g, st)`. -/
theorem subroutine_ok_runSpecAnyPlaced_of_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Program} {entry : BitVec 64} {CodeOk : Memory → Prop}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : RunCall → List AllocEvent → Prop}
    {uuidParse : CryptoVerification.LibsignalTripleRatchetRepr.UuidParser}
    {Run : Inputs → RunAnswer → Prop} {wrOk : List (BitVec 8) → Prop} {resStack : Nat}
    (hfits : ∀ g st, FitsEnv M lim st (Env g))
    (hok : subroutine_ok P entry (runSpecPlaced CodeOk A lim Env uuidParse Run wrOk resStack)) :
    subroutine_ok P entry (runSpecAnyPlaced CodeOk A lim uuidParse Run wrOk resStack) := by
  refine subroutine_ok_mono hok ?_ ?_ (fun _ _ _ _ hp => hp)
  · rintro ⟨g, st⟩ R s0 hpre
    simp only [runSpecAnyPlaced, runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hc, hr, hp, hx0, hx1, hx2, hx3, hx4, hfs, hout, hspb, hlr⟩, hmem⟩
    exact ⟨⟨hc, hr, hp, hx0, hx1, hx2, hx3, hx4, hfs, hout, hspb, hfits g st, hlr⟩, hmem⟩
  · rintro ⟨g, st⟩ R s0 sf hpost
    dsimp only [runSpecPlaced, runSpecAnyPlaced] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨evs, hpost⟩
    refine ⟨M.stepEvents evs st, ?_⟩
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.2, hpost.2⟩


/-! ## Section 4: `LibsignalFrozen` / `[LibsignalFullPlacement]` Composition -/

/-- Bundle of the budget-threaded arm hop contracts of `signal_session::run` (Block `579`)
upgraded to `LibsignalFrozen lsmpl` at `slotsOfSigPkFrozenPlaced` (with `init1..3`, `send`, and
`recvBad` proved at `LibsignalCodeRoLoaded lsmpl` and lifted via `toRoCl` + `joinRo`). -/
structure RunArmsFrozenPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs) (aEnvs : RunArmEnvs)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) :
    Prop where
  join : RunHopJoinPlaced (CryptoVerification.LibsignalFrozen lsmpl)
    A lim sEnvs H B S needs resStack
  joinRo : RunHopJoinPlaced (LibsignalCodeRoLoaded lsmpl) A lim sEnvs H B S needs resStack
  pre : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget.RunHopPrePlacedOf
    (CryptoVerification.LibsignalFrozen lsmpl) A lim cEnvs aEnvs.pre H B S
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    resStack
  init1 : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget.RunHopInit1PlacedOf
    (LibsignalCodeRoLoaded lsmpl) A lim cEnvs aEnvs.init1 H B S
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    resStack
  init2 : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget.RunHopInit2PlacedOf
    (LibsignalCodeRoLoaded lsmpl) A lim cEnvs aEnvs.init2 H B S
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    resStack
  init3 : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget.RunHopInit3PlacedOf
    (LibsignalCodeRoLoaded lsmpl) A lim cEnvs aEnvs.init3 H B S
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    resStack
  send : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget.RunHopSendPlacedOf
    (LibsignalCodeRoLoaded lsmpl) A lim cEnvs aEnvs.send H B S
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    resStack
  recvW : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlacedBudget.RunHopRecvWPlacedOf
    (CryptoVerification.LibsignalFrozen lsmpl) A lim cEnvs aEnvs.recvW H B S
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    resStack
  recvP : LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget.RunHopRecvPPlacedOf
    (CryptoVerification.LibsignalFrozen lsmpl) A lim cEnvs
    aEnvs.pksmTryFrom aEnvs.recvP H B S
    (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
      A lim sEnvs S needs)
    resStack
  recvBad : RunHopRecvBadPlaced (LibsignalCodeRoLoaded lsmpl) A lim sEnvs H B S needs resStack

/-- `signal_session::run` (Block `579`) meets budget-threaded `runSpecPlaced (LibsignalFrozen lsmpl)`
at `slotsOfSigPkFrozenPlaced` under `[LibsignalPlacement]`. -/
theorem run_ok_frozen_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsFrozenPlaced A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (runSpecPlaced (CryptoVerification.LibsignalFrozen lsmpl)
        A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack) := by
  have hres_base : runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack := hres
  apply subroutine_ok_of_sepWPp_init
  rintro ⟨g, st⟩ R s0 hpc hrun hpre hsp
  have ⟨hspb, hlr_ls⟩ : resStack ≤ s0.sp.toNat ∧ LsRetAddr624 (s0.readReg64 .x30) := by
    have hpre' := hpre
    simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
    rcases hpre' with ⟨⟨_, _, _, _, _, _, _, _, _, _, hspb, _, hlr_ls⟩, _⟩
    exact ⟨hspb, hlr_ls⟩
  rcases runEntry_of_placed_pre hpc hrun hpre hsp with ⟨he, hfits, hmem⟩
  refine ⟨runEntryMemPlaced A lim st g s0 resStack, hmem, ?_⟩
  let Q : State → SepProp → Prop := fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlaced (CryptoVerification.LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).post
          (g, st) s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf
  let Qp : State → SepProp → Prop := fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (runSpecPlaced (CryptoVerification.LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).onPanic
          (g, st) s0 sf ∗ R)
  have hdrop : DropSpeOwnedOkAtBlock (runProgPlaced H) A lim :=
    run_hop_dropSpeOwned_placed hh.alloc
  have hpanic : PanicK g s0 Qp := fun _ _ hpan hmf =>
    placed_onPanic_of_runPanic
      (CodeOk := CryptoVerification.LibsignalFrozen lsmpl)
      (S := S) (A := A) (lim := lim) (RunEnv := RunEnv aEnvs) (st := st) (resStack := resStack)
      hpan hmf
  have hpost_mono :
      ∀ {sf Pf},
        runPostPlaced (CryptoVerification.LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) g st resStack s0 sf Pf → Q sf Pf :=
    fun hp => ⟨fun hmf => (placed_post_of_runPost he.fs he.stdout hp hmf).1, hp.2.1, hp.2.2.1⟩
  have hpost_mono_ro :
      ∀ {sf Pf},
        runPostPlaced (LibsignalCodeRoLoaded lsmpl)
          A lim (RunEnv aEnvs) g st resStack s0 sf Pf → Q sf Pf :=
    fun hp => ⟨fun hmf => (placed_post_of_runPost (S := S) he.fs he.stdout hp hmf).1, hp.2.1, hp.2.2.1⟩
  have mkRej : ∀ {st_cur : M.σ} {evs_pref : List AllocEvent} {ArmEnv : List AllocEvent → Prop},
      st_cur = M.stepEvents evs_pref st →
      (∀ evs_a, ArmEnv evs_a → RunCoreEnv aEnvs g (evs_pref ++ evs_a)) →
      RejectKPlacedEnv (CryptoVerification.LibsignalFrozen lsmpl) H A lim
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
      JoinKPlacedEnv (CryptoVerification.LibsignalFrozen lsmpl) H A lim
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
    fun _ h => dispatchEnv_of_armAtMe hd h
  have hfits_arm : FitsEnv M lim (M.stepEvents evs₀ st) (RunArmAtMeEnv aEnvs g me) :=
    (hfits_core.seq_right hpre₀).mono hsub_me
  have hCore1 : ∀ evs₁, RunArmAtMeEnv aEnvs g me evs₁ → RunCoreEnv aEnvs g (evs₀ ++ evs₁) :=
    fun evs₁ h => SeqEnv.append hpre₀ (hsub_me evs₁ h)
  cases hcall : g.c with
  | keygen meK nK =>
    have htag : g.c.tag ≠ 0 := runRel_not_keygen he.rel he.parse
    rw [hcall] at htag
    exact absurd rfl htag
  | send peerV =>
    have hsub_s : ∀ evs₁, aEnvs.send g me peerV evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
      intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
    exact harms.send hh hc hdrop hres hres64 hspb he.toRoCl hd.toRoCl hcall (hfits_arm.mono hsub_s)
      hpanic
      (mkRejRo rfl fun evs₁ h => hCore1 evs₁ (hsub_s evs₁ h))
      (mkJoinRo rfl fun evs₁ h => hCore1 evs₁ (hsub_s evs₁ h))
  | init peerV dir =>
    cases me with
    | none =>
      have hsub_i0 : ∀ evs₁, aEnvs.init1 g .none peerV dir evs₁ → RunArmAtMeEnv aEnvs g .none evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall] using h
      exact harms.init1 hh hc hdrop hres hres64 he.toRoCl hd.toRoCl hcall (hfits_arm.mono hsub_i0)
        hpanic
        (mkRejRo rfl fun evs₁ h => hCore1 evs₁ (hsub_i0 evs₁ h))
        fun _ _ _ hi1 _ => (init1_impossible_of_none hd.toRoCl hi1).elim
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
      refine harms.init1 hh hc hdrop hres hres64 he.toRoCl hd.toRoCl hcall hfits_i12.seq_left hpanic
        (mkRejRo rfl fun evs₁ h1 => hCore1 evs₁ (hsub_is evs₁ (SeqEnv.inl h1)))
        fun s1 evs₁ d1 hi1 hinit1 => ?_
      have hst₂ : M.stepEvents evs₁ (M.stepEvents evs₀ st) = M.stepEvents (evs₀ ++ evs₁) st :=
        (M.stepEvents_append evs₀ evs₁ st).symm
      have hsub_d1 :
          ∀ evs₂,
            SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir) evs₂ →
              RunInit2ChainEnv aEnvs g meV peerV dir evs₂ :=
        fun _ h => init2ChainEnv_of_atInit1 hd.toRoCl hcall hi1 h
      have hfits_i23 :
          FitsEnv M lim (M.stepEvents evs₁ (M.stepEvents evs₀ st))
            (SeqEnv (aEnvs.init2 g d1) (RunInit3Env aEnvs g meV peerV dir)) :=
        (hfits_i12.seq_right hinit1).mono hsub_d1
      refine harms.init2 hh hc hdrop hres hres64 he.toRoCl hi1 hfits_i23.seq_left hpanic
        (mkRejRo hst₂ fun evs₂ h2 => by
          rw [List.append_assoc]
          exact hCore1 (evs₁ ++ evs₂) (hsub_is _ (SeqEnv.append hinit1 (hsub_d1 evs₂ (SeqEnv.inl h2)))))
        fun s2 evs₂ d2 hi2 hinit2 => ?_
      have hst₃ :
          M.stepEvents evs₂ (M.stepEvents evs₁ (M.stepEvents evs₀ st)) =
            M.stepEvents ((evs₀ ++ evs₁) ++ evs₂) st := by
        rw [hst₂, ← M.stepEvents_append]
      have hsub_d2 : ∀ evs₃, aEnvs.init3 g d2 evs₃ → RunInit3Env aEnvs g meV peerV dir evs₃ :=
        fun _ h => init3Env_of_atInit2 hd.toRoCl hcall hi2 h
      have hCore3 :
          ∀ evs₃, aEnvs.init3 g d2 evs₃ → RunCoreEnv aEnvs g (((evs₀ ++ evs₁) ++ evs₂) ++ evs₃) := by
        intro evs₃ h3
        simp only [List.append_assoc]
        exact hCore1 (evs₁ ++ (evs₂ ++ evs₃))
          (hsub_is _ (SeqEnv.append hinit1 (hsub_d1 (evs₂ ++ evs₃)
            (SeqEnv.append hinit2 (hsub_d2 evs₃ h3)))))
      exact harms.init3 hh hc hdrop hres hres64 hspb he.toRoCl hi2
        ((hfits_i23.seq_right hinit2).mono hsub_d2) hpanic
        (mkRejRo hst₃ hCore3) (mkJoinRo hst₃ hCore3)
  | recv peerV =>
    cases hstdin : g.i.stdin with
    | nil =>
      have hsub_r0 : ∀ evs₁, FreeOnlyEvs evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
        intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin] using h
      exact harms.recvBad hh hres_base hres64 he.toRoCl hd.toRoCl hcall (Or.inl hstdin)
        (mkRejRo rfl fun evs₁ h => hCore1 evs₁ (hsub_r0 evs₁ h))
    | cons t rest =>
      by_cases ht2 : t = 2#8
      · subst ht2
        have hsub_rw : ∀ evs₁, aEnvs.recvW g me peerV rest evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
          intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ↓reduceIte] using h
        exact harms.recvW hh hc hdrop hres hres64 hspb he hd hcall hstdin
          (hfits_arm.mono hsub_rw) hpanic
          (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rw evs₁ h))
          (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_rw evs₁ h))
      · by_cases ht3 : t = 3#8
        · subst ht3
          have hsub_rp : ∀ evs₁, aEnvs.recvP g me peerV rest evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
            intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ht2, ↓reduceIte] using h
          exact harms.recvP hh hc hpksm hdrop hres hres64 hspb he hd hcall hstdin
            (hfits_arm.mono hsub_rp) hpanic
            (mkRej rfl fun evs₁ h => hCore1 evs₁ (hsub_rp evs₁ h))
            (mkJoin rfl fun evs₁ h => hCore1 evs₁ (hsub_rp evs₁ h))
        · have hsub_rb : ∀ evs₁, FreeOnlyEvs evs₁ → RunArmAtMeEnv aEnvs g me evs₁ := by
            intro evs₁ h; simpa only [RunArmAtMeEnv, hcall, hstdin, ht2, ht3, ↓reduceIte] using h
          exact harms.recvBad hh hres_base hres64 he.toRoCl hd.toRoCl hcall
            (Or.inr ⟨t, rest, hstdin, ht2, ht3⟩)
            (mkRejRo rfl fun evs₁ h => hCore1 evs₁ (hsub_rb evs₁ h))

/-- `signal_session::run` (Block `579`) meets `withLsFrozen lsmpl (runSpecPlaced ...)` under
`[LibsignalPlacement]`. -/
theorem run_ok_withLsFrozen_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    (harms : RunArmsFrozenPlaced A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63) :
    subroutine_ok (runProgPlaced H) (lsmpl.base 579)
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (runSpecPlaced (CryptoVerification.LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack)) :=
  LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.subroutine_ok_withLsFrozen_of_plain
    (run_ok_frozen_placed harms hh hc hpksm hres hres64)

/-- Cross-block transfer of `run_ok_withLsFrozen_placed` from Block `579` (`runProgPlaced H`)
to any caller block `i < 624` (`callerProg`, e.g. Block `617` `mProgPlaced H`) under
`[LibsignalFullPlacement]`. -/
theorem run_ok_frozen_placed_at_block [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    {callerProg : Program} {i : Nat} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {cEnvs : RunCalleesEnvs} {sEnvs : RunSlotEnvs} {aEnvs : RunArmEnvs}
    {H : LibsignalHooks} {B : RunBudgets} {S : RunSem} {needs : RunNeeds} {resStack : Nat}
    [hcaller : IsLsBlockProg callerProg i H]
    (harms : RunArmsFrozenPlaced A lim cEnvs sEnvs aEnvs H B S needs resStack)
    (hh : RunHooksPlaced A lim H)
    (hc : RunCalleesPlaced A lim cEnvs H B
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs))
    (hpksm : subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlaced M A lim aEnvs.pksmTryFrom S))
    (hres : runNeed B
      (LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget.slotsOfSigPkFrozenPlaced
        A lim sEnvs S needs) ≤ resStack)
    (hres64 : resStack ≤ 2 ^ 63)
    (_hi : i < 624 := by decide) :
    subroutine_ok callerProg (lsmpl.base 579)
      (runSpecPlaced (CryptoVerification.LibsignalFrozen lsmpl)
        A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack) := by
  have h579 : IsLsBlockProg (runProgPlaced H) 579 H := inferInstance
  have hfr := @LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.ls_subroutine_ok_withLsFrozen_of_block_frc
    _ _ callerProg (runProgPlaced H) i 579 H hcaller h579 (lsmpl.base 579) _
    (run_ok_withLsFrozen_placed harms hh hc hpksm hres hres64) (by decide)
  refine subroutine_ok_mono hfr ?_ (fun _ _ _ _ h => h)
  intro g R s0 hpre
  dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsFrozen]
  have hpre' := hpre
  simp only [runSpecPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  have hcomm :
      (runSpecPlaced (CryptoVerification.LibsignalFrozen lsmpl)
        A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗
        ⌜CryptoVerification.LibsignalFrozen lsmpl s0.mem⌝ ∗ R =
      ⌜CryptoVerification.LibsignalFrozen lsmpl s0.mem⌝ ∗
        ((runSpecPlaced (CryptoVerification.LibsignalFrozen lsmpl)
          A lim (RunEnv aEnvs) uuidTryParse (runRel S) cliWrOk resStack).pre g s0 ∗ R) := by
    sep_ac_rfl
  rw [sepConj_assoc, hcomm, satisfies_pure_sepConj]
  exact ⟨hpre'.1.1, hpre⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget
