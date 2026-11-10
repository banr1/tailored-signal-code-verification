/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1aPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1bPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1cPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3aPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Arm Hop Specifications for `signal_session::run`

Defines `Ok`-branch `fs`-preserving wire-decoder contracts (`tryFromPlacedSpecOkFs` and
`pksmSlotSpecPlacedOkFs`) and the file-descriptor-preserving (`FdsGe3Closed`) hop specifications
`RunHopPrePlacedFd` through `RunHopRecvPPlacedFd` on Block `579`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPl_111 lsmpl)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyTryFromStack)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet (TryFromGhost)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall)
open CryptoVerification.SignalSession.Cli.RunCompose
  (AtRunEntryPlaced Init1Data Init2Data MeAtDispatch PanicK PksmGhost RunNeeds RunSem
   pksmResAt runProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets RunSlots runNeed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.HopsPlacedBudget
  (JoinKPlacedEnv RejectKPlacedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
  (RunSlotEnvs slotsOfPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedBudget
  (dispatchMemPlaced init1MemPlaced init2MemPlaced runEntryMemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.StatesPlacedFd
  (AtDispatchPlacedFd AtInit1PlacedFd AtInit2PlacedFd AtRunEntryPlacedFd)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DropSpeOwnedPlacedBudget
  (DropSpeOwnedOkAtBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (pksmSlotSpecPlaced pksmTryFromSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
  (RunCalleesEnvs RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudgetFd
  (RunCalleesPlacedFd)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget (tryFromPlacedSpec)

/-! ## `Ok`-Branch `fs`-Preserving Wire-Decoder Specifications -/

/-- Strengthens `tryFromPlacedSpec` (Block `85`, `SignalMessage::try_from`) with `(SignalMessage.tryFrom protoSignalCodec x.bytes).isOk = true → sf.fs = s0.fs` in the postcondition. -/
def tryFromPlacedSpecOkFs [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (TryFromGhost × M.σ) :=
  { tryFromPlacedSpec A lim with
    post := fun (x, st) s0 sf =>
      ⌜(SignalMessage.tryFrom protoSignalCodec x.bytes).isOk = true → sf.fs = s0.fs⌝ ∗
        (tryFromPlacedSpec A lim).post (x, st) s0 sf }

theorem fs_eq_of_sigTryFrom_eq_ok {α ε : Type} {res : Except ε α} {m : α} {s0 sf : State}
    (h : res.isOk = true → sf.fs = s0.fs) (hok : res = .ok m) :
    sf.fs = s0.fs :=
  h (by simp [hok, Except.isOk, Except.toBool])

theorem subroutine_ok_tryFromPlacedSpec_of_okFs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim))) :
    subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim)) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [tryFromPlacedSpecOkFs, withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

/-- Strengthens `pksmSlotSpecPlaced` (Block `111`, `PreKeySignalMessage::try_from`) with `(S.pksmParse x.bytes).isSome = true → sf.fs = s0.fs` in the postcondition. -/
def pksmSlotSpecPlacedOkFs [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) (S : RunSem) :
    Spec (PksmGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ptr ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          preKeyTryFromStack ≤ s.sp.toNat ∧
          FitsEnv M lim st (PksmTryFromEnv x)⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
        stackAt s.sp preKeyTryFromStack ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ⌜(S.pksmParse x.bytes).isSome = true → sf.fs = s0.fs⌝ ∗
          ∃∗ evs : List AllocEvent,
            ⌜sf.trace = s0.trace ∧ PksmTryFromEnv x evs⌝ ∗
              pksmResAt A.repAlloc x.ret (S.pksmParse x.bytes) ∗ (x.ptr ↦ₛ x.bytes) ∗
              lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗
              A.pool lim (M.stepEvents evs st) sf }

/-- Concrete `pksmParse` specialization of `pksmSlotSpecPlacedOkFs`. -/
def pksmTryFromSpecPlacedOkFs [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop) :
    Spec (PksmGhost × M.σ) :=
  withLsCodeRoLoaded lsmpl
    { pre := fun (x, st) s =>
        ⌜s.readReg64 .x0 = x.ptr ∧ (s.readReg64 .x1).toNat = x.bytes.length ∧
          x.bytes.length < 2 ^ 32 ∧ s.readReg64 .x8 = x.ret ∧
          preKeyTryFromStack ≤ s.sp.toNat ∧
          FitsEnv M lim st (PksmTryFromEnv x)⌝ ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.ret 248 ∗ lsLogOff ∗
        stackAt s.sp preKeyTryFromStack ∗ A.pool lim st s
      post := fun (x, st) s0 sf =>
        ⌜(pksmParse x.bytes).isSome = true → sf.fs = s0.fs⌝ ∗
          ∃∗ evs : List AllocEvent,
            ⌜sf.trace = s0.trace ∧ PksmTryFromEnv x evs⌝ ∗
              pksmResAt A.repAlloc x.ret (pksmParse x.bytes) ∗ (x.ptr ↦ₛ x.bytes) ∗
              lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗
              A.pool lim (M.stepEvents evs st) sf }

theorem pksmSlotSpecPlacedOkFs_eq_pksmTryFromSpecPlacedOkFs [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop)
    (S : RunSem) (hS : ∀ b, S.pksmParse b = pksmParse b) :
    pksmSlotSpecPlacedOkFs M A lim PksmTryFromEnv S =
      pksmTryFromSpecPlacedOkFs M A lim PksmTryFromEnv := by
  have hfun : S.pksmParse = pksmParse := funext hS
  simp only [pksmSlotSpecPlacedOkFs, pksmTryFromSpecPlacedOkFs, hfun]

theorem fs_eq_of_pksmParse_eq_some {α : Type} {res : Option α} {pm : α} {s0 sf : State}
    (h : res.isSome = true → sf.fs = s0.fs) (hsome : res = some pm) :
    sf.fs = s0.fs :=
  h (by simp [hsome])

theorem subroutine_ok_pksmSlotSpecPlaced_of_okFs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (pksmSlotSpecPlacedOkFs M A lim PksmTryFromEnv S)) :
    subroutine_ok prog entry (pksmSlotSpecPlaced M A lim PksmTryFromEnv S) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [pksmSlotSpecPlacedOkFs, pksmSlotSpecPlaced, withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

theorem subroutine_ok_pksmTryFromSpecPlaced_of_okFs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PksmTryFromEnv : PksmGhost → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (pksmTryFromSpecPlacedOkFs M A lim PksmTryFromEnv)) :
    subroutine_ok prog entry (pksmTryFromSpecPlaced M A lim PksmTryFromEnv) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [pksmTryFromSpecPlacedOkFs, pksmTryFromSpecPlaced, withLsCodeRoLoaded] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

/-! ## Arm `R0` (`R+0x0 → R+0x214`) -/

def RunHopPrePlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (PreEnv : RunCall → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 : State} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlacedFd CodeOk S g s0 →
    FitsEnv M lim st (PreEnv g) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, PreEnv g evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ s (evs : List AllocEvent) (me : MeAtDispatch),
      AtDispatchPlacedFd CodeOk g me s0 s →
      PreEnv g evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
        (dispatchMemPlaced A lim (M.stepEvents evs st) g me s0 s resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s0
      (runEntryMemPlaced A lim st g s0 resStack) Q Qp
      (fun _ => ⌜False⌝)

def RunHopPrePlacedFdOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (PreEnv : RunCall → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 : State} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlacedFd CodeOk S g s0 →
    FitsEnv M lim st (PreEnv g) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, PreEnv g evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ s (evs : List AllocEvent) (me : MeAtDispatch),
      AtDispatchPlacedFd CodeOk g me s0 s →
      PreEnv g evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
        (dispatchMemPlaced A lim (M.stepEvents evs st) g me s0 s resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s0
      (runEntryMemPlaced A lim st g s0 resStack) Q Qp
      (fun _ => ⌜False⌝)

/-! ## Arm `R1a` (`R+0x214 → R+0x74c`) -/

def RunHopInit1PlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (Init1Env : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {dir : List (BitVec 8)} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlacedFd CodeOk g me s0 s →
    g.c = .init peerV dir →
    FitsEnv M lim st (Init1Env g me peerV dir) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init1Env g me peerV dir evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ s1 (evs : List AllocEvent) (d1 : Init1Data),
      AtInit1PlacedFd CodeOk g d1 s0 s1 →
      Init1Env g me peerV dir evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (init1MemPlaced A lim (M.stepEvents evs st) g d1 s0 s1 resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

def RunHopInit1PlacedFdOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (Init1Env : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {dir : List (BitVec 8)} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlacedFd CodeOk g me s0 s →
    g.c = .init peerV dir →
    FitsEnv M lim st (Init1Env g me peerV dir) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init1Env g me peerV dir evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ s1 (evs : List AllocEvent) (d1 : Init1Data),
      AtInit1PlacedFd CodeOk g d1 s0 s1 →
      Init1Env g me peerV dir evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
        (init1MemPlaced A lim (M.stepEvents evs st) g d1 s0 s1 resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

/-! ## Arm `R1b` (`R+0x74c → R+0x28f0`) -/

def RunHopInit2PlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (Init2Env : RunCall → Init1Data → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {d1 : Init1Data} {s0 s1 : State} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtInit1PlacedFd CodeOk g d1 s0 s1 →
    FitsEnv M lim st (Init2Env g d1) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init2Env g d1 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2PlacedFd CodeOk g d2 s0 s2 →
      Init2Env g d1 evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs st) g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      (init1MemPlaced A lim st g d1 s0 s1 resStack) Q Qp
      (fun _ => ⌜False⌝)

def RunHopInit2PlacedFdOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (Init2Env : RunCall → Init1Data → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {d1 : Init1Data} {s0 s1 : State} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    AtRunEntryPlaced CodeOk S g s0 →
    AtInit1PlacedFd CodeOk g d1 s0 s1 →
    FitsEnv M lim st (Init2Env g d1) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init2Env g d1 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    (∀ (s2 : State) (evs : List AllocEvent) (d2 : Init2Data),
      AtInit2PlacedFd CodeOk g d2 s0 s2 →
      Init2Env g d1 evs →
      SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
        (init2MemPlaced A lim (M.stepEvents evs st) g d2 s0 s2 resStack)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s1
      (init1MemPlaced A lim st g d1 s0 s1 resStack) Q Qp
      (fun _ => ⌜False⌝)

/-! ## Arm `R1c` (`R+0x28f0 → Join/Reject`) -/

def RunHopInit3PlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (Init3Env : RunCall → Init2Data → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s2 : State} {d2 : Init2Data} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtInit2PlacedFd CodeOk g d2 s0 s2 →
    FitsEnv M lim st (Init3Env g d2) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init3Env g d2 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init3Env g d2 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
      (init2MemPlaced A lim st g d2 s0 s2 resStack) Q Qp
      (fun _ => ⌜False⌝)

def RunHopInit3PlacedFdOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (Init3Env : RunCall → Init2Data → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s2 : State} {d2 : Init2Data} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtInit2PlacedFd CodeOk g d2 s0 s2 →
    FitsEnv M lim st (Init3Env g d2) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init3Env g d2 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, Init3Env g d2 evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s2
      (init2MemPlaced A lim st g d2 s0 s2 resStack) Q Qp
      (fun _ => ⌜False⌝)

/-! ## Arm `R2` (`send`, `R+0x214 → Join/Reject`) -/

def RunHopSendPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (SendEnv : RunCall → MeAtDispatch → AddrV → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlacedFd CodeOk g me s0 s →
    g.c = .send peerV →
    FitsEnv M lim st (SendEnv g me peerV) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, SendEnv g me peerV evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, SendEnv g me peerV evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

def RunHopSendPlacedFdOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (SendEnv : RunCall → MeAtDispatch → AddrV → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B slots →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlacedFd CodeOk g me s0 s →
    g.c = .send peerV →
    FitsEnv M lim st (SendEnv g me peerV) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, SendEnv g me peerV evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, SendEnv g me peerV evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

/-! ## Arm `R3a` (Whisper `recv`, `R+0x214 → Join/Reject`) -/

def RunHopRecvWPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (RecvWEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {rest : List (BitVec 8)} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlacedFd CodeOk g me s0 s →
    g.c = .recv peerV →
    g.i.stdin = 2#8 :: rest →
    FitsEnv M lim st (RecvWEnv g me peerV rest) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvWEnv g me peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvWEnv g me peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

def RunHopRecvWPlacedFdOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (RecvWEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {rest : List (BitVec 8)} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B slots →
    subroutine_ok (runProgPlaced H) (lsmpl.base 85)
      (withLsCodeRoLoaded lsmpl (tryFromPlacedSpecOkFs A lim)) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlacedFd CodeOk g me s0 s →
    g.c = .recv peerV →
    g.i.stdin = 2#8 :: rest →
    FitsEnv M lim st (RecvWEnv g me peerV rest) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvWEnv g me peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvWEnv g me peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

/-! ## Arm `R3b` (PreKey `recv`, `R+0x214 → Join/Reject`) -/

def RunHopRecvPPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs) (sEnvs : RunSlotEnvs)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop)
    (RecvPEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (needs : RunNeeds) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {rest : List (BitVec 8)} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B (slotsOfPlaced A lim sEnvs S needs) →
    subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim PksmTryFromEnv S) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B (slotsOfPlaced A lim sEnvs S needs) ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlacedFd CodeOk g me s0 s →
    g.c = .recv peerV →
    g.i.stdin = 3#8 :: rest →
    FitsEnv M lim st (RecvPEnv g me peerV rest) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvPEnv g me peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvPEnv g me peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

def RunHopRecvPPlacedFdOf [LibsignalPlacement] {M : AllocCostModel}
    (CodeOk : Memory → Prop) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (cEnvs : RunCalleesEnvs)
    (PksmTryFromEnv : PksmGhost → List AllocEvent → Prop)
    (RecvPEnv : RunCall → MeAtDispatch → AddrV → List (BitVec 8) → List AllocEvent → Prop)
    (H : LibsignalHooks) (B : RunBudgets) (S : RunSem) (slots : RunSlots) (resStack : Nat) : Prop :=
  ∀ {g : RunCall} {st : M.σ} {s0 s : State} {me : MeAtDispatch} {peerV : AddrV}
    {rest : List (BitVec 8)} {Q Qp : State → SepProp → Prop},
    RunHooksPlaced A lim H →
    RunCalleesPlacedFd A lim cEnvs H B slots →
    subroutine_ok (runProgPlaced H) blkPl_111.base
      (pksmSlotSpecPlacedOkFs M A lim PksmTryFromEnv S) →
    DropSpeOwnedOkAtBlock (runProgPlaced H) A lim →
    runNeed B slots ≤ resStack →
    resStack ≤ 2 ^ 63 →
    resStack ≤ s0.sp.toNat →
    AtRunEntryPlaced CodeOk S g s0 →
    AtDispatchPlacedFd CodeOk g me s0 s →
    g.c = .recv peerV →
    g.i.stdin = 3#8 :: rest →
    FitsEnv M lim st (RecvPEnv g me peerV rest) →
    PanicK g s0 Qp →
    RejectKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvPEnv g me peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    JoinKPlacedEnv CodeOk H A lim
      (fun _ _ st' => ∃ evs, RecvPEnv g me peerV rest evs ∧ st' = M.stepEvents evs st)
      g s0 resStack Q Qp →
    SepWPp (runProgPlaced H) (s0.readReg64 .lr) s
      (dispatchMemPlaced A lim st g me s0 s resStack) Q Qp
      (fun _ => ⌜False⌝)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.HopSpecsPlacedBudgetFd
