/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillVmPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage Assembly for `signal_session_handshake::initiate`

Defines per-stage and whole-function allocation-budget fitness bundles (`Stage1BudgetFits`,
`Stage2BudgetFits`, `Stage4BudgetFits`, `CliInitiateBudgetFits`) over `RustCliAllocBudget M` and
assembles Stages 1–5 into `initSlotSpecPlaced` on block `521` and caller blocks `i < 619`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget

noncomputable section

open Arm64 Arm64.Process ProofLib SepProp
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (ChainKey RootKey SessionState rootCreateChain)
open CryptoGames.Ratchet (clampScalar)
open CryptoVerification (IsLsBlockProg LibsignalPlacement lsmpl lsρ)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives modelPrims ofU8 vecU8)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (extract_withLsCodeRoLoaded withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalSpqrV1 (Params libsignalSpqrParams)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.RecordCodecs (IdentityKeyPair)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (StoresGhost cliIdentityVtSym cliSessionVtSym)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem cliBundleAt)
open CryptoVerification.SignalSession.Cli.RunProofs
  (InitOk₀ bundleEOf? cliInitiateFrame cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced AtStage2Placed AtStage3Placed AtStage4Placed AtStage5Placed
   cliCoinsFillStack cliCoinsFillStackPlaced initEntryPlaced initOom initProgPlaced
   transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas (mkBundleE)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas (stage4EphVec)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFillPlacedBudget
  (signal_session_coins_fill_placed_ok_at_init)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced initSlotSpecPlaced stage2MemPlaced stage3MemPlaced
   stage4MemPlaced stage5MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced SubsetA4InitCalleesPlaced initLocalCallees_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget
  (trustPollGhostOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoadPlacedBudget
  (sessLoadPollGhostOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1PlacedBudget
  (initEntryMemPlaced initiate_stage1_placed_ok stage1BadSpkEvents stage1OkEvents
   stage1SigsOkEvents stage1TrustEvents stage1UntrustedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2PlacedBudget
  (Stage2PlacedOk coinsFill_placed_ok_at_init_vmPreserved stage2Placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepPreChainPlacedBudget
  (stage4PreChainEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSessionPlacedBudget
  (stage4StepSessionEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4PlacedBudget
  (initiate_stage4_placed_ok stage4ErrTotalEvents stage4OkTotalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5PlacedBudget
  (CliStage5BudgetFits initiate_stage5_placed_ok_with_panic)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (CliIdKeyPairPollEnv ExistingStoreCalleesEnvs ExistingStoreCalleesPlaced InitStoreCalleesPlaced
   initStoreCallees_placed_ok)
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## Per-stage budget fitness bundles -/

/-- Heap `AllocEvent` trace across Stage 2 (`0x0390 → 0x0760`) on the continuation path. -/
abbrev stage2OkEvents (evs1 evs2 : List AllocEvent) : List AllocEvent :=
  evs1 ++ evs2 ++ rustDeallocEvents 16 8 ++ rustAllocEvents 1568 1

/-- Budget-fitness and early-exit `InitEnv` obligations for Stage 1 (`0x0000 → 0x0390`). -/
structure Stage1BudgetFits [LibsignalPlacement]
    (M : AllocCostModel) (lim : BudgetLimits)
    (eEnvs : ExistingStoreCalleesEnvs)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (x : InitGhost) (s0 : State) (st0 st : M.σ) : Prop where
  fitTrustShim : FitsEnv M lim st (BoxAllocEnv 32)
  fitTrustPoll : ∀ (evsT1 : List AllocEvent) (futT : BitVec 64),
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    FitsEnv M lim (M.stepEvents evsT1 st)
      (eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT))
  fitTrustClone : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64),
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
    StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
    FitsEvents M lim (M.stepEvents (stage1TrustEvents evsT1 evsT2) st)
      (stringCloneEvents x.peer.name)
  envUntrusted : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64),
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
    StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
    ∃ evs, InitEnv x evs ∧
      M.stepEvents (stage1UntrustedEvents evsT1 evsT2 x.peer.name) st = M.stepEvents evs st0
  fitSpkSer : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64),
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
    StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
    FitsEvents M lim (M.stepEvents (stage1TrustEvents evsT1 evsT2) st)
      (rustAllocEvents 33 1)
  envBadSpk : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64)
      (h1 : x.bundle.spkSig.length = 64)
      (h2 : x.bundle.kpkSig.length = 64)
      (h3 : x.bundle.kpk.length = 1568),
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
    StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
    (modelPrims X ⟨W.C, W.Q⟩).sigVerify
      (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
      (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
      (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = false →
    ∃ evs, InitEnv x evs ∧
      M.stepEvents (stage1BadSpkEvents evsT1 evsT2) st = M.stepEvents evs st0
  fitKpkSer : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64)
      (h1 : x.bundle.spkSig.length = 64)
      (h2 : x.bundle.kpkSig.length = 64)
      (h3 : x.bundle.kpk.length = 1568),
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
    StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
    (modelPrims X ⟨W.C, W.Q⟩).sigVerify
      (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
      (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
      (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = true →
    FitsEvents M lim (M.stepEvents (stage1BadSpkEvents evsT1 evsT2) st)
      (rustAllocEvents 1569 1)
  envBadKpk : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64)
      (h1 : x.bundle.spkSig.length = 64)
      (h2 : x.bundle.kpkSig.length = 64)
      (h3 : x.bundle.kpk.length = 1568),
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
    StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
    (modelPrims X ⟨W.C, W.Q⟩).sigVerify
      (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
      (SignalPqxdh.encodeEC (vecU8 (mkBundleE x.bundle h1 h2 h3).spkPub))
      (vecU8 (mkBundleE x.bundle h1 h2 h3).spkSig) = true →
    (modelPrims X ⟨W.C, W.Q⟩).sigVerify
      (vecU8 (mkBundleE x.bundle h1 h2 h3).idPub)
      (SignalPqxdh.encodeKEM (vecU8 (mkBundleE x.bundle h1 h2 h3).kpkPub))
      (vecU8 (mkBundleE x.bundle h1 h2 h3).kpkSig) = false →
    ∃ evs, InitEnv x evs ∧
      M.stepEvents (stage1SigsOkEvents evsT1 evsT2) st = M.stepEvents evs st0
  fitLoadShim : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64)
      (be : PreKeyBundleFields),
    bundleEOf? x.bundle = some be →
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
    StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
    PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true →
    FitsEnv M lim (M.stepEvents (stage1SigsOkEvents evsT1 evsT2) st) (BoxAllocEnv 24)
  fitLoadPoll : ∀ (evsT1 evsT2 evsL1 : List AllocEvent) (futT futL : BitVec 64)
      (be : PreKeyBundleFields),
    bundleEOf? x.bundle = some be →
    BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
    eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
    StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
    PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true →
    BoxAllocEnv 24 evsL1 → futL ≠ 0#64 → futL.toNat % 8 = 0 →
    FitsEnv M lim (M.stepEvents (stage1SigsOkEvents evsT1 evsT2 ++ evsL1) st)
      (eEnvs.sessLoadPoll x.F (sessLoadPollGhostOf x s0 futL))

/-- Budget-fitness and early-exit `InitEnv` obligations for Stage 2 (`0x0390 → 0x0760`). -/
structure Stage2BudgetFits [LibsignalPlacement]
    (M : AllocCostModel) (lim : BudgetLimits)
    (eEnvs : ExistingStoreCalleesEnvs)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (x : InitGhost) (s0 : State) (st0 st : M.σ) : Prop where
  fitShim : FitsEnv M lim st (BoxAllocEnv 16)
  fitPoll : ∀ (evs1 : List AllocEvent) (box : BitVec 64),
    BoxAllocEnv 16 evs1 → box ≠ 0#64 →
    FitsEnv M lim (M.stepEvents evs1 st)
      (CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
        { fut := box
          out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
          self := x.stores
          own := StoresGhost.opened.identity.own })
  envErr : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64),
    StoresGhost.opened.identity.keyPair cliIo.rd x.F = .error () →
    box ≠ 0#64 →
    BoxAllocEnv 16 evs1 →
    CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
      { fut := box
        out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
        self := x.stores
        own := StoresGhost.opened.identity.own } evs2 →
    ∃ evs, InitEnv x evs ∧
      M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st = M.stepEvents evs st0
  fitPqspkAlloc : ∀ (evs1 evs2 : List AllocEvent) (box : BitVec 64) (kp : IdentityKeyPair),
    StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp →
    box ≠ 0#64 →
    BoxAllocEnv 16 evs1 →
    CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
      { fut := box
        out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
        self := x.stores
        own := StoresGhost.opened.identity.own } evs2 →
    FitsEvents M lim (M.stepEvents (evs1 ++ evs2 ++ rustDeallocEvents 16 8) st)
      (rustAllocEvents 1568 1)

/-- Budget-fitness and early-exit `InitEnv` obligations for Stage 4 (`0x10a4 → 0x1484`). -/
structure Stage4BudgetFits
    (M : AllocCostModel) (lim : BudgetLimits)
    (InitStateEnv : Params → List AllocEvent → Prop)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (W : CliHooks) (x : InitGhost) (dk : SignalPqxdh.DRKey)
    (st0 st : M.σ) : Prop where
  fitPreChain : FitsEvents M lim st
    (stage4PreChainEvents W.C x.bundle.spk (clampScalar (stage4EphVec x.coins)))
  fitSpqr : ∀ (rk1 : RootKey) (ck1 : ChainKey),
    rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
        ⟨clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
    FitsEnv M lim
      (M.stepEvents
        (stage4PreChainEvents W.C x.bundle.spk (clampScalar (stage4EphVec x.coins))) st)
      (InitStateEnv
        (libsignalSpqrParams false .a2b (bytesToKey32 (ofU8 dk.pqrKey))))
  fitSess : ∀ (rk1 : RootKey) (ck1 : ChainKey) (evsSpqr : List AllocEvent),
    rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
        ⟨clampScalar (stage4EphVec x.coins)⟩ = .ok (rk1, ck1) →
    InitStateEnv
      (libsignalSpqrParams false .a2b (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
    FitsEvents M lim
      (M.stepEvents evsSpqr
        (M.stepEvents
          (stage4PreChainEvents W.C x.bundle.spk (clampScalar (stage4EphVec x.coins))) st))
      stage4StepSessionEvents
  envErr :
    rootCreateChain W.C (bytesToKey32 (ofU8 dk.rootKey)) x.bundle.spk
        ⟨clampScalar (stage4EphVec x.coins)⟩ = .error .invalidKeyAgreement →
    ∃ evs, InitEnv x evs ∧
      M.stepEvents (stage4ErrTotalEvents W x) st = M.stepEvents evs st0

/-- Budget-threaded Stage 3 (`0x0760 → 0x10a4`) continuation contract under `[LibsignalPlacement]`. -/
def Stage3PlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (InitStateEnv : Params → List AllocEvent → Prop)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop)
    (Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem) : Prop :=
  ∀ {x : InitGhost} {st0 st : M.σ} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
    {Q Qp : State → SepProp → Prop},
    RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) →
    (∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl
          (withVmPreserved
            (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk)))) →
    (∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (CoinsFillPlacedBudget.coinsFillSpecPlacedW3 cStk))) →
    InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk →
    Stage3Fit x be kp ekASk ekAPk pqspkPtr opkId s0 st0 st →
    S.initiate = initDef X ⟨W.C, W.Q⟩ →
    InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
    x.coins.length < 2 ^ 63 →
    cliInitiateNeed B ≤ stk →
    stk ≤ 2 ^ 63 →
    stk ≤ s0.sp.toNat →
    AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
    (∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf) →
    (∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf) →
    (∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64)
        (evsS3 : List AllocEvent),
      Stage3Out x be kp dk hdr evsS3 →
      AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s4
        (stage4MemPlaced A lim (M.stepEvents evsS3 st) x kp ekASk ekAPk kemCtBytes hkSlotBytes
          pqspkPtr kemCtPtr opkId stk s0 s4)
        Q Qp (initOom s0)) →
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s3
      (stage3MemPlaced A lim st x kp ekASk ekAPk pqspkPtr opkId stk s0 s3) Q Qp (initOom s0)

/-! ## Whole-function budget-fitness bundle -/

/-- Stage 1 continuation witnesses from entry `s0` to `AtStage2Placed` (`0x0390`). -/
structure Stage1StepWitness [LibsignalPlacement]
    (eEnvs : ExistingStoreCalleesEnvs) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (x : InitGhost) (be : PreKeyBundleFields) (s0 s2 : State)
    (evsT1 evsT2 evsL1 evsL2 : List AllocEvent) (futT futL : BitVec 64) : Prop where
  boxTrust : BoxAllocEnv 32 evsT1
  futTNonNull : futT ≠ 0#64
  futTAligned : futT.toNat % 8 = 0
  trustPoll : eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2
  boxLoad : BoxAllocEnv 24 evsL1
  futLNonNull : futL ≠ 0#64
  futLAligned : futL.toNat % 8 = 0
  loadPoll : eEnvs.sessLoadPoll x.F (sessLoadPollGhostOf x s0 futL) evsL2
  atStage2 : AtStage2Placed W X x be s0 s2

/-- Stage 2 continuation witnesses from `AtStage2Placed` (`0x0390`) to `AtStage3Placed` (`0x0760`). -/
structure Stage2StepWitness [LibsignalPlacement]
    (eEnvs : ExistingStoreCalleesEnvs) (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (x : InitGhost) (be : PreKeyBundleFields) (kp : IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s3 : State) (evs1 evs2 : List AllocEvent) (box : BitVec 64) : Prop where
  boxNonNull : box ≠ 0#64
  boxAlloc : BoxAllocEnv 16 evs1
  keyPairPoll : CliIdKeyPairPollEnv eEnvs.dirGet cliIo.rd x.F
    { fut := box
      out := s0.sp - BitVec.ofNat 64 cliInitiateFrame + 5632#64
      self := x.stores
      own := StoresGhost.opened.identity.own } evs2
  atStage3 : AtStage3Placed W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3

/-- Whole-function budget-fitness bundle threading allocator state `st0` across Stages 1–5 of `initiate`. -/
structure CliInitiateBudgetFits [LibsignalPlacement]
    (M : AllocCostModel) (lim : BudgetLimits)
    (eEnvs : ExistingStoreCalleesEnvs)
    (InitStateEnv : Params → List AllocEvent → Prop)
    (InitEnv : InitGhost → List AllocEvent → Prop)
    (Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop)
    (Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop)
    (W : CliHooks) (X : UnreachedPqxdhPrimitives)
    (x : InitGhost) (s0 : State) (st0 : M.σ) : Prop where
  stage1 : Stage1BudgetFits M lim eEnvs InitEnv W X x s0 st0 st0
  stage2 : ∀ {s2 : State} {be : PreKeyBundleFields}
      {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64},
    Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL →
    Stage2BudgetFits M lim eEnvs InitEnv x s0 st0
      (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st0)
  stage3 : ∀ {s2 s3 : State} {be : PreKeyBundleFields}
      {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64}
      {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
      {pqspkPtr : BitVec 64} {opkId : BitVec 32}
      {evs1 evs2 : List AllocEvent} {box : BitVec 64},
    Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL →
    Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box →
    Stage3Fit x be kp ekASk ekAPk pqspkPtr opkId s0 st0
      (M.stepEvents (stage2OkEvents evs1 evs2)
        (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st0))
  stage4 : ∀ {s2 s3 s4 : State} {be : PreKeyBundleFields}
      {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64}
      {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
      {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
      {evs1 evs2 : List AllocEvent} {box : BitVec 64}
      {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
      {kemCtBytes hkSlotBytes : List (BitVec 8)} {evsS3 : List AllocEvent},
    Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL →
    Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box →
    Stage3Out x be kp dk hdr evsS3 →
    AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
      s0 s4 →
    Stage4BudgetFits M lim InitStateEnv InitEnv W x dk st0
      (M.stepEvents evsS3
        (M.stepEvents (stage2OkEvents evs1 evs2)
          (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st0)))
  stage5 : ∀ {s2 s3 s4 s5 : State} {be : PreKeyBundleFields}
      {evsT1 evsT2 evsL1 evsL2 : List AllocEvent} {futT futL : BitVec 64}
      {kp : IdentityKeyPair} {ekASk ekAPk : List (BitVec 8)}
      {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
      {evs1 evs2 : List AllocEvent} {box : BitVec 64}
      {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
      {kemCtBytes hkSlotBytes : List (BitVec 8)} {evsS3 : List AllocEvent}
      {sg : SessionGhost} {ss : SessionState (List (BitVec 8))} {evsSpqr : List AllocEvent},
    Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL →
    Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box →
    Stage3Out x be kp dk hdr evsS3 →
    AtStage4Placed W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
      s0 s4 →
    InitStateEnv
      (libsignalSpqrParams false .a2b (bytesToKey32 (ofU8 dk.pqrKey))) evsSpqr →
    AtStage5Placed W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
    CliStage5BudgetFits M lim eEnvs InitEnv x be kp hdr opkId sg ss s0 st0
      (M.stepEvents (stage4OkTotalEvents W x evsSpqr)
        (M.stepEvents evsS3
          (M.stepEvents (stage2OkEvents evs1 evs2)
            (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st0))))

/-! ## Top-level assembly theorems -/

/-- Lifts an entry `SepWPp` proof into `subroutine_ok` for `DefsPlacedBudget.initSlotSpecPlaced`. -/
theorem subroutine_ok_of_sepWPp_init_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {S : RunSem} {stk : Nat}
    (h : ∀ (p : InitGhost × M.σ) (R : SepProp) (s0 : State),
      s0.pc = initEntryPlaced →
      s0.status = .Running →
      (s0.mem ⊨ (initSlotSpecPlaced A lim InitEnv S stk).pre p s0 ∗ R) →
      s0.spAligned = true →
      ∃ P0, (s0.mem ⊨ P0 ∗ R) ∧
        SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s0 P0
          (fun sf Pf =>
            ((sf.mem ⊨ Pf ∗ R) →
              (sf.mem ⊨ (initSlotSpecPlaced A lim InitEnv S stk).post p s0 sf ∗ R)) ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
          (fun sf Pf =>
            (sf.mem ⊨ Pf ∗ R) →
              (sf.mem ⊨ (initSlotSpecPlaced A lim InitEnv S stk).onPanic p s0 sf ∗ R))
          (initOom s0)) :
    subroutine_ok (initProgPlaced mmpl gh W) initEntryPlaced (initSlotSpecPlaced A lim InitEnv S stk) :=
  subroutine_ok_of_sepWPp_init h

set_option maxRecDepth 200000 in
/-- Budget-threaded top-level assembly on block `521`, parameterized over `Stage2PlacedOk` and `Stage3PlacedOk`. -/
theorem cliInitiate_placed_ok_proof_of_stage2 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage2 : Stage2PlacedOk A lim eEnvs InitStateEnv InitEnv mmpl gh W X B S)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hFits : ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
      AtInitEntryPlaced x s0 →
      S.filesOk x.F x.peer.val x.me.val →
      S.initOk x.F x.peer.val x.me.val →
      InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      FitsEnv M lim st0 (InitEnv x) →
      CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0) :
    subroutine_ok (initProgPlaced mmpl gh W) initEntryPlaced (initSlotSpecPlaced A lim InitEnv S stk) := by
  have : CryptoVerification.SignalSession.Cli.RunProofs.Initiate.InitTraceFsSound mmpl gh W := ⟨hh.fs⟩
  have hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk :=
    initStoreCallees_placed_ok mmpl gh W B hh hExist stk hstk hstk64
  have hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk :=
    initLocalCallees_placed_ok mmpl gh W B hh ha4 stk hstk hstk64
  have hCoinsRoCl : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsRoCl lsmpl (CoinsFillPlacedBudget.coinsFillSpecPlacedW3 cStk)) :=
    fun hc1 hc2 => signal_session_coins_fill_placed_ok_at_init mmpl gh W hh.allocFs hc1 hc2
  have hCoinsVmPlaced : ∀ {cStk : Nat}, cliCoinsFillStackPlaced ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl
          (withVmPreserved
            (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) :=
    fun hc1 hc2 => coinsFill_placed_ok_at_init_vmPreserved mmpl gh W hh.allocFs hc1 hc2
  have hCoinsVm : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 618)
        (withLsCodeRoLoaded lsmpl
          (withVmPreserved
            (CryptoVerification.SignalSession.Cli.RunProofs.Initiate.coinsFillSpecPlacedW3 cStk))) := by
    intro cStk hc1 hc2
    have hge : 80 ≤ cStk := by
      unfold cliCoinsFillStack CryptoVerification.LibsignalTripleRatchet.extHookStack at hc1; omega
    have hmcSat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
        CryptoVerification.LibsignalTripleRatchet.memcpyName
        (CryptoVerification.LibsignalTripleRatchet.withStack
          LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec
          (cStk - 80)).keepsFs := by
      rcases hh.memcpyRegionKeepsFs with ⟨f, hf, hok⟩
      have hws := CryptoVerification.SignalSession.Cli.MainHops.hookOk_withStack hok (cStk - 80)
      refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
      obtain ⟨hkf, hsym, hout⟩ := hws x R s0 hrun hpre hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | hrest
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withStack, Arm64.Spec.keepsFs] at hpost ⊢
        simpa only [sepConj_assoc] using hpost
      · exact Or.inr hrest
    have hmsSat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
        CryptoVerification.LibsignalTripleRatchet.memsetName
        (CryptoVerification.LibsignalTripleRatchet.withStack
          LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemsetRegionBudgetSpec
          (cStk - 80)).keepsFs := by
      rcases hh.memsetRegionKeepsFs with ⟨f, hf, hok⟩
      have hws := CryptoVerification.SignalSession.Cli.MainHops.hookOk_withStack hok (cStk - 80)
      refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
      obtain ⟨hkf, hsym, hout⟩ := hws x R s0 hrun hpre hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | hrest
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withStack, Arm64.Spec.keepsFs] at hpost ⊢
        simpa only [sepConj_assoc] using hpost
      · exact Or.inr hrest
    exact CoinsFillVmPlacedBudget.signal_session_coins_fill_vm_placed_ok_of_mc_ms hge hc2
      (CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain
        (CryptoVerification.ls_hook_ok_ultra_of_mem
          (prog := (CryptoVerification.SignalSession.Coins.Placed.blkPC_618).rebase
            (CryptoVerification.SignalSession.Coins.Placed.blkPl_618).base
            (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          hmcSat))
      (CryptoVerification.LibsignalPublicApi.StoreKit.subroutine_ok_rocl_of_plain
        (CryptoVerification.ls_hook_ok_ultra_of_mem
          (prog := (CryptoVerification.SignalSession.Coins.Placed.blkPC_618).rebase
            (CryptoVerification.SignalSession.Coins.Placed.blkPl_618).base
            (cliGhostExterns gh (cliExternsPlaced mmpl W)))
          hmsSat))
  apply subroutine_ok_of_sepWPp_init_placed
  rintro ⟨x, st0⟩ R s0 hpc hrun0 hpre hal
  unfold initSlotSpecPlaced at hpre
  obtain ⟨hinv, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only at hpre1
  simp only [DefsPlacedBudget.slotFramePlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hfs0, hfilesOk, hsInitOk, hspk, hFitsInit⟩,
    hcoinsLt, hm⟩ := hpre1
  have hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val :=
    hok x.F x.peer.val x.me.val hfilesOk hsInitOk
  have hs0 : AtInitEntryPlaced x s0 :=
    { pc := hpc
      run := hrun0
      inv := hinv
      spAligned := hal
      x0 := hx0
      x1 := hx1
      x2 := hx2
      x3 := hx3
      x4 := hx4
      x5 := hx5
      x6 := hx6
      x7 := hx7
      x8 := hx8
      files := hfs0 }
  have hFitAll := hFits x st0 s0 hs0 hfilesOk hsInitOk hinitOk hcoinsLt hspk hFitsInit
  refine ⟨initEntryMemPlaced A lim st0 x stk s0, ?_, ?_⟩
  · simpa only [initEntryMemPlaced, sepConj_assoc] using hm
  · have hpostK : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf →
        (((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (initSlotSpecPlaced A lim InitEnv S stk).post (x, st0) s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
      intro sf Pf ⟨hsp, hcs, hent⟩
      exact ⟨fun hmPf => Satisfies.mono (sepConj_mono_left hent) hmPf, hsp, hcs⟩
    have hpanicK : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf →
        ((sf.mem ⊨ Pf ∗ R) →
          (sf.mem ⊨ (initSlotSpecPlaced A lim InitEnv S stk).onPanic (x, st0) s0 sf ∗ R)) := by
      intro sf Pf hent hmPf
      exact Satisfies.mono (sepConj_mono_left hent) hmPf
    have hF1 := hFitAll.stage1
    refine initiate_stage1_placed_ok hh hStore hLocal
      hF1.fitTrustShim hF1.fitTrustPoll hF1.fitTrustClone hF1.envUntrusted
      hF1.fitSpkSer hF1.envBadSpk hF1.fitKpkSer hF1.envBadKpk
      hF1.fitLoadShim hF1.fitLoadPoll
      hS hinitOk hcoinsLt hstk hstk64 hspk hs0 hpostK hpanicK
      fun s2 be evsT1 evsT2 evsL1 evsL2 futT futL
          hevsT1 hfutTNZ hfutTAl hevsT2 hevsL1 hfutLNZ hfutLAl hevsL2 hs2 => ?_
    have hw1 : Stage1StepWitness eEnvs W X x be s0 s2 evsT1 evsT2 evsL1 evsL2 futT futL :=
      ⟨hevsT1, hfutTNZ, hfutTAl, hevsT2, hevsL1, hfutLNZ, hfutLAl, hevsL2, hs2⟩
    have hF2 := hFitAll.stage2 hw1
    refine hStage2 hh @hCoinsVmPlaced hStore hLocal
      hF2.fitShim hF2.fitPoll hF2.envErr
      hS hinitOk hcoinsLt hstk hstk64 hspk hs2 hpostK hpanicK
      (fun evs1 evs2 box kp _ _ _ hkp hbox hevs1 hevs2 _ _ =>
        Entails.pure_left fun ⟨hnfit, _⟩ =>
          False.elim (hnfit (hF2.fitPqspkAlloc evs1 evs2 box kp hkp hbox hevs1 hevs2)))
      fun s3 kp ekASk ekAPk pqspkPtr opkId evs1 evs2 box hbox hevs1 hevs2 hs3 => ?_
    have hw2 : Stage2StepWitness eEnvs W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 evs1 evs2 box :=
      ⟨hbox, hevs1, hevs2, hs3⟩
    have hF3 := hFitAll.stage3 hw1 hw2
    refine hStage3 hh @hCoinsVm @hCoinsRoCl hLocal hF3
      hS hinitOk hcoinsLt hstk hstk64 hspk hs3 hpostK hpanicK
      fun s4 dk hdr kemCtBytes hkSlotBytes kemCtPtr evsS3 hevsS3 hs4 => ?_
    have hF4 := hFitAll.stage4 hw1 hw2 hevsS3 hs4
    refine initiate_stage4_placed_ok hh @hCoinsRoCl hLocal
      hF4.fitPreChain hF4.fitSpqr hF4.fitSess hF4.envErr
      hS hinitOk hcoinsLt hstk hstk64 hspk hs4 hpostK hpanicK
      fun s5 sg ss evsSpqr hevsSpqr hs5 => ?_
    have hF5 := hFitAll.stage5 hw1 hw2 hevsS3 hs4 hevsSpqr hs5
    exact initiate_stage5_placed_ok_with_panic hh hStore hLocal hF5
      hS hinitOk hcoinsLt hstk hstk64 hspk hs5 hpostK hpanicK

/-- Budget-threaded top-level assembly on block `521`, discharging Stage 2 via `Stage2PlacedBudget.stage2Placed_ok`. -/
theorem cliInitiate_placed_ok_proof [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hFits : ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
      AtInitEntryPlaced x s0 →
      S.filesOk x.F x.peer.val x.me.val →
      S.initOk x.F x.peer.val x.me.val →
      InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      FitsEnv M lim st0 (InitEnv x) →
      CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0) :
    subroutine_ok (initProgPlaced mmpl gh W) initEntryPlaced (initSlotSpecPlaced A lim InitEnv S stk) :=
  cliInitiate_placed_ok_proof_of_stage2 mmpl gh W X B S hh hExist ha4
    (stage2Placed_ok A lim eEnvs InitStateEnv InitEnv mmpl gh W X B S)
    hStage3 hS hok stk hstk hstk64 hFits

/-- Transfers `cliInitiate_placed_ok_proof` to any caller block `i < 619`. -/
theorem cliInitiate_caller_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {Stage3Fit : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      List (BitVec 8) → List (BitVec 8) → BitVec 64 → BitVec 32 → State → M.σ → M.σ → Prop}
    {Stage3Out : InitGhost → PreKeyBundleFields → IdentityKeyPair →
      SignalPqxdh.DRKey → SignalPqxdh.HandshakeHdr → List AllocEvent → Prop}
    {callerProg : Program} {i : Nat}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (X : UnreachedPqxdhPrimitives) (B : RunBudgets) (S : RunSem)
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hExist : ExistingStoreCalleesPlaced A lim eEnvs (cliGhostExterns gh (cliExternsPlaced mmpl W)) B)
    (ha4 : SubsetA4InitCalleesPlaced A lim InitStateEnv mmpl gh W)
    (hStage3 : Stage3PlacedOk A lim InitStateEnv InitEnv Stage3Fit Stage3Out mmpl gh W X B S)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hok : ∀ F peer me, S.filesOk F peer me → S.initOk F peer me → InitOk₀ ⟨W.C, W.Q⟩ F peer me)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (hstk64 : stk ≤ 2 ^ 63)
    (hFits : ∀ (x : InitGhost) (st0 : M.σ) (s0 : State),
      AtInitEntryPlaced x s0 →
      S.filesOk x.F x.peer.val x.me.val →
      S.initOk x.F x.peer.val x.me.val →
      InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val →
      x.coins.length < 2 ^ 63 →
      stk ≤ s0.sp.toNat →
      FitsEnv M lim st0 (InitEnv x) →
      CliInitiateBudgetFits M lim eEnvs InitStateEnv InitEnv Stage3Fit Stage3Out W X x s0 st0)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 521) (initSlotSpecPlaced A lim InitEnv S stk) :=
  transfer_withLsCodeRoLoaded (callerProg := callerProg) (hi := hi)
    (cliInitiate_placed_ok_proof mmpl gh W X B S hh hExist ha4 hStage3 hS hok stk hstk hstk64 hFits)

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.AssemblyPlacedBudget
