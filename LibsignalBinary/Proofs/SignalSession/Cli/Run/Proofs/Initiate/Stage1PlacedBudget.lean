/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoadPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Stage 1 (`0x0000 → 0x0390`)

Composes the budget-threaded Stage 1 segments (`stage1_prologue_trust_placed_ok`,
`stage1_spk_sig_placed_ok`, `stage1_kpk_sig_placed_ok`, and `stage1_load_session_placed_ok`) on
`initProgPlaced` over `RustCliAllocBudget M`, tracking the `AllocEvent` traces along `0x0000 → 0x0390`
and all early `Err` exits.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1PlacedBudget

noncomputable section

open Arm64 Arm64.Obj Arm64.Process ProofLib SepProp
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PreKeyBundleFields UnreachedPqxdhPrimitives modelPrims vecU8)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalSpqrV1 (Params)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchetRepr (protocolAddressAt)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo coinsInstalledPlaced storesAt)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem cliBundleAt)
open CryptoVerification.SignalSession.Cli.RunProofs (InitOk₀ bundleEOf? cliInitiateNeed initDef)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (AtInitEntryPlaced AtStage2Placed initProgExtPlaced initProgPlaced)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
  (bundleEOf_eq_some_mkBundleE mkBundleE)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (stringCloneEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlacedBudget
  (InitExitPostPlaced InitPanicPostPlaced stage2MemPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (InitLocalCalleesPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegPrologueTrustPlacedBudget
  (stage1_prologue_trust_placed_ok trustPollGhostOf)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoadPlacedBudget
  (sessLoadPollGhostOf stage1_load_session_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsPlacedBudget
  (kpkSigEvents spkSigEvents stage1_kpk_sig_placed_ok stage1_spk_sig_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlacedBudget
  (ExistingStoreCalleesEnvs InitStoreCalleesPlaced)

/-- Spatial entry footprint of `DefsPlacedBudget.initSlotSpecPlaced` after extracting pure preconditions. -/
def initEntryMemPlaced [LibsignalPlacement] {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (x : InitGhost) (stk : Nat)
    (s0 : State) : SepProp :=
  storesAt A.repAlloc x.stores StoresGhost.opened ∗
    protocolAddressAt A.repAlloc x.peer x.peerA ∗ protocolAddressAt A.repAlloc x.me x.meA ∗
    coinsInstalledPlaced x.coinsP x.coins ∗
    tokenInitPlacedAt ∗
    lsLogOff ∗ A.pool lim st s0 ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s0.sp stk

/-- Heap `AllocEvent` trace of Segment 1 (`is_trusted_identity` shim, poll, and dealloc). -/
abbrev stage1TrustEvents (evsT1 evsT2 : List AllocEvent) : List AllocEvent :=
  evsT1 ++ evsT2 ++ rustDeallocEvents 32 8

/-- Heap `AllocEvent` trace along the untrusted-identity early `Err` exit (`0x0000 → 0x0350`). -/
abbrev stage1UntrustedEvents (evsT1 evsT2 : List AllocEvent) (peerName : VecGhost) :
    List AllocEvent :=
  stage1TrustEvents evsT1 evsT2 ++ stringCloneEvents peerName

/-- Heap `AllocEvent` trace through Segment 2 (SPK signature serialize, verify, and dealloc). -/
abbrev stage1BadSpkEvents (evsT1 evsT2 : List AllocEvent) : List AllocEvent :=
  stage1TrustEvents evsT1 evsT2 ++ spkSigEvents

/-- Heap `AllocEvent` trace through Segment 3 (both SPK and KPK signature checks). -/
abbrev stage1SigsOkEvents (evsT1 evsT2 : List AllocEvent) : List AllocEvent :=
  stage1BadSpkEvents evsT1 evsT2 ++ kpkSigEvents

/-- Complete heap `AllocEvent` trace across Stage 1 (`0x0000 → 0x0390`). -/
abbrev stage1OkEvents (evsT1 evsT2 evsL1 evsL2 : List AllocEvent) : List AllocEvent :=
  stage1SigsOkEvents evsT1 evsT2 ++ evsL1 ++ evsL2 ++ rustDeallocEvents 24 8

/-- Budget-threaded relocatable Stage 1 (`0x0000 → 0x0390` and early `Err` exits). -/
theorem initiate_stage1_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {eEnvs : ExistingStoreCalleesEnvs}
    {InitStateEnv : Params → List AllocEvent → Prop}
    {InitEnv : InitGhost → List AllocEvent → Prop}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {st0 st : M.σ} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A lim eEnvs mmpl gh W B stk)
    (hLocal : InitLocalCalleesPlaced A lim InitStateEnv mmpl gh W stk)
    (hFitsTrustShim : FitsEnv M lim st (BoxAllocEnv 32))
    (hFitsTrustPoll : ∀ (evsT1 : List AllocEvent) (futT : BitVec 64),
      BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
      FitsEnv M lim (M.stepEvents evsT1 st)
        (eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT)))
    (hFitsTrustClone : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64),
      BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
      FitsEvents M lim (M.stepEvents (stage1TrustEvents evsT1 evsT2) st)
        (stringCloneEvents x.peer.name))
    (hEnvUntrusted : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64),
      BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok false →
      ∃ evs, InitEnv x evs ∧
        M.stepEvents (stage1UntrustedEvents evsT1 evsT2 x.peer.name) st = M.stepEvents evs st0)
    (hFitsSpkSer : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64),
      BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      FitsEvents M lim (M.stepEvents (stage1TrustEvents evsT1 evsT2) st)
        (rustAllocEvents 33 1))
    (hEnvBadSpk : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64)
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
        M.stepEvents (stage1BadSpkEvents evsT1 evsT2) st = M.stepEvents evs st0)
    (hFitsKpkSer : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64)
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
        (rustAllocEvents 1569 1))
    (hEnvBadKpk : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64)
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
        M.stepEvents (stage1SigsOkEvents evsT1 evsT2) st = M.stepEvents evs st0)
    (hFitsLoadShim : ∀ (evsT1 evsT2 : List AllocEvent) (futT : BitVec 64)
        (be : PreKeyBundleFields),
      bundleEOf? x.bundle = some be →
      BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true →
      FitsEnv M lim (M.stepEvents (stage1SigsOkEvents evsT1 evsT2) st) (BoxAllocEnv 24))
    (hFitsLoadPoll : ∀ (evsT1 evsT2 evsL1 : List AllocEvent) (futT futL : BitVec 64)
        (be : PreKeyBundleFields),
      bundleEOf? x.bundle = some be →
      BoxAllocEnv 32 evsT1 → futT ≠ 0#64 → futT.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
      StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true →
      PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true →
      BoxAllocEnv 24 evsL1 → futL ≠ 0#64 → futL.toNat % 8 = 0 →
      FitsEnv M lim (M.stepEvents (stage1SigsOkEvents evsT1 evsT2 ++ evsL1) st)
        (eEnvs.sessLoadPoll x.F (sessLoadPollGhostOf x s0 futL)))
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (_hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs0 : AtInitEntryPlaced x s0)
    (hpost : ∀ sf Pf, InitExitPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A lim InitEnv S x st0 stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State) (be : PreKeyBundleFields)
        (evsT1 evsT2 evsL1 evsL2 : List AllocEvent) (futT futL : BitVec 64),
      BoxAllocEnv 32 evsT1 →
      futT ≠ 0#64 →
      futT.toNat % 8 = 0 →
      eEnvs.idTrustPoll x.F (trustPollGhostOf x s0 futT) evsT2 →
      BoxAllocEnv 24 evsL1 →
      futL ≠ 0#64 →
      futL.toNat % 8 = 0 →
      eEnvs.sessLoadPoll x.F (sessLoadPollGhostOf x s0 futL) evsL2 →
      AtStage2Placed W X x be s0 s2 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
        (stage2MemPlaced A lim (M.stepEvents (stage1OkEvents evsT1 evsT2 evsL1 evsL2) st)
          x stk s0 s2)
        Q Qp oom) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s0
      (initEntryMemPlaced A lim st x stk s0) Q Qp oom := by
  unfold initEntryMemPlaced
  refine stage1_prologue_trust_placed_ok hh hStore hFitsTrustShim hFitsTrustPoll
    hFitsTrustClone hEnvUntrusted hS hinitOk hstk hstk64 hs0 hpost hpanic
    fun s1 evsT1 evsT2 futT h1 h2 h3 hevsT1 hfutTNZ hfutTAl hevsT2 hctrl1 htr1 hfs1 htrust => ?_
  refine stage1_spk_sig_placed_ok hh hLocal hS hstk hstk64 hs0.x8
    h1 h2 h3 hctrl1 htr1 hfs1 htrust
    (hFitsSpkSer evsT1 evsT2 futT hevsT1 hfutTNZ hfutTAl hevsT2 htrust)
    (fun hbadSpk => by
      rw [← M.stepEvents_append (stage1TrustEvents evsT1 evsT2) spkSigEvents st]
      exact hEnvBadSpk evsT1 evsT2 futT h1 h2 h3 hevsT1 hfutTNZ hfutTAl hevsT2 htrust hbadSpk)
    hpost hpanic fun s2 hctrl2 htr2 hfs2 hspkSig => ?_
  rw [← M.stepEvents_append (stage1TrustEvents evsT1 evsT2) spkSigEvents st]
  refine stage1_kpk_sig_placed_ok hh hLocal hS hstk hstk64 hs0.x8
    h1 h2 h3 hctrl2 htr2 hfs2 htrust hspkSig
    (hFitsKpkSer evsT1 evsT2 futT h1 h2 h3 hevsT1 hfutTNZ hfutTAl hevsT2 htrust hspkSig)
    (fun hbadKpk => by
      rw [← M.stepEvents_append (stage1BadSpkEvents evsT1 evsT2) kpkSigEvents st]
      exact hEnvBadKpk evsT1 evsT2 futT h1 h2 h3
        hevsT1 hfutTNZ hfutTAl hevsT2 htrust hspkSig hbadKpk)
    hpost hpanic fun s3 hctrl3 htr3 hfs3 hsigs => ?_
  rw [← M.stepEvents_append (stage1BadSpkEvents evsT1 evsT2) kpkSigEvents st]
  have hbe : bundleEOf? x.bundle = some (mkBundleE x.bundle h1 h2 h3) :=
    bundleEOf_eq_some_mkBundleE x.bundle h1 h2 h3
  exact stage1_load_session_placed_ok hh hStore
    (hFitsLoadShim evsT1 evsT2 futT (mkBundleE x.bundle h1 h2 h3)
      hbe hevsT1 hfutTNZ hfutTAl hevsT2 htrust hsigs)
    (fun evsL1 futL hevsL1 hfutLNZ hfutLAl => by
      rw [← M.stepEvents_append (stage1SigsOkEvents evsT1 evsT2) evsL1 st]
      exact hFitsLoadPoll evsT1 evsT2 evsL1 futT futL (mkBundleE x.bundle h1 h2 h3)
        hbe hevsT1 hfutTNZ hfutTAl hevsT2 htrust hsigs hevsL1 hfutLNZ hfutLAl)
    hinitOk hstk hstk64 hs0.x8 hbe hctrl3 htr3 hfs3 htrust hsigs hpanic
    fun s4 be' evsL1 evsL2 futL hevsL1 hfutLNZ hfutLAl hevsL2 hAt2 => by
      rw [← M.stepEvents_append (stage1SigsOkEvents evsT1 evsT2)
        (evsL1 ++ evsL2 ++ rustDeallocEvents 24 8) st]
      have heqOk :
          stage1SigsOkEvents evsT1 evsT2 ++ (evsL1 ++ evsL2 ++ rustDeallocEvents 24 8) =
            stage1OkEvents evsT1 evsT2 evsL1 evsL2 := by
        simp only [stage1OkEvents, List.append_assoc]
      rw [heqOk]
      exact hnext s4 be' evsT1 evsT2 evsL1 evsL2 futT futL
        hevsT1 hfutTNZ hfutTAl hevsT2 hevsL1 hfutLNZ hfutLAl hevsL2 hAt2

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1PlacedBudget
