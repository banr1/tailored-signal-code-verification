/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoadPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 1 (`0x0000 → 0x0390`): Prologue, Trust Check, Bundle Signatures, and `load_session`

Composes the `[LibsignalPlacement]` Stage 1 segments on `initProgPlaced` from `initEntryMemPlaced`
(`0x0000`) to `AtStage2Placed` (`0x0390`) and early `Err` returns (`0x0350 → ret`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (CliGhostHooks cliGhostExterns)
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Spatial entry footprint of `initSlotSpecPlaced` after extracting pure preconditions. -/
def initEntryMemPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost) (stk : Nat)
    (s0 : State) : SepProp :=
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    coinsInstalledPlaced x.coinsP x.coins ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    FromRecordCallees.lsLogOff ∗ A.pool ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s0.sp stk

/-- Relocatable Stage 1 (`0x0000 → 0x0390` and early `Err` exits) on `initProgPlaced`. -/
theorem initiate_stage1_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop}
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hStore : InitStoreCalleesPlaced A mmpl gh W B stk)
    (hLocal : InitLocalCalleesPlaced A mmpl gh W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (_hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs0 : AtInitEntryPlaced x s0)
    (hpost : ∀ sf Pf, InitExitPostPlaced A S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPostPlaced A S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State) (be : PreKeyBundleFields),
      AtStage2Placed W X x be s0 s2 →
      SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s2
        (stage2MemPlaced A x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgPlaced mmpl gh W) (s0.readReg64 .lr) s0
      (initEntryMemPlaced A x stk s0) Q Qp (initOom s0) := by
  unfold initEntryMemPlaced
  refine Stage1Lemmas.stage1_prologue_trust_placed_ok hh hStore hS hinitOk hstk hstk64
    hs0 hpost hpanic fun s1 h1 h2 h3 hctrl1 htr1 hfs1 htrust => ?_
  refine Stage1Lemmas.stage1_spk_sig_placed_ok hh hLocal hS hstk hstk64 hs0.x8
    h1 h2 h3 hctrl1 htr1 hfs1 htrust hpost hpanic fun s2 hctrl2 htr2 hfs2 hspkSig => ?_
  refine Stage1Lemmas.stage1_kpk_sig_placed_ok hh hLocal hS hstk hstk64 hs0.x8
    h1 h2 h3 hctrl2 htr2 hfs2 htrust hspkSig hpost hpanic fun s3 hctrl3 htr3 hfs3 hsigs => ?_
  exact Stage1Lemmas.stage1_load_session_placed_ok hh hStore hinitOk hstk hstk64 hs0.x8
    (Stage1Lemmas.bundleEOf_eq_some_mkBundleE x.bundle h1 h2 h3)
    hctrl3 htr3 hfs3 htrust hsigs hpanic hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
