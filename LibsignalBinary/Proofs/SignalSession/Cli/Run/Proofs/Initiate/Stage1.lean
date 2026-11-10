/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage1Lemmas.SegSigsLoad
/-!
# Stage 1 (`0x0000 → 0x0390`): Prologue, Trust Check, Bundle Signatures, and `load_session`

Verifies Stage 1 of `signal_session_handshake::initiate` from entry (`0x0000`) to `AtStage2`
(`0x0390`) together with its early `Err` exits (`0x0350 → ret`):
1. Prologue allocating `cliInitiateFrame = 7408` bytes and storing `initArgsAt` at `[fsp + 0xd0, fsp + 0x128)`.
2. `is_trusted_identity(peer, &bundle.idKey)` (`Err` / OOM or `Ok(false)` → `UntrustedIdentity`).
3. Signed pre-key and Kyber pre-key XEdDSA signature checks (`verify_signature`, rejecting with `SpeOwned.plain 11`).
4. `load_session(peer)` yielding `Ok(None)` under `InitOk₀.noSession` and establishing `AtStage2`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Spatial entry footprint of `initSlotSpec` after extracting pure preconditions. -/
def initEntryMem (A : RustAlloc) (img : Obj.Image) (x : InitGhost) (stk : Nat)
    (s0 : State) : SepProp :=
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    coinsInstalled img x.coinsP x.coins ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    logOff img ∗ A.pool ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s0.sp stk

/-- Stage 1 (`0x0000 → 0x0390` and early `Err` exits) on `initProg img W`. -/
theorem initiate_stage1_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {stk : Nat} {s0 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hStore : InitStoreCallees img A W B stk)
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs0 : AtInitEntry img W x s0)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State) (be : PreKeyBundleFields),
      AtStage2 img W X x be s0 s2 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s2
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s0
      (initEntryMem A img x stk s0) Q Qp (initOom s0) := by
  unfold initEntryMem
  refine Stage1Lemmas.stage1_prologue_trust_ok himg hh hStore hS hinitOk hstk hstk64
    hs0 hpost hpanic fun s1 h1 h2 h3 hctrl1 htr1 hfs1 htrust => ?_
  refine Stage1Lemmas.stage1_spk_sig_ok hh hLocal hS hstk hstk64 hs0.x8
    h1 h2 h3 hctrl1 htr1 hfs1 htrust hpost hpanic fun s2 hctrl2 htr2 hfs2 hspkSig => ?_
  refine Stage1Lemmas.stage1_kpk_sig_ok hh hLocal hS hstk hstk64 hs0.x8
    h1 h2 h3 hctrl2 htr2 hfs2 htrust hspkSig hpost hpanic fun s3 hctrl3 htr3 hfs3 hsigs => ?_
  exact Stage1Lemmas.stage1_load_session_ok himg hh hStore hinitOk hstk hstk64 hs0.x8
    (Stage1Lemmas.bundleEOf_eq_some_mkBundleE x.bundle h1 h2 h3)
    hctrl3 htr3 hfs3 htrust hsigs hpanic hnext

/-- Stage 1 (`0x0000 → 0x0390` and early `Err` exits) on `initProgExt img ext` from `RunHooksExt` at residual stack `calStk ≤ stk - cliInitiateFrame`. -/
theorem initiate_stage1_ext_ok_of_hooks {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {calStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hcal : calStk ≤ stk - cliInitiateFrame)
    (hVerify : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliVerifySignatureName)
      ((Stage1Lemmas.verifySigAtStkSpec (modelPrims X P) calStk).inImage img))
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} {Q Qp : State → SepProp → Prop}
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (_hcoinsLt : x.coins.length < 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs0 : AtInitEntryExt img ext x s0)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State) (be : PreKeyBundleFields),
      AtStage2Ext img P ext X x be s0 s2 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s0
      (initEntryMem A img x stk s0) Q Qp (initOom s0) := by
  unfold initEntryMem
  refine Stage1Lemmas.stage1_prologue_trust_ext_ok himg hh hStore hS hinitOk hstk hstk64
    hs0 hpost hpanic fun s1 h1 h2 h3 hctrl1 htr1 hfs1 htrust => ?_
  refine Stage1Lemmas.stage1_spk_sig_ext_ok hh hcal hVerify hS hstk hstk64 hs0.x8
    h1 h2 h3 hctrl1 htr1 hfs1 htrust hpost hpanic fun s2 hctrl2 htr2 hfs2 hspkSig => ?_
  refine Stage1Lemmas.stage1_kpk_sig_ext_ok hh hcal hVerify hS hstk hstk64 hs0.x8
    h1 h2 h3 hctrl2 htr2 hfs2 htrust hspkSig hpost hpanic fun s3 hctrl3 htr3 hfs3 hsigs => ?_
  exact Stage1Lemmas.stage1_load_session_ext_ok himg hh hStore hinitOk hstk hstk64 hs0.x8
    (Stage1Lemmas.bundleEOf_eq_some_mkBundleE x.bundle h1 h2 h3)
    hctrl3 htr3 hfs3 htrust hsigs hpanic hnext

/-- Stage 1 on `initProgExt img ext` from `CliExternsOk P A ext` at residual stack `calStk ≤ stk - cliInitiateFrame`. -/
theorem initiate_stage1_ext_ok_at_stk {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {calStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hcal : calStk ≤ stk - cliInitiateFrame)
    (hVerify : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliVerifySignatureName)
      ((Stage1Lemmas.verifySigAtStkSpec (modelPrims X P) calStk).inImage img))
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} {Q Qp : State → SepProp → Prop}
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs0 : AtInitEntryExt img ext x s0)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State) (be : PreKeyBundleFields),
      AtStage2Ext img P ext X x be s0 s2 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s0
      (initEntryMem A img x stk s0) Q Qp (initOom s0) :=
  initiate_stage1_ext_ok_of_hooks himg (RunHooksExt.of_externsOk hOk img) hcal hVerify hS
    hstk hstk64 hStore hinitOk hcoinsLt hspk hs0 hpost hpanic hnext

/-- Stage 1 on `initProgExt img ext` from `CliExternsOk P A ext` and `verifySignatureSpec`, matching `cliInitiate_ext_ok_of_stages`. -/
theorem initiate_stage1_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hVerify : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliVerifySignatureName)
      (verifySignatureSpec (modelPrims X P) img))
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {s0 : State} {Q Qp : State → SepProp → Prop}
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs0 : AtInitEntryExt img ext x s0)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s2 : State) (be : PreKeyBundleFields),
      AtStage2Ext img P ext X x be s0 s2 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
        (stage2Mem A img x stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s0
      (initEntryMem A img x stk s0) Q Qp (initOom s0) := by
  have hspecEq : verifySignatureSpec (modelPrims X P) img =
      (Stage1Lemmas.verifySigAtStkSpec (modelPrims X P)
        (Pqxdh.Shared.pqxdhHookStack + 1280)).inImage img := rfl
  rw [hspecEq] at hVerify
  have hcal : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ stk - cliInitiateFrame := by
    have hb := stk_sub_ge_base hstk
    have hp : Pqxdh.Shared.pqxdhHookStack + 1280 ≤ 516880 := by decide
    omega
  exact initiate_stage1_ext_ok_at_stk himg hOk hcal hVerify hS hstk hstk64
    hStore hinitOk hcoinsLt hspk hs0 hpost hpanic hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
