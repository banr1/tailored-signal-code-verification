/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.SegA

/-!
# Stage 2 (`0x0390 → 0x0760`): Ephemeral Base Key, `get_identity_key_pair`, `pqspkB`, and `is_same_account`

Verifies Stage 2 of `signal_session_handshake::initiate` from `AtStage2` (`0x0390`) to `AtStage3`
(`0x0760`) together with its early `Err` and OOM exits:
1. Draws 32 coin bytes via `signal_session_coins_fill`, clamps `ekASk`, and derives `ekAPk`.
2. Polls `get_identity_key_pair` (`Err` unwinds the fresh `SessionRecord`; `Ok(kp)` satisfies `InitOk₀.idPairDerived`).
3. Clones the 1568-byte Kyber pre-key (`pqspkPtr`, panicking cleanly on OOM).
4. Checks `<IdentityKey>::is_same_account` (`false` under `InitOk₀.distinctAcct`) and unpacks `bundle.opk`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Stage 2 (`0x0390 → 0x0760` and early `Err` / OOM exits) on `initProg img W`. -/
theorem initiate_stage2_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {stk : Nat} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hStore : InitStoreCallees img A W B stk)
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs2 : AtStage2 img W X x be s0 s2)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32),
      AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s3
        (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s2
      (stage2Mem A img x stk s0) Q Qp (initOom s0) := by
  exact Stage2Lemmas.segA_ok himg hh @hCoins hStore hLocal hS hinitOk hcoinsLt hstk hstk64
    hs2 hpost hpanic hnext

/-- Builds `Stage2CalleesExt` from `CliExternsOk P A ext` and `.inImage img`-scoped `is_same_account` at `isaStk ≤ 516880`. -/
theorem stage2CalleesExt_of_subroutines {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {isaStk : Nat}
    (hOk : CliExternsOk P A ext)
    (hisa : isaStk ≤ 516880)
    (hSameAcct : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliIsSameAccountName)
      ((Stage2Lemmas.isSameAccountDistinctAtSpec A uuidTryParse isaStk).inImage img)) :
    Stage2Lemmas.Stage2CalleesExt img P A ext :=
  Stage2Lemmas.stage2CalleesExt_of_externsOk hOk hisa hSameAcct

/-- Builds `Stage2CalleesExt` from `CliExternsOk P A ext` and unscoped `isSameAccountDistinctAtSpec`. -/
theorem stage2CalleesExt_of_isSameAccount {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {isaStk : Nat}
    (hOk : CliExternsOk P A ext)
    (hisa : isaStk ≤ 516880)
    (hSameAcct : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliIsSameAccountName)
      (Stage2Lemmas.isSameAccountDistinctAtSpec A uuidTryParse isaStk)) :
    Stage2Lemmas.Stage2CalleesExt img P A ext :=
  Stage2Lemmas.stage2CalleesExt_of_externsOk hOk hisa
    (subroutine_ok_inImage_of_subroutine_ok img hSameAcct)

/-- Stage 2 (`0x0390 → 0x0760` and early `Err` / OOM exits) on `initProgExt img ext` from `RunHooksExt` and `Stage2CalleesExt`. -/
theorem initiate_stage2_ok_ext_with_hooks {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooksExt img A (cliExternsWith ext))
    (hLocal : Stage2Lemmas.Stage2CalleesExt img P A ext)
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {be : PreKeyBundleFields} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs2 : AtStage2Ext img P ext X x be s0 s2)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32),
      AtStage3Ext img P ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
        (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
      (stage2Mem A img x stk s0) Q Qp (initOom s0) :=
  Stage2Lemmas.segA_ok_ext himg hh @hCoins hStore hLocal hS hinitOk hcoinsLt hstk hstk64
    hs2 hpost hpanic hnext

/-- Stage 2 (`0x0390 → 0x0760` and early `Err` / OOM exits) on `initProgExt img ext` under `CliExternsOk P A ext`. -/
theorem initiate_stage2_ok_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hLocal : Stage2Lemmas.Stage2CalleesExt img P A ext)
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {be : PreKeyBundleFields} {s0 s2 : State}
    {Q Qp : State → SepProp → Prop}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs2 : AtStage2Ext img P ext X x be s0 s2)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s3 : State) (kp : IdentityKeyPair) (ekASk ekAPk : List (BitVec 8))
        (pqspkPtr : BitVec 64) (opkId : BitVec 32),
      AtStage3Ext img P ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
        (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s2
      (stage2Mem A img x stk s0) Q Qp (initOom s0) :=
  initiate_stage2_ok_ext_with_hooks himg (RunHooksExt.of_externsOk hOk img) hLocal hS hstk hstk64
    @hCoins hStore hinitOk hcoinsLt hspk hs2 hpost hpanic hnext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
