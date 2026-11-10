/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Top
/-!
# Stage 4: Ratchet Chain, SPQR Initial State, and `SessionState` Construction

Verifies `signal_session_handshake::initiate` from `+0x10a4` (`BB129`) to `+0x1484` (`BB143`):
draws and clamps the sender ratchet key `ephA`, runs `<RootKey>::create_chain` (unwinding with
`SpeOwned.plain 7` on non-contributory DH failure), initializes SPQR state via
`spqr_chain_params(false)` and `spqr::initial_state`, constructs the `344`-byte `SessionState`
at `[fsp + 0x460, fsp + 0x5b8)` (`[fsp + 0x5b9] := 1#8`), and takes the `logOff` branch directly
to `+0x1484`.
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

/-- Stage 4 (`+0x10a4 → +0x1484` and early `Err` / OOM exits). -/
theorem initiate_stage4_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {kemCtBytes hkSlotBytes : List (BitVec 8)}
    {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s4 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hh : RunHooks img A (cliExterns W))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProg img W) ((initProg img W).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hLocal : InitLocalCallees img A W stk)
    (hS : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (hinitOk : InitOk₀ ⟨W.C, W.Q⟩ x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs4 : AtStage4 img W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
      opkId s0 s4)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s5 : State) (sg : SessionGhost) (ss : SessionState (List (BitVec 8))),
      AtStage5 img W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s5
        (stage5Mem A img x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s4
      (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
      Q Qp (initOom s0) := by
  exact Stage4Lemmas.initiate_stage4_ok_impl himg hh hCoins hLocal hS hinitOk hcoinsLt
    hstk hstk64 hspk hs4 hpost hpanic hnext

/-- Assembles `Stage4CalleesExt` from `CliExternsOk P A ext` and the seven non-hook local
subroutines invoked in Stage 4. -/
theorem stage4CalleesExt_of_subroutines {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CliExternsOk P A ext)
    (hCreateChain : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliRootKeyCreateChainName)
      ((createChainSpecX P.C A).inImage img))
    (hSpqrParams : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSpqrChainParamsName)
      Pqxdh.spqrChainParamsSpec)
    (hSpqrInit : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSpqrInitialStateName)
      (CryptoVerification.SpqrV1.Top.InitialState.initialStateSpecX A P.C.F img))
    (hSessNew : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSessionStateNewName)
      (Pqxdh.Initiator.sessionStateNewSpec A img))
    (hWithRecv : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliWithReceiverChainName)
      (Pqxdh.Initiator.withReceiverChainEmptySpec A img))
    (hWithSend : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliWithSenderChainName)
      (Pqxdh.Initiator.withSenderChainNoneSpec A img))
    (hSetKyber : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSetKyberCiphertextName)
      Pqxdh.setKyberCiphertextNoneSpec) :
    Stage4Lemmas.Stage4CalleesExt img P A ext :=
  { derivePubKeyBytes := Stage4Lemmas.derivePubKeyBytes_ok_ext img hOk
    rootKeyCreateChain := hCreateChain
    spqrChainParams := hSpqrParams
    spqrInitialState := hSpqrInit
    sessionStateNew := hSessNew
    withReceiverChain := hWithRecv
    withSenderChain := hWithSend
    setKyberCiphertext := hSetKyber }

/-- Contract-parameterized Stage 4 (`+0x10a4 → +0x1484` and early `Err` / OOM exits) under
`CliExternsOk P A ext`. -/
theorem initiate_stage4_ok_ext {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {kemCtBytes hkSlotBytes : List (BitVec 8)}
    {pqspkPtr kemCtPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s4 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hh : RunHooks img A (cliExternsWith ext))
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (hLocal : Stage4Lemmas.Stage4CalleesExt img P A ext)
    (hS : S.initiate = initDef X P)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs4 : AtStage4Ext img P ext X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr
      kemCtPtr opkId s0 s4)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s5 : State) (sg : SessionGhost) (ss : SessionState (List (BitVec 8))),
      AtStage5Ext img P ext X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s5
        (stage5Mem A img x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s4
      (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
      Q Qp (initOom s0) := by
  exact Stage4Lemmas.initiate_stage4_ok_impl_ext himg hOk hh hCoins hLocal hS hinitOk hcoinsLt
    hstk hstk64 hspk
    { ctrl := ⟨hs4.ctrl.pc, hs4.ctrl.run, hs4.ctrl.sp, hs4.ctrl.fp, hs4.ctrl.x19,
        hs4.ctrl.files0, hs4.ctrl.inv, hs4.ctrl.vregs, hs4.ctrl.spAligned⟩
      trace := hs4.trace, files := hs4.files, x8 := hs4.x8, bundleEq := hs4.bundleEq
      trustedOk := hs4.trustedOk, kpOk := hs4.kpOk, ekPairEq := hs4.ekPairEq
      opkIdEq := hs4.opkIdEq, keysOk := hs4.keysOk, kemCtEq := hs4.kemCtEq
      hkSlotEq := hs4.hkSlotEq, pqspkNonNull := hs4.pqspkNonNull
      kemCtNonNull := hs4.kemCtNonNull, x20 := hs4.x20, x21 := hs4.x21, x22 := hs4.x22 }
    hpost hpanic (fun s5 sg ss hs5 => hnext s5 sg ss
      { ctrl := ⟨hs5.ctrl.pc, hs5.ctrl.run, hs5.ctrl.sp, hs5.ctrl.fp, hs5.ctrl.x19,
          hs5.ctrl.files0, hs5.ctrl.inv, hs5.ctrl.vregs, hs5.ctrl.spAligned⟩
        trace := hs5.trace, files := hs5.files, x8 := hs5.x8, bundleEq := hs5.bundleEq
        trustedOk := hs5.trustedOk, kpOk := hs5.kpOk, ekPairEq := hs5.ekPairEq
        opkIdEq := hs5.opkIdEq, keysOk := hs5.keysOk, initSessOk := hs5.initSessOk
        pqLen := hs5.pqLen, canonPre := hs5.canonPre, pqspkNonNull := hs5.pqspkNonNull
        x20 := hs5.x20 })

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
