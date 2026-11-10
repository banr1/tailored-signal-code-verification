/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeysA
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DeriveKeys

/-!
# Stage 3 (`0x0760 → 0x10a4`): PQXDH Diffie-Hellman Agreements, KEM Encapsulation, and `HandshakeKeys::derive`

Verifies Stage 3 of `signal_session_handshake::initiate` from `AtStage3` (`0x0760`) to `AtStage4`
(`0x10a4`) together with its early `Err` and OOM exits:
1. Allocates the 192-byte `secrets` buffer and writes the 32-byte `0xFF` discontinuity prefix.
2. Computes `DH1..DH3` and optional `DH4` via `<PrivateKey>::calculate_agreement` (rejecting all-zero
   outputs with `SpeOwned.plain 7` and keeping `cap = 192` so `do_reserve_and_handle` is unreachable).
3. Executes 32 unrolled `signal_session_coins_fill(dst, 4)` calls (`pos: 32 → 160`) to form
   `initiateKemCoins (padCoins x.coins)`.
4. Runs `kyber::encapsulate`, boxes `kemSs` and `kemCt`, serializes `kemCt` (`1569` bytes), appends
   `kemSs` to `secrets`, invokes `<HandshakeKeys>::derive`, frees `secrets`, and reaches `0x10a4`.
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

/-- Stage 3 (`0x0760 → 0x10a4` and early `Err` / OOM exits) on `initProg img W`. -/
theorem initiate_stage3_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {stk : Nat} {s0 s3 : State}
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
    (hs3 : AtStage3 img W X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4 img W X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId
        s0 s4 →
      SepWPp (initProg img W) (s0.readReg64 .lr) s4
        (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0)) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s3
      (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0) :=
  Stage3Lemmas.stage3_all_ok hh @hCoins hLocal hS hcoinsLt
    hstk hstk64 hs3 hpost hpanic hnext

/-! ## Extern-parameterized Stage 3 (`CliExternsOk`) -/

/-- Stage 3 local callee bundle on `initProgExt img ext` (`kem::Ciphertext::serialize` and `HandshakeKeys::derive`). -/
structure Stage3CalleesExt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  kemCtSerialize :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliKemCtSerializeName)
      (Stage3Lemmas.kemCiphertextSerializeExtSpec A)
  handshakeDerive : ∀ X : UnreachedPqxdhPrimitives,
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliHandshakeDeriveName)
      (E2E.Pqxdh.Initiator.handshakeKeysDeriveSpecExt (modelPrims X P) A img)

/-- Stage 3 (`0x0760 → 0x10a4` and early `Err` / OOM exits) on `initProgExt img ext` under `CliExternsOk P A ext`. -/
theorem initiate_stage3_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hLocal : Stage3CalleesExt img P A ext)
    (hS : S.initiate = initDef X P)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {s0 s3 : State}
    {Q Qp : State → SepProp → Prop}
    (hCoins : ∀ {cStk : Nat}, cliCoinsFillStack ≤ cStk → cStk ≤ 2 ^ 63 →
      subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr cliCoinsFillName)
        (coinsFillSpec img cStk))
    (_hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (_hspk : stk ≤ s0.sp.toNat)
    (hs3 : AtStage3Ext img P ext X x be kp ekASk ekAPk pqspkPtr opkId s0 s3)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf)
    (hnext : ∀ (s4 : State) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
        (kemCtBytes hkSlotBytes : List (BitVec 8)) (kemCtPtr : BitVec 64),
      AtStage4Ext img P ext X x be kp ekASk ekAPk dk hdr kemCtBytes hkSlotBytes pqspkPtr kemCtPtr
        opkId s0 s4 →
      SepWPp (initProgExt img ext) (s0.readReg64 .lr) s4
        (stage4Mem A img x kp ekASk ekAPk kemCtBytes hkSlotBytes pqspkPtr kemCtPtr opkId stk s0)
        Q Qp (initOom s0)) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s3
      (stage3Mem A img x kp ekASk ekAPk pqspkPtr opkId stk s0) Q Qp (initOom s0) :=
  Stage3Lemmas.stage3_all_ok_ext hOk @hCoins
    (fun X' => Stage3Lemmas.Ext.calculateAgreement_frozen_ok_of_specExt himg
      (E2E.Pqxdh.ResponderCore.pqxdhCalculateAgreement_ok_of_cliExternsOk X' himg hOk))
    hLocal.kemCtSerialize hLocal.handshakeDerive hS hcoinsLt
    hstk hstk64 hs3 hpost hpanic hnext

abbrev initiate_stage3_ok_ext := @initiate_stage3_ext_ok

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
