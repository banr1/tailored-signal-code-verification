/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.CallKit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.EntryAndRegId
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatExt

/-!
# Stage 5: Unacknowledged PreKey Metadata, Registration ID, `save_identity`, `promote_state`, and `store_session`

Verifies `signal_session_handshake::initiate` from `+0x1484` (`BB143`) through the shared epilogue
(`+0x0350..+0x037c → ret`): sets unacknowledged PreKey and Kyber PreKey metadata, polls
`get_local_registration_id` (unwinding with `SpeOwned` on `Err`), runs `save_identity`,
`<SessionRecord>::promote_state`, and `store_session` on `Ok(reg)`, drops `SessionRecord` and
`pqspkB`, and returns `InitExitPost`.
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

/-- Stage 5 (`+0x1484 → ret` at `lr`, both `Ok(())` and `Err`). -/
theorem initiate_stage5_ok {img : Obj.Image} {A : RustAlloc}
    {W : CliHooks} {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
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
    (hs5 : AtStage5 img W X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProg img W) (s0.readReg64 .lr) s5
      (stage5Mem A img x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0)
      Q Qp (initOom s0) := by
  let _ := hspk
  exact Stage5Lemmas.initiate_stage5_ok_impl himg hh hStore hLocal hS hinitOk hcoinsLt
    hstk hstk64 hs5 hpost hpanic

/-- Assembles `Stage5CalleesExt` from `CliExternsOk P A ext` and the remaining local Stage 5
subroutine contracts (`dropSessionStructure`, `setUnackKyberId`, `promoteState`). -/
theorem stage5CalleesExt_of_subroutines {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image}
    (hOk : CliExternsOk P A ext)
    (hDropSS : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliDropSessionStructureName)
      (FromRecordCallees.dropSessionStructureLocal2Spec A))
    (hSetUnackKyb : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliSetUnackKyberIdName)
      Pqxdh.setUnackKyberPreKeyIdSpec)
    (hPromoteState : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliPromoteStateName)
      (Stage5Lemmas.promoteStateEmptyExtSpec img (extHookStack + 32))) :
    Stage5Lemmas.Stage5CalleesExt img A (cliExternsWith ext) :=
  { dropSessionStructure := hDropSS
    setUnackPreKeyMsg := Slots.setUnackPreKeyMsg_ext_stack_epoch_ok hOk
    setUnackKyberId := hSetUnackKyb
    promoteState := hPromoteState }

/-- Contract-parameterized Stage 5 (`+0x1484 → ret` at `lr`) under `CliExternsOk P A ext`. -/
theorem initiate_stage5_ext_ok {img : Obj.Image} {A : RustAlloc}
    {P : PEParams} {ext : String → Option (State → State)}
    {X : UnreachedPqxdhPrimitives} {B : RunBudgets} {S : RunSem}
    {x : InitGhost} {be : PreKeyBundleFields} {kp : IdentityKeyPair}
    {ekASk ekAPk : List (BitVec 8)} {dk : SignalPqxdh.DRKey} {hdr : SignalPqxdh.HandshakeHdr}
    {pqspkPtr : BitVec 64} {opkId : BitVec 32}
    {sg : SessionGhost} {ss : SessionState (List (BitVec 8))}
    {stk : Nat} {s0 s5 : State}
    {Q Qp : State → SepProp → Prop}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : CliExternsOk P A ext)
    (hStore : InitStoreCalleesExt img A (cliExternsWith ext) B stk)
    (hCal : Stage5Lemmas.Stage5CalleesExt img A (cliExternsWith ext))
    (hS : S.initiate = initDef X P)
    (hinitOk : InitOk₀ P x.F x.peer.val x.me.val)
    (hcoinsLt : x.coins.length < 2 ^ 63)
    (hstk : cliInitiateNeed B ≤ stk)
    (hstk64 : stk ≤ 2 ^ 63)
    (hspk : stk ≤ s0.sp.toNat)
    (hs5 : AtStage5Ext img P ext X x be kp ekASk ekAPk dk hdr sg ss pqspkPtr opkId s0 s5)
    (hpost : ∀ sf Pf, InitExitPost A img S x stk s0 sf Pf → Q sf Pf)
    (hpanic : ∀ sf Pf, InitPanicPost A img S x stk s0 sf Pf → Qp sf Pf) :
    SepWPp (initProgExt img ext) (s0.readReg64 .lr) s5
      (stage5Mem A img x kp ekASk ekAPk pqspkPtr opkId sg ss stk s0)
      Q Qp (initOom s0) := by
  let _ := hspk
  exact Stage5Lemmas.initiate_stage5_ok_impl_ext himg
    (Stage5Lemmas.stage5ExternDeps_of_alloc_and_fs
      (Slots.ext_allocContractsX hOk img)
      (initProgExt_traceFsSound img hOk))
    hStore hCal hS hinitOk hcoinsLt hstk hstk64
    (Stage5Lemmas.S5AtStage5.of_atStage5Ext hs5) hpost hpanic

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
