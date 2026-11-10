/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureVtablesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StoreSessionPrev1Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Placed CLI Poll Overwrite-Path (`Path C`) `Prev1` Session-Store Kit

Relocatable (`[LibsignalPlacement]`) counterpart of `Over/PollOverP4.lean`, defining
`cliPollSessPrev1KitPlaced` and `cliPollStorePrev1OpsPlaced` and instantiating the placed `Prev1`
`SessionStore::store_session` poll contract on `dpPollProgPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Placed `Prev1` Session-Store Kit (`cliPollSessPrev1KitPlaced`) & `StorePrev1Ops` -/

/-- Placed CLI `SessionStoreSpec` for Stage P4 on overwrite Path C (`previous_sessions = [enc]`):
shares `ss_vt = lsρ cliSessionVtSym`, `id_vt = lsρ cliIdentityVtSym`, and stack budgets with
`cliPollSessKitPlaced`, while weakening `storeAt` to `cliSessPrev1StoreAt`. -/
def cliPollSessPrev1KitPlaced [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) : SessionStoreSpec A 0#64 :=
  { cliPollSessPrev1Kit A 0#64 F0 peer σ with
    ss_vt := lsρ cliSessionVtSym
    id_vt := lsρ cliIdentityVtSym
    loadShimOff := lsmpl.base 604
    storeShimOff := lsmpl.base 605
    loadFutVtOff := lsρ sessLoadFutVtSym
    storeFutVtOff := lsρ sessStoreFutVtSym
    loadPollOff := lsmpl.base 569
    storePollOff := lsmpl.base 570
    loadFutDropOff := lsDropOffPlaced
    storeFutDropOff := lsDropOffPlaced
    loadFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    storeFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

theorem cliPollSessKitPlaced_storeAt_entails_prev1 [LibsignalPlacement] {A : RustAlloc}
    {F0 : FsFiles} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {σ : DpKitStk} (self : BitVec 64) (d : DirGhost) :
    (cliPollSessKitPlaced A F0 Scope peer σ).storeAt self d ⊢
      (cliPollSessPrev1KitPlaced A F0 peer σ).storeAt self d :=
  cliPollSessKit_storeAt_entails_prev1 (A := A) (b := 0#64) (F0 := F0)
    (Scope := Scope) (peer := peer) (σ := σ) self d

/-- `Over.StorePrev1Ops` instance for `cliPollSessPrev1KitPlaced`. -/
def cliPollStorePrev1OpsPlaced [LibsignalPlacement] {A : RustAlloc}
    {F0 : FsFiles} {peer : AddrGhost} {σ : DpKitStk} :
    Over.StorePrev1Ops (cliPollSessPrev1KitPlaced A F0 peer σ) where
  RecPrev1Ok := fun G sess enc =>
    E2E.Record.Serialization.CanonSession G sess ∧
    (Over.encodeRecordPrev1 sess enc).length < 2 ^ 32
  storeRelPrev1 := fun _ _ _ _ _ ans => ans = .ok ()
  storeUpdatePrev1 := fun d rem _ sess enc _ =>
    d.put (Cli.addressText rem) (Over.encodeRecordPrev1 sess enc)
  storeEvsPrev1 := fun _ _ _ _ _ => []

theorem cliPollSessPrev1Placed_quiet [LibsignalPlacement] {A : RustAlloc}
    (F0 : FsFiles) (peer : AddrGhost) (σ : DpKitStk) :
    (cliPollSessPrev1KitPlaced A F0 peer σ).Quiet :=
  ⟨fun _ _ _ => NoFsEv.nil, fun _ _ _ _ => NoFsEv.nil⟩

/-! ## 2. Placed `store_session` Poll Contract on `Prev1` -/

theorem cliPollSessPrev1_storePoll_placed_of_mem [LibsignalPlacement] {prog : Program}
    {entry : BitVec 64} {stk : Nat}
    (hMem : subroutine_ok prog entry
      (Store.StoreSessionPrev1.sessStorePollPrev1MemSpecPlaced E2E.HooksE.A0 stk)) :
    subroutine_ok prog entry
      (Store.StoreSessionPrev1.sessStorePollPrev1SpecPlaced E2E.HooksE.A0 stk) :=
  Store.StoreSessionPrev1.sessStorePollPrev1_placed_of_mem hMem

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
