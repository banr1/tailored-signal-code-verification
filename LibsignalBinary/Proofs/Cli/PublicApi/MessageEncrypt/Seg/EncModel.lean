/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Callees
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKit
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks
import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Drops
import LibsignalBinary.Proofs.Cli.TripleRatchet.Getters.Drops.Chain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From

/-!
# CLI `MessageEncrypt` Pure Model Equations

Pure specification-level equations connecting per-segment transitions of `MessageEncrypt` to the
overall `sessionMessageEncrypt` state machine on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.EncModel

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.EncModel.encCallees_of_calleeProofs_trap {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (hA : AllocHooks A (trTrapExterns C abs))
    (hEnc : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ_trap Q img C A ctl uuidTryParse S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hUnack : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.UnackItemsOk_trap img C A abs)
    (hKyber : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_trap img C A abs)
    (hPsm : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewOk_trap img C A abs)
    (hCmDrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_trap img C A abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees_trap Q img C A ctl uuidTryParse S abs :=
  let hA_abs : AllocHooks A abs := (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.allocHooks_trTrap_iff C A abs).mp hA
  let hAC : AllocContracts img.base A (trTrapExterns C abs) :=
    AllocContracts.of_tripleRatchetProgAt_trap img.base C A abs hA_abs
  { otrFrom := OutgoingRatchet.otrFrom_ok_ext himg hAC
      (Glue.deserializeOk_ext img.base (trTrapExterns C abs))
      (Glue.remoteIdentityKeyOk_ext img A (trTrapExterns C abs) himg)
      (Glue.dropSpeOk_ext himg hAC)
    otrApply := OutgoingRatchet.otrApply_ok_ext img A (trTrapExterns C abs) hAC
    remoteIk := Glue.remoteIdentityKeyOk_ext img A (trTrapExterns C abs) himg
    otrEnc := hEnc
    unack := hUnack
    kyber := hKyber
    psmNew := hPsm
    cmDrop := hCmDrop
    dropSs := CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure_local2_ok_ext hAC
      (CryptoVerification.Cli.LibsignalTripleRatchet.Getters.drop_chain_ok_ext hAC) }

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.EncModel.encCallees_of_calleeProofs_noSessionStore {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h3 : PublicApiHooksNoSessionStore C A S abs)
    (hEnc : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ Q img C A ctl uuidTryParse S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hUnack : UnackItemsOk img C A ctl abs)
    (hKyber : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk img C A ctl abs)
    (hPsm : PreKeyMsgNewOk img C A ctl abs)
    (hCmDrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk img C A ctl abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees Q img C A ctl uuidTryParse S abs where
  otrFrom := OutgoingRatchet.otrFrom_ok himg h3.alloc (Glue.deserializeOk img.base C ctl abs)
    (Glue.remoteIdentityKeyOk img C A ctl abs himg)
    (Glue.dropSpeOk_of_tripleRatchetHooks himg h3.toTripleRatchetHooks)
  otrApply := OutgoingRatchet.otrApply_ok img C A S ctl abs h3.toTripleRatchetHooks
  remoteIk := Glue.remoteIdentityKeyOk img C A ctl abs himg
  otrEnc := hEnc
  unack := hUnack
  kyber := hKyber
  psmNew := hPsm
  cmDrop := hCmDrop
  dropSs := CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.drop_session_structure_local2_ok h3.alloc (CryptoVerification.Cli.LibsignalTripleRatchet.Glue.drop_chain_ok_of_tripleRatchetHooks h3.toTripleRatchetHooks)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.EncModel.encCallees_of_calleeProofs {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (h3 : PublicApiHooks C A S encRecord abs)
    (hEnc : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ Q img C A ctl uuidTryParse S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hUnack : UnackItemsOk img C A ctl abs)
    (hKyber : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk img C A ctl abs)
    (hPsm : PreKeyMsgNewOk img C A ctl abs)
    (hCmDrop : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk img C A ctl abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees Q img C A ctl uuidTryParse S abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.EncModel.encCallees_of_calleeProofs_noSessionStore (PublicApiHooks.toNoSessionStore h3) hEnc himg hUnack hKyber hPsm hCmDrop

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.EncModel
