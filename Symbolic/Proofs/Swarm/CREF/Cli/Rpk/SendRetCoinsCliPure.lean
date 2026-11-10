/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.TRREF.B3DefsPure -- shake: keep

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.TripleRatchet
open CryptoVerification
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR

section EvalSendWireBridge

theorem gamma_computeMac_tr (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (macKeyTerm myIk peerIk wire : DY.Bytes) (sender receiver : IdentityKey) (macKeyBv : BitVec 256)
    (hkey : keyToBytes32 macKeyBv = gamma interpretation S g macKeyTerm)
    (hsender : sender.serialize = gamma interpretation S g myIk)
    (hreceiver : receiver.serialize = gamma interpretation S g peerIk)
    (content : List (BitVec 8)) (hwire : content = gamma interpretation S g wire) :
    CryptoGames.LibsignalSession.computeMac (sha256CompressFunction interpretation) sender receiver macKeyBv content =
    gamma interpretation S g (DY.Libsignal.TripleRatchet.computeMac macKeyTerm myIk peerIk wire) := by
  change CryptoGames.HMAC.hmacSha256Trunc8 (sha256CompressFunction interpretation) (keyToBytes32 macKeyBv) ((sender.serialize ++ receiver.serialize) ++ content) =
    gamma interpretation S g (DY.Trunc.trunc8 (DY.KdfExtract.kdfExtract macKeyTerm (DY.Concat.concat myIk (DY.Concat.concat peerIk wire))))
  rw [gamma_trunc8_tr, gamma_kdfExtract_tr, gamma_concat_tr, gamma_concat_tr, hkey, hsender, hreceiver, hwire, List.append_assoc]; rfl

end EvalSendWireBridge

end Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins
