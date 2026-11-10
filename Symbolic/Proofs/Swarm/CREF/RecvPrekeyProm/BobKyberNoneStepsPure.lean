/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.OooRpkPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# `PureBobKyberNone` Preservation on Session Promotion

Proves `bobKyberNone_post_promoteWireRecCanon`, showing that `PureBobKyberNone` holds on the
post-state record of an accepting promote call.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record (encodeRecord)
open Symbolic.Swarm.CREF.TR.Pure (WireRecCanon)
open Symbolic.Swarm.CREF.CliPure.RpkCli

theorem bobKyberNone_post_promoteWireRecCanon
    {r : ProtocolSetup} {records : Participant → Option HwBytes}
    {rec newState : HwBytes} {sess sess' : Session HwBytes} {rr : RecordRec}
    (hbob : PureBobKyberNone r records)
    (hrec : records r.bob = some rec)
    (hrc : Symbolic.Swarm.CREF.TR.Pure.slots_RecordCanonical_Q Symbolic.Swarm.CREF.TR.Pure.slots_NonEmptyV1Q rec sess)
    (hkyb : sess'.pendingKyberPreKey = sess.pendingKyberPreKey)
    (henc : newState = encodeRecord ⟨some sess'⟩)
    (hwc : WireRecCanon newState)
    (hrr : newState = recordBytes rr) :
    rr.current.pendingKyberPreKey = none := by
  have ⟨_, hbs_in⟩ := RpkCli.recordBytes_sessionToRecordRecPending_of_canonical_Q hrc
  have hkyb0 : sess.pendingKyberPreKey = none :=
    (sessionToRecordRecPending_pendingKyberPreKey_eq_none_iff sess).mp
      (hbob (sessionToRecordRecPending sess) (hbs_in ▸ hrec))
  obtain ⟨_, _, _, _, _, h62, _⟩ := hwc
  exact pendingKyberPreKey_eq_none_of_encodeRecord_lt henc (by omega) (hkyb.trans hkyb0) hrr

end Symbolic.Swarm.CREF.CliPure
