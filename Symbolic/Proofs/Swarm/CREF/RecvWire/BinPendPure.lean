/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PureRecvEval
import Symbolic.Proofs.Swarm.TRREF.EncodeRecordPqInj

/-!
# Entry Record Canonicity under `PureCRecRel`

Defines `TRRecordCanonPend` for records that may still carry Alice's pending pre-key and
derives it from `PureCRecRel` together with `SpqrOooBounded` and the input length bound.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open Symbolic.Swarm.TRREF.EncodeRecordPqInj (encodeRecord_pq_inj_of_eq)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPureRcv

/-- `TRRecordCanon` without the `pendingPreKey = none` conjunct (the record may carry Alice's
pending pre-key). -/
def TRRecordCanonPend (recBytes : HwBytes) : Prop :=
  ∃ sess : Session (List (BitVec 8)),
    TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes sess ∧
    TR.Pure.slots_RecordInScopeP ⟨some sess⟩ ∧
    TR.Pure.slots_RecordScopeP TR.Pure.slots_NonEmptyV1Q ⟨some sess⟩ ∧
    sess.state.remoteIdentity.isSome ∧
    recBytes.length < 2 ^ 62 ∧
    recBytes.length < 2 ^ 32 - 2 ^ 20 ∧
    SpqrOooBounded sess.state.pqRatchetState

theorem ooo_of_trRecordCanonPend {recBytes : List (BitVec 8)}
    {gs : Session (List (BitVec 8))}
    (hcanonP : TRRecordCanonPend recBytes)
    (hrc : TR.Pure.slots_RecordCanonical_Q TR.Pure.slots_NonEmptyV1Q recBytes gs) :
    SpqrOooBounded gs.state.pqRatchetState ∧ gs.state.pqRatchetState.length < 2 ^ 32 := by
  obtain ⟨sess₀, hrc₀, -, -, -, h62, -, hooo₀⟩ := hcanonP
  have hpq : sess₀.state.pqRatchetState = gs.state.pqRatchetState :=
    encodeRecord_pq_inj_of_eq hrc₀.1 hrc.1 h62
  obtain ⟨-, -, _, _, _, _, _, hpqlen, _⟩ := hrc
  exact ⟨hpq ▸ hooo₀, hpqlen⟩

theorem rcv_canonPend_of_pending {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ms : List Move} {rec : HwBytes}
    (hp : PureAliceInitPending interpretation r S g ms rec)
    (hooo : SpqrOooBounded (pqStateOf rec)) (hlen : rec.length < 2 ^ 32 - 2 ^ 20) :
    TRRecordCanonPend rec ∧
      ∃ rr : RecordRec, rec = recordBytes rr ∧ rr.current.sessionVersion = 4#32 := by
  obtain ⟨sess, _sc, remote, _items, _kpk, _st, _stateIdx, _ekIdx, _ctIdx, _ek, _ct,
    hcanon, hscope, hscopeP, _h4, _h5, _h6, _h7, _h8, _h9, _h10, _h11, _h12, _h13, hrem,
    _h15, _h16, _h17, _h18, _h19, _h20, _h21, _h22, _h23, _h24, _h25, rr, hb, hst_rel, _⟩ := hp
  refine ⟨⟨sess, hcanon, hscope, hscopeP, by rw [hrem]; rfl, by omega, hlen, ?_⟩,
    rr, hb, congrArg SessionRec.sessionVersion hst_rel.2⟩
  rw [← TR.PureRecvEval.pqStateOf_of_pureCanonical_Q hcanon]
  exact hooo

/-- Any record satisfying `PureCRecRel`, `SpqrOooBounded`, and the input length bound satisfies
`TRRecordCanonPend` and decodes to a version-4 `RecordRec`. -/
theorem rcv_canonPend_of_recRel {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms : List Move} {p : Participant} {rec : HwBytes}
    (hcr : PureCRecRel interpretation r S g ms p rec)
    (hooo : SpqrOooBounded (pqStateOf rec)) (hlen : rec.length < 2 ^ 32 - 2 ^ 20) :
    TRRecordCanonPend rec ∧
      ∃ rr : RecordRec, rec = recordBytes rr ∧ rr.current.sessionVersion = 4#32 := by
  rcases hcr with htr | ⟨_, hp⟩
  · obtain ⟨_, rr, _st, _, hb, _, _, hst_rel, _, hcanon, _, _⟩ := htr p rec (by simp)
    obtain ⟨sess, hq, hs, hsq, hrem, h62, _, h32, hooo'⟩ := hcanon hlen
    exact ⟨⟨sess, hq, hs, hsq, hrem, h62, h32, hooo'⟩, rr, hb,
      congrArg SessionRec.sessionVersion hst_rel.2⟩
  · exact rcv_canonPend_of_pending hp hooo hlen

end Symbolic.Swarm.CREF.CliPureRcv.RecvWirePure
