/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyPromModel
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.AcceptCliPure
public import Symbolic.Proofs.Swarm.CREF.Sem
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.SlotPure

/-!
# Promote Pre-Key Receive Accept Step Contract

Defines and proves `PurePromAcceptStepSpec` (`purePromAcceptStepSpec_proved`) for a matching-session
promote pre-key `recv` call from `PromPureAcceptOut`, `PureCRel`, `COpkRelC`, and `Clean`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (WireType encodeKey)
open DY.Libsignal.HwEvents (StateAndMessage)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli)

theorem rpkProm_encodeRecord_some_ne_nil (sess : Session HwBytes) :
    CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩ ≠ [] := by
  apply List.ne_nil_of_length_pos
  simp [CryptoVerification.E2E.Record.encodeRecord, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField,
    show (encodeKey 1 WireType.lengthDelimited).length = 1 by decide]

/-- Symbolic accept step specification for a matching-session promote pre-key `recv` call. -/
def PurePromAcceptStepSpec (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) : Prop :=
  ProtocolSetupWF r →
  ExternContractsHoldCli interp →
  S = compSemOf interp r →
  ∀ (who : List Participant) (ok : Nat → Bool)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes) (opkUsed : Bool)
    (acc_hw mid : List MachineEvent) (rec_ b rec' pt : HwBytes)
    (pf : PreKeyFields) (sess sess' : Session HwBytes)
    (coins : BitVec 256) (expected : Option HwBytes),
    who[(callStarts acc_hw).length]? = some r.bob →
    records r.bob = some rec_ →
    rec_.length < 2 ^ 32 - 2 ^ 20 →
    EligibleForSessionPromotion rec_ b →
    HonestIdentity interp r b →
    (∀ q, parsePreKeyWire b = some q → PqFromHonest sent q.message) →
    (∃ g₀ ms₀, Clean interp r S who ok g₀ ms₀ acc_hw) →
    PureCRel interp r S who ok records sent accepted acc_hw →
    COpkRelC interp r S who ok opkUsed acc_hw →
    PromPureAcceptOut interp r rec_ b rec' mid pt pf sess sess' coins expected →
    ((∃ g ms, MatchedPrefix interp r S who g ms (acc_hw ++ promAccBlk b mid pt)) ∨
      CollisionAt interp r S who ok (acc_hw ++ promAccBlk b mid pt)) ∧
    (¬ CollisionAt interp r S who ok (acc_hw ++ promAccBlk b mid pt) →
      ok (callStarts acc_hw).length = true →
      (∃ g ms, Clean interp r S who ok g ms (acc_hw ++ promAccBlk b mid pt)) ∧
      PureCRel interp r S who ok (fun q => if q = r.bob then some rec' else records q)
        sent accepted (acc_hw ++ promAccBlk b mid pt) ∧
      COpkRelC interp r S who ok opkUsed (acc_hw ++ promAccBlk b mid pt))

theorem purePromAcceptStepSpec_proved (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) :
    PurePromAcceptStepSpec interp r S := by
  intro hwf hext hSeq who ok records sent accepted opkUsed acc_hw mid rec_ b rec' pt
    pf sess sess' coins expected hwho hrec hlen hpm hhon hpqh hclean hrel hopk hout
  by_cases hcol : CollisionAt interp r S who ok (acc_hw ++ promAccBlk b mid pt)
  · exact ⟨Or.inr hcol, fun hncol => False.elim (hncol hcol)⟩
  · have hS : SemReady interp r S := hSeq ▸ compSemOf_ready interp r hwf
    let e' : PromTurn := ⟨records, sent, accepted, opkUsed⟩
    have hR : CReadyPure interp r S who ok e'.records e'.sent e'.accepted e'.opkUsed acc_hw :=
      ⟨hclean, hrel, hopk⟩
    have hentry : PromEntryHyps interp r S who ok (callStarts acc_hw).length e' acc_hw rec_ b :=
      prom_entry_hyps_pure hwf hR hwho hrec hlen hpm hhon hpqh
    let sm : StateAndMessage := { state := rec', message := List.replicate 47 0#8 ++ pt }
    have hbinOut : PromBinAcceptOut interp r rec_ b mid sm pf sess sess' coins expected pt :=
      { hpf := hout.hpf
        hcan_in := hout.hcan_in
        hcoins := hout.hcoins
        hdecOk := hout.hdecOk
        hexec := hout.hexec
        halice := hout.halice
        hpend := hout.hpend
        hkyb := hout.hkyb
        hstate := hout.hstate
        hmsg := rfl
        hwrc := hout.hwrc
        hcanon_out := hout.hcanon_out }
    have hcall : PromAcceptCall interp r S who ok (callStarts acc_hw).length e' mid acc_hw
        rec_ b sm pf sess sess' coins expected pt :=
      { entry := hentry
        hj := rfl
        out := hbinOut
        ver := hout.hver
        nodraw := hout.hnodraw }
    obtain ⟨hmp, hcont⟩ :=
      slot_rpk_prom_accept_pure interp hext r hwf S hS hSeq hcall hcol
    exact ⟨Or.inl hmp, fun _ hok => hcont hok⟩

end Symbolic.Swarm.CREF.Cli
