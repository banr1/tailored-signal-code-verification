/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.LeakRecordsCompat
public import Symbolic.Proofs.Refinement.Composed.Cli.OldShape
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBinPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptHypsPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRelPure
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRelPureB
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.ExplainOKPure

/-!
# Fresh Pre-Key `recv` Accept Assembly

Combines `RecvAcceptContractPure`, `RpkAcceptBin`, `AcceptD.AcceptTieD`,
`slot_rpk_hxpl`, and the post-accept `CReadyPure` relation lemmas to discharge
the `code = 0` accept branch of a fresh pre-key `recv` call.
-/

@[expose] public section

set_option autoImplicit false
cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

cref_open
open Symbolic.Swarm.CREF.CliPure
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.SignalSession (Address)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open DY.Libsignal.Composed.Refinement (ProtocolSetup ProtocolSetupWF PreKeyFields opkRemovedIdx)
open DY.Libsignal.Composed.Refinement.Cli (CliCall CliTurn CoinSplit
  ExternContractsHoldCli cliEntryEvents cliExitEvents)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli

/-- Reflexive `CoinSplit` on `[.recv c.stdin, .rng c.coins, .accept pt]` when `c.cmd = .recv peer`
and `c.coins ≠ []`. -/
theorem coinSplit_rpkNew_accept {c : CliCall} {peer : Address}
    (hcmd : c.cmd = .recv peer) (hc_ne : c.coins ≠ []) (pt : HwBytes) :
    CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 pt)
      [.recv c.stdin, .rng c.coins, .accept pt] := by
  have hentry : cliEntryEvents c = [.recv c.stdin, .rng c.coins] := by
    simp [cliEntryEvents, hcmd]
  have hexit : cliExitEvents c 0 pt = [.accept pt] := by
    simp [cliExitEvents, hcmd]
  rw [hentry, hexit]
  change CoinSplit [.recv c.stdin, .rng c.coins, .accept pt]
    (.recv c.stdin :: ([c.coins].map MachineEvent.rng ++ [.accept pt]))
  refine CoinSplit.keep (fun _ h => nomatch h)
    (CoinSplit.split ?_ (by simp) (CoinSplit.keep (fun _ h => nomatch h) CoinSplit.nil))
  intro p hp
  rw [List.mem_singleton] at hp
  exact hp ▸ hc_ne

/-- Preserves `CReadyPure` and extends `MatchedPrefix` across an accepting fresh pre-key `recv`. -/
theorem rpkNew_accept_cReady {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {t t' : CliTurn} {accepted : List HwBytes} {acc_hw : List MachineEvent}
    {b d ct_wire pt : HwBytes} {sm : StateAndMessage} {pf : PreKeyFields}
    (hext : ExternContractsHoldCli interp)
    (hwf : ProtocolSetupWF r)
    (hSeq : S = compSemOf interp r)
    (hwho : who[(callStarts acc_hw).length]? = some r.bob)
    (hready : CReadyPure interp r S who ok (t.leakRecords r) t.sent accepted (t.opkUsed r) acc_hw)
    (hhon : DY.Libsignal.Composed.Refinement.HonestIdentity interp r b)
    (hpqh : ∀ q, DY.Libsignal.Composed.Refinement.parsePreKeyWire b = some q →
      DY.Libsignal.Composed.Refinement.PqFromHonest t.sent q.message)
    (hfresh : ∀ q, DY.Libsignal.Composed.Refinement.parsePreKeyWire b = some q →
      q.baseKey.take 33 ∉ accepted)
    (hst_lt : sm.state.length < 2 ^ 64)
    (hcontract : RecvAcceptContractPure interp r (t.opkUsed r) b sm pf d ct_wire pt)
    (hBin : RpkAcceptBin pf sm)
    (hTie : AcceptD.AcceptTieD interp r pf d pt sm)
    (hsent' : t'.sent = t.sent)
    (hleak' : t'.leakRecords r =
      fun q => if q = r.bob then some sm.state else t.leakRecords r q)
    (hopk' : t'.opkUsed r = (t.opkUsed r || (sm.message[opkRemovedIdx]?).any (· != 0#8))) :
    ((∃ g ms, MatchedPrefix interp r S who g ms (acc_hw ++ [.recv b, .rng d, .accept pt])) ∨
      CollisionAt interp r S who ok (acc_hw ++ [.recv b, .rng d, .accept pt])) ∧
    (¬ CollisionAt interp r S who ok (acc_hw ++ [.recv b, .rng d, .accept pt]) →
      ok (callStarts acc_hw).length = true →
      CReadyPure interp r S who ok (t'.leakRecords r) t'.sent
        (accepted ++ [pf.baseKey.take 33]) (t'.opkUsed r)
        (acc_hw ++ [.recv b, .rng d, .accept pt])) := by
  have hS : SemReady interp r S := hSeq ▸ compSemOf_ready interp r hwf
  have hA : RpkAcceptHypsPure interp r S who ok (t.leakRecords r) t.sent accepted (t.opkUsed r)
      acc_hw b sm pf d ct_wire pt :=
    { ready := hready
      who_cs := hwho
      hon := hhon
      pqh := hpqh
      fresh := hfresh
      state_lt := hst_lt
      contract := hcontract }
  have hxpl := slot_rpk_hxpl interp hext r hwf S hS hSeq who ok
    (t.leakRecords r) t.sent accepted (t.opkUsed r) acc_hw b sm pf d ct_wire pt hA
  refine ⟨?_, fun hcol hok => ?_⟩
  · by_cases hcol : CollisionAt interp r S who ok (acc_hw ++ [.recv b, .rng d, .accept pt])
    · exact Or.inr hcol
    · exact Or.inl (hxpl hcol).1
  · have hclean' := (hxpl hcol).2 hok
    have hrel' := rpk_accept_cRel hext hwf hSeq hA hBin hTie hcol
    have hopk_rel' := rpk_accept_cOpk hA
    refine ⟨hclean', ?_, ?_⟩
    · rw [hleak', hsent']; exact hrel'
    · rw [hopk']; exact hopk_rel'

end Symbolic.Swarm.CREF.Cli.Slots
