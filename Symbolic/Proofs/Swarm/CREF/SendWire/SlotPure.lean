/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPureC
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatement
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyFrame
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.SendWire.SlotPureB
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPure
import Symbolic.Proofs.Swarm.CREF.Stage1Wire
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach

/-!
# Pending-PreKey `SendWire` Return Step and `CoinSplit` Closure

Proves `sndP_ret_pure_step` over `PureCRel` and `COpkRelC`, together with `CoinSplit` step lemmas
for failed and returning `send_wire` calls.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.SndPure

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement.Cli (CoinSplit ExternContractsHoldCli)
open Symbolic.Swarm.CREF.SendWire
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalProtoCodec
open Proofs.libsignal.SR
open Symbolic.Swarm.COMPOSED

/-- Returning pending-prekey `send_wire` step over `PureCRel` and `COpkRelC`. -/
theorem sndP_ret_pure_step (interpretation : ExternInterpretation)
    (hext : ExternContractsHoldCli interpretation) (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (S : OpaqueSymbolSemantics) (hSeq : S = compSemOf interpretation r)
    (who : List Participant) (ok : Nat → Bool)
    (records : Participant → Option HwBytes) (sent accepted : List HwBytes) (opkUsed : Bool)
    (acc mid : List MachineEvent)
    (p : Participant) (rec pt coins_cli retState retMessage : HwBytes)
    (hclean₀ : ∃ g₀ ms₀, Clean interpretation r S who ok g₀ ms₀ acc)
    (hrel : PureCRel interpretation r S who ok records sent accepted acc)
    (hopk : COpkRelC interpretation r S who ok opkUsed acc)
    (hwho : who[(callStarts acc).length]? = some p)
    (hrec : records p = some rec)
    (hpend_rec : PureRecPending rec)
    (hreclen : rec.length < 2 ^ 32 - 2 ^ 20)
    (hsent_lt : sent.length < 2 ^ 32 - 1)
    (hout : (p = r.alice → SndPendingRetOut interpretation r rec pt coins_cli mid retState retMessage)) :
    let blk := (MachineEvent.pt pt :: mid) ++ [MachineEvent.send retMessage]
    let records' := fun q => if q = p then some retState else records q
    let sent' := sent ++ (sentBody retMessage).toList
    (callStarts blk).length = 1 ∧
    (∃ coins : HwBytes, ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      coins <+: coins_cli) ∧
    (∃ g ms, MatchedPrefix interpretation r S who g ms (acc ++ blk)) ∧
    (ok (callStarts acc).length = true →
      (∃ g ms, Clean interpretation r S who ok g ms (acc ++ blk)) ∧
      PureCRel interpretation r S who ok records' sent' accepted (acc ++ blk) ∧
      COpkRelC interpretation r S who ok opkUsed (acc ++ blk)) := by
  intro blk records' sent'
  obtain ⟨g₀, ms₀, hc₀⟩ := hclean₀
  have hmp₀ := hc₀.matched
  obtain ⟨⟨hrecs₀, hbook₀, _, _⟩, _⟩ := hrel.clean g₀ ms₀ hc₀
  obtain ⟨hp_alice, hpend₀⟩ := recPending_imp_alice_pending_of_recRel interpretation r S p rec
    g₀ ms₀ hreclen hpend_rec (hrecs₀ p rec hrec).2.2
  subst hp_alice
  have hout' := hout rfl
  obtain ⟨hcanon, hwc, sess, coins, hrc_sw, hmid, hpref, hev, stateIdx₀, ekIdx₀, ctIdx₀, _, hm_ext⟩ :=
    snd_ret_eval_and_matchedPrefix interpretation hext r hwf S hSeq who
      records sent accepted rec pt coins_cli retState retMessage acc mid
      g₀ ms₀ hmp₀ hwho hpend₀ hbook₀ hrel.oooAll hrec hreclen hsent_lt hout'
  have hcs_blk : (callStarts blk).length = 1 := by
    dsimp only [blk]; rw [snd_callStarts_ret pt retMessage ⟨coins, hmid⟩]; rfl
  refine ⟨hcs_blk, ⟨coins, hmid, hpref⟩, ⟨_, _, hm_ext⟩, fun hok_j => ?_⟩
  have hc_sg := clean_sendPendingGhost pt coins hc₀
  have hcc_ms₀ : callCount (runVis r ms₀) = (callStarts acc).length :=
    Stage1Wire.callCount_of_forall₂_eventMatchesEntry hmp₀.2.2.2.2.2
  have hok_ext : OutcomeFaithful r ok
      (ms₀ ++ [Move.encrypt r.alice stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) (some (ekIdx₀, ctIdx₀))]) :=
    Stage1Wire.outcomeFaithful_snoc hc₀.1.2 (fun _ h => by cases h)
      (fun _ => by rw [hcc_ms₀]; exact hok_j)
  have hc_ext : Clean interpretation r S who ok
      (sendPendingGhost g₀ (runTraceMoves r ms₀).length pt coins)
      (ms₀ ++ [Move.encrypt r.alice stateIdx₀ coins.length ((runTraceMoves r ms₀).length + 2) (some (ekIdx₀, ctIdx₀))])
      (acc ++ blk) := by
    refine ⟨⟨hm_ext, hok_ext⟩,
      not_readCollision_append_noAccept hc_sg.not_readCollision
        (fun e he q heq => snd_ret_noAccept pt retMessage mid ⟨coins, hmid⟩ e he (by subst heq; rfl)) ?_⟩
    intro m' hm' pre e
    simp only [List.mem_singleton] at hm'
    subst hm'
    exact snd_not_readColMove_encrypt pre e
  have hbkn' : PureBobKyberNone r records' := by
    intro rr hrr
    dsimp only [records'] at hrr
    simp only [hwf.1.symm, ↓reduceIte] at hrr
    exact hrel.bkn rr hrr
  have hbks_rec : ∀ rr', records' r.bob = some (recordBytes rr') →
      ∃ rr, records r.bob = some (recordBytes rr) ∧
        rr'.current.aliceBaseKey = rr.current.aliceBaseKey := by
    refine bks_rec_of_eq ?_
    dsimp only [records']
    simp only [hwf.1.symm, ↓reduceIte]
  exact ⟨⟨_, _, hc_ext⟩,
    sndW_ret_pureCRel hrel hwho hout'.msg_lt ⟨coins, hmid⟩
      (sndP_ret_cOooAll hrel.oooAll hcanon hrc_sw hwc hev)
      (snd_bka_ret_alice hwf retState hrel.bka) hbkn' hbks_rec
      (fun g ms_pre δ hB hdf hrel_pre =>
        sndP_ret_pureCRelAt_of_faithful interpretation hext r S hSeq
          hrec hpend_rec hreclen hout' hcanon hwc hmid hdf hB hrel_pre),
    cOpkRelC_of_no_accept hopk (fun h => h)
      (snd_ret_blockHead pt retMessage mid) (fun _ _ h => matchedPrefix_prefix_reachable h)
      (snd_ret_noAccept pt retMessage mid ⟨coins, hmid⟩)⟩

theorem coinSplit_append_snd {τ₁ τhw₁ τ₂ τhw₂ : List MachineEvent}
    (h1 : CoinSplit τ₁ τhw₁) (h2 : CoinSplit τ₂ τhw₂) :
    CoinSplit (τ₁ ++ τ₂) (τhw₁ ++ τhw₂) := by
  induction h1 with
  | nil => simpa using h2
  | keep hne _ ih => exact .keep hne ih
  | split hne hpre _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .split hne hpre ih

theorem coinSplit_send_fail_step (pt coins_cli : HwBytes) {mid : List MachineEvent}
    (hout : SndWhisperFailOut coins_cli mid) :
    CoinSplit [.pt pt, .rng coins_cli] (.pt pt :: mid) := by
  refine .keep (fun _ h => by cases h) ?_
  rcases hout with rfl | ⟨coins, hlen, hpre, rfl⟩
  · simpa using (CoinSplit.split (pieces := []) (by simp) List.nil_prefix CoinSplit.nil)
  · have hne : coins ≠ [] := by intro hc; subst hc; exact hlen rfl
    have hpre' : [coins].flatten <+: coins_cli := by simpa using hpre
    simpa using (CoinSplit.split (pieces := [coins]) (by simp [hne]) hpre' CoinSplit.nil)

theorem coinSplit_send_ret_step (pt coins_cli retMessage : HwBytes) {mid : List MachineEvent}
    (hmid : ∃ coins : HwBytes, ((coins = [] ∧ mid = []) ∨ (coins ≠ [] ∧ mid = [.rng coins])) ∧
      coins <+: coins_cli) :
    CoinSplit [.pt pt, .rng coins_cli, .send retMessage]
      ((.pt pt :: mid) ++ [.send retMessage]) := by
  rw [List.cons_append]
  refine .keep (fun _ h => by cases h) ?_
  have htail : CoinSplit [.send retMessage] [.send retMessage] :=
    .keep (fun _ h => by cases h) .nil
  obtain ⟨coins, ⟨_, rfl⟩ | ⟨hne, rfl⟩, hpre⟩ := hmid
  · simpa using (CoinSplit.split (pieces := []) (by simp) List.nil_prefix htail)
  · have hpre' : [coins].flatten <+: coins_cli := by simpa using hpre
    simpa using (CoinSplit.split (pieces := [coins]) (by simp [hne]) hpre' htail)

end Symbolic.Swarm.CREF.CliPure.SndPure

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed.Refinement.Cli (CoinSplit ExternContractsHoldCli)
open Symbolic.Swarm.CREF.SendWire
open Symbolic.Swarm.COMPOSED
export SndPure (PureRecPending SndWhisperFailOut SndWhisperRetOut
   SndPendingRetOut coinSplit_send_fail_step coinSplit_send_ret_step)

end Symbolic.Swarm.CREF.CliPure
