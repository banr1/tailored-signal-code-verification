/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.Coinsplit.Lift.Defs
import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureA
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Xpl.PrefixReach

/-!
# Quiet-Failure Invariant Transfer Across Coin Splits

Proves `BridgeBQuietFailSpec`: whenever a call fails (`ok (callStarts τ_pre).length = false`),
`PureCRel` and `COpkRelC` transfer from `τ_pre` to `τ_pre ++ blk'` for every `CoinSplit` cut
`blk'` of `[e, .rng coins]` with `e` a `.recv` or `.pt` event.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.Lift.L04

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli (CoinSplit)
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.Coinsplit.Lift

private theorem coinSplit_two_eq_cons_map_rng {e : MachineEvent} {coins : HwBytes}
    {blk' : List MachineEvent}
    (he : eventKind e = .recv ∨ eventKind e = .pt)
    (hcs : CoinSplit [e, .rng coins] blk') :
    ∃ ds : List HwBytes, blk' = e :: ds.map MachineEvent.rng := by
  have hne : eventKind e ≠ .rng := by
    rcases he with h | h <;> simp [h]
  obtain ⟨τ', rfl, hcs'⟩ := S1.coinSplit_cons_nonRng_iff hne |>.mp hcs
  obtain ⟨ds, τ'', _, _, hτ', hnil⟩ := S1.coinSplit_cons_rng_iff.mp hcs'
  cases hnil
  rw [List.append_nil] at hτ'
  exact ⟨ds, congrArg (e :: ·) hτ'⟩

private theorem runVis_append_invisible {r : ProtocolSetup} {ms₀ pre : List Move}
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre) :
    runVis r (ms₀ ++ pre) = runVis r ms₀ := by
  rw [CREF.runVis_append, IniPure.ini_invisible_nil pre (runTraceMoves r ms₀) hpre, List.append_nil]

private theorem not_logsAliceDone_of_fail {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms₀ pre post : List Move} {m : Move} {τ_pre : List MachineEvent}
    (hpre_mp : MatchedPrefix interp r S who g ms₀ τ_pre)
    (hof : OutcomeFaithful r ok (ms₀ ++ (pre ++ m :: post)))
    (hpre : MovesFrom InvisibleNoEffect (runTraceMoves r ms₀) pre)
    (hok : ok (callStarts τ_pre).length = false) :
    ¬IniPure.LogsAliceDone (runMoves pre (runTraceMoves r ms₀)).1 m := by
  intro hdone
  have hof' : OutcomeFaithful r ok ((ms₀ ++ pre) ++ m :: post) := by
    simpa [List.append_assoc] using hof
  have hget : ((ms₀ ++ pre) ++ m :: post)[(ms₀ ++ pre).length]? = some m := by
    simp
  have hstep := (hof' (ms₀ ++ pre).length m hget).2
  rw [List.take_left] at hstep
  have htr : runTraceMoves r (ms₀ ++ pre) = (runMoves pre (runTraceMoves r ms₀)).1 :=
    TR.runTrace_append r ms₀ pre
  have hcc : callCount (runVis r (ms₀ ++ pre)) = (callStarts τ_pre).length := by
    rw [runVis_append_invisible hpre]
    exact CREF.callCount_eq_callStarts_length hpre_mp.2.2.2.2.2
  rw [htr, hcc] at hstep
  have htrue : ok (callStarts τ_pre).length = true := hstep hdone
  rw [hok] at htrue
  cases htrue

private theorem quiet_of_fail_block {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool} {g : Ghost}
    {ms₀ δ : List Move} {τ_pre : List MachineEvent} {e : MachineEvent} {ds : List HwBytes}
    (he : eventKind e = .recv ∨ eventKind e = .pt)
    (hB : XplBlock interp r S who g ms₀ δ τ_pre (e :: ds.map MachineEvent.rng))
    (hof : OutcomeFaithful r ok (ms₀ ++ δ))
    (hok : ok (callStarts τ_pre).length = false) :
    MovesFrom (fun tr m => NoSessionEffect tr m) (runTraceMoves r ms₀) δ := by
  let blk' : List MachineEvent := e :: ds.map MachineEvent.rng
  have hhead : ∀ x ∈ blk'.head?, eventKind x = .recv ∨ eventKind x = .pt := by
    intro x hx
    simp only [blk', List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    subst hx
    exact he
  have htail : ∀ x ∈ blk'.tail,
      eventKind x ≠ .recv ∧ eventKind x ≠ .pt ∧ eventKind x ≠ .leak := by
    intro x hx
    simp only [blk', List.tail_cons, List.mem_map] at hx
    obtain ⟨_, _, rfl⟩ := hx
    simp [eventKind]
  obtain ⟨pre, m, post, rfl, hpre, ⟨_hs, ha, hm⟩, hpost⟩ :=
    xpl_oneMove hB hhead (List.cons_ne_nil _ _) htail
  have hpre' := movesFrom_mono (fun _ _ h => h.2) _ _ hpre
  have hpost' := movesFrom_mono (fun _ _ h => h.2) _ _ hpost
  refine (movesFrom_append _ pre (m :: post) _).2 ⟨hpre', ?_, hpost'⟩
  obtain ⟨v, hv, hvk, _⟩ := xpl_head_entry hm (List.head?_cons ..)
  rcases he with he_recv | he_pt
  · have hrk : RecvHeadKind m := xpl_recvHeadKind m _ hv (hvk.trans he_recv)
    have hnoacc : ∀ w ∈ m.vis (runMoves pre (runTraceMoves r ms₀)).1, w.kind ≠ .accept := by
      intro w hw
      obtain ⟨x, hx, hxw⟩ := xpl_forall₂_mem_right hm w hw
      rw [xpl_kind_of_matches hxw]
      rcases List.mem_cons.mp hx with rfl | hx'
      · rw [he_recv]; decide
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx'
        simp [eventKind]
    have hnot_done : ¬IniPure.LogsAliceDone (runMoves pre (runTraceMoves r ms₀)).1 m :=
      not_logsAliceDone_of_fail hB.pre hof hpre hok
    cases m
    case aliceStart => exact IniPure.noSessionEffect_aliceStart_of_not_logsAliceDone hnot_done
    case bobStart => exact noSessionEffect_of_no_accept trivial ha hnoacc
    case decrypt => exact noSessionEffect_of_no_accept trivial ha hnoacc
    case decryptSkipped => exact noSessionEffect_of_no_accept trivial ha hnoacc
    case reject => exact noSessionEffect_of_no_accept trivial ha hnoacc
    all_goals exact False.elim hrk
  · have hsk : SendKind m := by
      have hvk_pt : v.kind = .pt := hvk.trans he_pt
      rcases xpl_vis_kind m _ hv with h | ⟨h, _⟩ | ⟨_, h⟩
      · rw [hvk_pt] at h; cases h
      · exact h
      · rw [hvk_pt] at h; rcases h with h | h | h <;> cases h
    refine SndPure.noSessionEffect_of_no_send hsk ha fun w hw hwk => ?_
    obtain ⟨x, hx, hxw⟩ := xpl_forall₂_mem_right hm w hw
    have hxk : eventKind x = .send := (xpl_kind_of_matches hxw).symm.trans hwk
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [he_pt] at hxk; cases hxk
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx'
      cases hxk

theorem bridgeB_quiet_fail : BridgeBQuietFailSpec := by
  intro interp r S who ok records sent accepted opkUsed τ_pre blk' e coins
    _hwf he hcs hok hrel hopk
  obtain ⟨ds, rfl⟩ := coinSplit_two_eq_cons_map_rng he hcs
  let blk : List MachineEvent := e :: ds.map MachineEvent.rng
  have hhead : ∀ x ∈ blk.head?, eventKind x = .recv ∨ eventKind x = .pt := by
    intro x hx
    simp only [blk, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
    subst hx
    exact he
  have hnosend : ∀ b, MachineEvent.send b ∉ blk := by
    intro b hb
    rcases List.mem_cons.mp hb with h | hb'
    · subst h
      rcases he with h | h <;> cases h
    · obtain ⟨_, _, h⟩ := List.mem_map.mp hb'
      cases h
  have hnoacc : ∀ x ∈ blk, eventKind x ≠ .accept := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases he with h | h <;> rw [h] <;> decide
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx'
      simp [eventKind]
  refine ⟨?_, cOpkRelC_of_no_accept' hopk id hhead hnoacc⟩
  refine
    { oooAll := hrel.oooAll
      sendsFit := TR.sendsFit_append hrel.sendsFit fun b hb => absurd hb (hnosend b)
      bka := hrel.bka
      bkn := hrel.bkn
      clean := fun g ms hc => ?_ }
  have hmp := hc.matched
  obtain ⟨ms₀, δ, rfl, hpre_mp, hmatch⟩ :=
    matchedPrefix_split hmp hhead (matchedPrefix_prefix_reachable hmp)
  have hc₀ : Clean interp r S who ok g ms₀ τ_pre :=
    clean_prefix hpre_mp.2.2.2.2.2.length_eq hc
  have hB : XplBlock interp r S who g ms₀ δ τ_pre blk := ⟨hpre_mp, hmp.2.1, hmatch⟩
  have hq : MovesFrom (fun tr m => NoSessionEffect tr m) (runTraceMoves r ms₀) δ :=
    quiet_of_fail_block he hB hc.1.2 hok
  have hsb_nil : TR.sentBodies blk = [] := by
    unfold TR.sentBodies
    refine List.filterMap_eq_nil_iff.mpr fun x hx => ?_
    cases x with
    | send b => exact absurd hx (hnosend b)
    | _ => rfl
  have hsent : TR.sentBodies (τ_pre ++ blk) = TR.sentBodies τ_pre := by
    rw [TR.sentBodies_append, hsb_nil, List.append_nil]
  obtain ⟨hat₀, hbks₀⟩ := hrel.clean g ms₀ hc₀
  exact ⟨pureCRelAt_quiet hB hq hsent hat₀, bks_quiet hq hbks₀⟩

end Symbolic.Swarm.Coinsplit.Lift.L04
