/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
public import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPure
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureA
import Symbolic.Proofs.Swarm.CREF.Initiate.ModelPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs -- shake: keep
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# `init` Coin-Cut Determinism and Failed-Move State Invariance

Proves that an anchored `Move.aliceStart` logging `AliceDone` under 32-byte `.single` `.rng`
length faithfulness pins `blk_hw` to the canonical 34-slice cut `initiateDrawsOfCoins coins`,
and that non-accepting moves on `init` cuts and failed `Move.aliceStart` steps preserve
`storedStates`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.S2

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open CryptoVerification.SignalSession (filesOf)

private theorem coinSplit_init_inv {blob coins : HwBytes} {blk_hw : List MachineEvent}
    (hcs : CoinSplit [.recv blob, .rng coins] blk_hw) :
    ∃ pieces : List HwBytes,
      (∀ p ∈ pieces, p ≠ []) ∧
      pieces.flatten <+: coins ∧
      blk_hw = .recv blob :: pieces.map MachineEvent.rng := by
  cases hcs with
  | keep _ hcs1 =>
    cases hcs1 with
    | keep hne _ => exact False.elim (hne coins rfl)
    | split hne hpre hcs2 =>
      cases hcs2
      exact ⟨_, hne, hpre, by simp⟩

private theorem pieces_eq_of_map_length_and_flatten :
    ∀ {xs ys : List HwBytes},
      xs.map List.length = ys.map List.length →
      xs.flatten = ys.flatten →
      xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => nomatch hlen
  | _ :: _, [], hlen, _ => nomatch hlen
  | x :: xs, y :: ys, hlen, hflat => by
    obtain ⟨hx, hxs⟩ := List.cons.inj hlen
    obtain ⟨rfl, hflat'⟩ := List.append_inj hflat hx
    exact congrArg (x :: ·) (pieces_eq_of_map_length_and_flatten hxs hflat')

private theorem aliceStart_next_eq_iniAliceStartTr_of_aliceDone {tr : ExecTrace}
    {a b : Participant} {idIdx regIdx : Nat}
    {h : _root_.DY.Libsignal.PQXDH.BundleHandles} {shown : Nat}
    (hdone : (eventIdx isAliceDone tr ((Move.aliceStart a b idIdx regIdx h shown).next tr)).isSome =
      true) :
    ∃ o, (Move.aliceStart a b idIdx regIdx h shown).next tr =
      Symbolic.Swarm.CREF.iniAliceStartTr tr a b o := by
  let Inv : ExecTrace → Prop := fun t =>
    t = tr ∨ t = tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32) ∨
      ∃ o, t = Symbolic.Swarm.CREF.iniAliceStartTr tr a b o
  have hInv : Inv ((Move.aliceStart a b idIdx regIdx h shown).next tr) := by
    change Inv (((aliceStart a b idIdx regIdx h >>= fun _ => Pure.pure ()).run tr).2.val)
    simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd]
    apply Symbolic.Swarm.COMPOSED.CompTrace.bind_aliceHandshake_at a b idIdx regIdx h tr
      (Or.inl rfl) (Or.inr (Or.inl rfl))
    intro ikA ikB _ spk _ pqpk _ opk _ _ _ _ _ _ _ _ _ _ _ _
    refine Or.inr (Or.inr ⟨Symbolic.Swarm.COMPOSED.CompTrace.aliceOut tr ikA ikB spk pqpk opk, ?_⟩)
    simp only [Symbolic.DYBridge.DY.Traceful.run_eq_1,
      Symbolic.DYBridge.DY.Random.genRand_eq_1,
      Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
      _root_.DY.Libsignal.TripleRatchet.traceLength,
      Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1,
      Symbolic.DYBridge.DY.Traceful.mk_eq_1,
      Symbolic.Swarm.CREF.iniAliceStartTr,
      Symbolic.Swarm.CREF.iniAliceStartState]
    dsimp only [Bind.bind, Pure.pure]
    simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.add_assoc]
    rfl
  rcases hInv with h0 | h1 | ho
  · rw [h0] at hdone
    simp [eventIdx, newIndices] at hdone
  · rw [h1] at hdone
    have hat :
        (((tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)).at? tr.length :
          Option (_root_.DY.ProtocolEvent.ExecEntryT _root_.DY.Libsignal.PQXDH.PQXDHEvent))) =
          none := by
      simp only [_root_.DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2]
      split
      · rfl
      · rfl
    have hlen1 : (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.RndE 32)).length = tr.length + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
    unfold eventIdx newIndices at hdone
    rw [hlen1, Nat.add_sub_cancel_left] at hdone
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat] at hdone
  · exact ho

private theorem aliceStart_vis_eq_of_aliceDone {tr : ExecTrace} {a b : Participant}
    {idIdx regIdx : Nat} {h : _root_.DY.Libsignal.PQXDH.BundleHandles} {shown : Nat}
    (hanc : (Move.aliceStart a b idIdx regIdx h shown).LogsSessionCompletion tr)
    (hdone : (eventIdx isAliceDone tr ((Move.aliceStart a b idIdx regIdx h shown).next tr)).isSome =
      true) :
    (Move.aliceStart a b idIdx regIdx h shown).vis tr =
      (⟨.recv, received tr ([h.spk, h.spkSig, h.pqpk, h.pqpkSig] ++ h.opk.toList), .bundle,
          none⟩ : VisEntry) ::
        (rngEntry (randTerm tr.length 32) :: kyberCoinEntries (randTerm (tr.length + 1) 32) ++
          [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by
  obtain ⟨o, htr'⟩ := aliceStart_next_eq_iniAliceStartTr_of_aliceDone hdone
  have hexp : exposures tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) = [] := by
    rw [htr']; exact Symbolic.Swarm.CREF.exposures_iniAliceStartTr tr a b o
  have hev : eventIdx isAliceDone tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) =
      some (tr.length + 5) := by
    rw [htr']; exact Symbolic.Swarm.CREF.eventIdx_isAliceDone_iniAliceStartTr tr a b o
  obtain ⟨v_anc, hv_anc, hva⟩ := hanc.2 (tr.length + 5) hev
  have hv_take : v_anc ∈
      (aliceVis tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) h).take shown := by
    dsimp only [Move.vis] at hv_anc
    rw [hexp, List.append_nil] at hv_anc
    exact hv_anc
  have hlen35 : 35 ≤
      ((aliceVis tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) h).take shown).length :=
    Symbolic.Swarm.CREF.XplSteps.xpl_aliceVis_take_anchor hv_take (by rw [hva]; simp)
  have hshown : 35 ≤ shown := by rw [List.length_take] at hlen35; omega
  have hvis_len :=
    Symbolic.Swarm.CREF.CliPure.IniPure.ini_aliceVis_length_le_35 tr
      ((Move.aliceStart a b idIdx regIdx h shown).next tr) h
  dsimp only [Move.vis]
  rw [hexp, List.append_nil,
    List.take_of_length_le (Nat.le_trans hvis_len hshown)]
  unfold aliceVis
  rw [htr', Symbolic.Swarm.CREF.newRandoms_iniAliceStartTr,
    Symbolic.Swarm.CREF.eventIdx_isAliceDone_iniAliceStartTr]
  rfl

private theorem forall2_map_snoc_inv {α β γ : Type} {R : β → γ → Prop} {f : α → β} :
    ∀ {xs : List α} {ys : List γ} {y : γ},
      List.Forall₂ R (xs.map f) (ys ++ [y]) →
      ∃ xs' x, xs = xs' ++ [x] ∧ List.Forall₂ R (xs'.map f) ys ∧ R (f x) y
  | [], _ :: _, _, h => nomatch h
  | [], [], _, h => nomatch h
  | [x], [], _, .cons hr .nil => ⟨[], x, rfl, .nil, hr⟩
  | _ :: _ :: _, [], _, .cons _ h => nomatch h
  | x :: xs, _ :: ys, _, .cons hr hrest => by
    obtain ⟨xs', x_last, rfl, h1, h2⟩ := forall2_map_snoc_inv hrest
    exact ⟨x :: xs', x_last, rfl, .cons hr h1, h2⟩

private theorem map_length_of_forall2_kyberCoin {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ent : _root_.DY.Bytes} :
    ∀ {ps : List HwBytes} {ks : List Nat},
      List.Forall₂ (EventMatchesEntry interp r S g)
        (ps.map MachineEvent.rng)
        (ks.map fun j => ⟨.rng, [ent], .kyberCoin j, none⟩) →
      ps.map List.length = List.replicate ks.length 4
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hm hrest =>
    congrArg₂ List.cons hm.2.1 (map_length_of_forall2_kyberCoin hrest)

/-- Under `AliceDone` and 32-byte `.single` `.rng` length faithfulness, an anchored
`Move.aliceStart` forces `blk_hw` to equal `.recv blob :: (initiateDrawsOfCoins coins).map .rng`. -/
theorem init_cut_eq_of_aliceDone {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {a b : Participant} {idIdx regIdx : Nat}
    {h : _root_.DY.Libsignal.PQXDH.BundleHandles} {shown : Nat} {blob coins : HwBytes}
    {blk_hw : List MachineEvent}
    (hcoins : coins.length = 192)
    (hrng : ∀ (v : VisEntry) (t : _root_.DY.Bytes),
      v ∈ (Move.aliceStart a b idIdx regIdx h shown).vis tr →
      v.kind = .rng → v.layout = .single → v.terms = [t] → (gamma interp S g t).length = 32)
    (hanc : (Move.aliceStart a b idIdx regIdx h shown).LogsSessionCompletion tr)
    (hdone : (eventIdx isAliceDone tr ((Move.aliceStart a b idIdx regIdx h shown).next tr)).isSome =
      true)
    (hcs : CoinSplit [.recv blob, .rng coins] blk_hw)
    (hmatch : List.Forall₂ (EventMatchesEntry interp r S g) blk_hw
      ((Move.aliceStart a b idIdx regIdx h shown).vis tr)) :
    blk_hw = .recv blob ::
      (Symbolic.Swarm.CREF.Cli.Slots.initiateDrawsOfCoins coins).map MachineEvent.rng := by
  obtain ⟨pieces, _, hpre, rfl⟩ := coinSplit_init_inv hcs
  have hvis_eq := aliceStart_vis_eq_of_aliceDone hanc hdone
  have hlen0 : (gamma interp S g (randTerm tr.length 32)).length = 32 :=
    hrng (rngEntry (randTerm tr.length 32)) (randTerm tr.length 32)
      (by rw [hvis_eq]; simp) rfl rfl rfl
  have hlen33 : (gamma interp S g (randTerm (tr.length + 2) 32)).length = 32 :=
    hrng { rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }
      (randTerm (tr.length + 2) 32) (by rw [hvis_eq]; simp) rfl rfl rfl
  rw [hvis_eq] at hmatch
  cases hmatch with
  | cons _ hmatch_rng =>
    rw [List.cons_append] at hmatch_rng
    rcases pieces with _ | ⟨p0, ps⟩
    · cases hmatch_rng
    · cases hmatch_rng with
      | cons hm0 hm_rest =>
        obtain ⟨ps_mid, p33, rfl, hm_kc, hm33⟩ := forall2_map_snoc_inv hm_rest
        have hp0_len : p0.length = 32 := by
          have hb := hm0.2
          dsimp only [rngEntry, List.map, eventBytes] at hb
          simp only [List.cons.injEq, and_true] at hb
          rw [← hb, hlen0]
        have hp33_len : p33.length = 32 := by
          have hb := hm33.2
          dsimp only [rngEntry, List.map, eventBytes] at hb
          simp only [List.cons.injEq, and_true] at hb
          rw [← hb, hlen33]
        have hmid_len : ps_mid.map List.length = List.replicate 32 4 := by
          unfold kyberCoinEntries at hm_kc
          simpa using map_length_of_forall2_kyberCoin hm_kc
        have hmap_len : (p0 :: (ps_mid ++ [p33])).map List.length =
            Symbolic.Swarm.CREF.initiateFullDrawLengths := by
          simp [hp0_len, hmid_len, hp33_len, Symbolic.Swarm.CREF.initiateFullDrawLengths]
        have htgt_len := Symbolic.Swarm.CREF.CliPure.initiateDrawsOfCoins_lengths hcoins
        have hlen_eq : (p0 :: (ps_mid ++ [p33])).map List.length =
            (Symbolic.Swarm.CREF.Cli.Slots.initiateDrawsOfCoins coins).map List.length :=
          hmap_len.trans htgt_len.symm
        have hflat_len : (p0 :: (ps_mid ++ [p33])).flatten.length = coins.length := by
          rw [List.length_flatten, hlen_eq, ← List.length_flatten,
            Symbolic.Swarm.CREF.CliPure.initiateDrawsOfCoins_flatten hcoins]
        obtain ⟨rest, hrest⟩ := hpre
        have hrest_nil : rest = [] := by
          apply List.eq_nil_of_length_eq_zero
          have hl := congrArg List.length hrest
          rw [List.length_append, hflat_len] at hl
          omega
        subst hrest_nil
        rw [List.append_nil] at hrest
        have hflat_eq : (p0 :: (ps_mid ++ [p33])).flatten =
            (Symbolic.Swarm.CREF.Cli.Slots.initiateDrawsOfCoins coins).flatten :=
          hrest.trans (Symbolic.Swarm.CREF.CliPure.initiateDrawsOfCoins_flatten hcoins).symm
        rw [pieces_eq_of_map_length_and_flatten hlen_eq hflat_eq]

end Symbolic.Swarm.Coinsplit.S2
