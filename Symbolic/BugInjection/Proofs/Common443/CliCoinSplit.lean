/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire

/-!
# CLI Coin-Split Helpers and Handshake Prefix Inversion

Splits the 192-byte `init` randomness into individual `MachineEvent.rng` draws via
`initiateDrawsOfCoins`, proves `CoinSplit` uniqueness for `init`, and lifts two-call (`init` +
`send`) prefix decomposition to split CLI traces.
-/

@[expose] public section

set_option autoImplicit false
cref_hide_foreign_instances

namespace Symbolic.BugInjection.Proofs.Common443.CliCoinSplit

open ByteSpecs
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open TripleRatchet (TREvent TRState)
open PQXDH (PQXDHEvent BundleHandles)
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh

/-- Splits 192 bytes of `init` randomness into a 32-byte draw, thirty-two 4-byte Kyber coin draws,
and a trailing 32-byte draw. -/
def initiateDrawsOfCoins (coins : HwBytes) : List HwBytes :=
  [coins.take 32] ++
    (List.range 32).map (fun j => (coins.drop (32 + 4 * j)).take 4) ++
    [(coins.drop 160).take 32]

theorem initiateDrawsOfCoins_lengths {coins : HwBytes} (h : coins.length = 192) :
    (initiateDrawsOfCoins coins).map List.length =
      [32] ++ List.replicate 32 4 ++ [32] := by
  unfold initiateDrawsOfCoins
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
  have h0 : (coins.take 32).length = 32 := by rw [List.length_take, h]; rfl
  have h33 : ((coins.drop 160).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, h]; rfl
  have hmid : List.map (List.length ∘ fun j => (coins.drop (32 + 4 * j)).take 4) (List.range 32) =
      List.replicate 32 4 := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_map, List.length_range] at hi1
      simp only [List.getElem_map, List.getElem_range, Function.comp_apply,
        List.length_take, List.length_drop, h, List.getElem_replicate]
      omega
  rw [h0, h33, hmid]

private theorem drop_take_append_drop (xs : HwBytes) (a b : Nat) :
    (xs.drop a).take b ++ xs.drop (a + b) = xs.drop a := by
  rw [← List.drop_drop, List.take_append_drop]

private theorem range_chunks_append :
    ∀ (k : Nat) (xs : HwBytes),
      ((List.range k).map (fun j => (xs.drop (32 + 4 * j)).take 4)).flatten ++
        xs.drop (32 + 4 * k) = xs.drop 32
  | 0, xs => by simp
  | k + 1, xs => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.append_assoc]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    have hstep : (xs.drop (32 + 4 * k)).take 4 ++ xs.drop (32 + 4 * (k + 1)) =
        xs.drop (32 + 4 * k) := by
      have heq : 32 + 4 * (k + 1) = (32 + 4 * k) + 4 := by omega
      rw [heq]
      exact drop_take_append_drop xs (32 + 4 * k) 4
    rw [hstep]
    exact range_chunks_append k xs

theorem initiateDrawsOfCoins_flatten {coins : HwBytes} (h : coins.length = 192) :
    (initiateDrawsOfCoins coins).flatten = coins := by
  unfold initiateDrawsOfCoins
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.singleton_append, List.append_assoc]
  have h33 : (coins.drop 160).take 32 = coins.drop 160 :=
    List.take_of_length_le (by rw [List.length_drop, h])
  rw [h33]
  have hmid :
      ((List.range 32).map (fun j => (coins.drop (32 + 4 * j)).take 4)).flatten ++
        coins.drop 160 = coins.drop 32 := range_chunks_append 32 coins
  rw [hmid, List.take_append_drop]

theorem coinSplit_init_ok (bun : HwBytes) {coins : HwBytes} (h : coins.length = 192) :
    CoinSplit [.recv bun, .rng coins]
      (.recv bun :: (initiateDrawsOfCoins coins).map MachineEvent.rng) := by
  refine CoinSplit.keep (fun b hb => by cases hb) ?_
  have h1 : (initiateDrawsOfCoins coins).map MachineEvent.rng =
      (initiateDrawsOfCoins coins).map MachineEvent.rng ++ [] := by simp
  rw [h1]
  refine CoinSplit.split ?_ ⟨[], ?_⟩ CoinSplit.nil
  · intro p hp
    have hlen_mem : p.length ∈ (initiateDrawsOfCoins coins).map List.length :=
      List.mem_map_of_mem hp
    rw [initiateDrawsOfCoins_lengths h] at hlen_mem
    intro hp_nil
    subst hp_nil
    simp at hlen_mem
  · rw [initiateDrawsOfCoins_flatten h, List.append_nil]

theorem coinSplit_append_inv :
    ∀ {σ₁ σ₂ τ : List MachineEvent},
      CoinSplit (σ₁ ++ σ₂) τ →
      ∃ τ₁ τ₂, τ = τ₁ ++ τ₂ ∧ CoinSplit σ₁ τ₁ ∧ CoinSplit σ₂ τ₂
  | [], _, τ, h => ⟨[], τ, rfl, .nil, h⟩
  | e :: σ₁, σ₂, _, h => by
    cases h with
    | keep hne hrest =>
      obtain ⟨τ₁, τ₂, rfl, h1, h2⟩ := coinSplit_append_inv hrest
      exact ⟨e :: τ₁, τ₂, rfl, .keep hne h1, h2⟩
    | @split coins pieces _ _ hne hpre hrest =>
      obtain ⟨τ₁, τ₂, rfl, h1, h2⟩ := coinSplit_append_inv hrest
      exact ⟨pieces.map MachineEvent.rng ++ τ₁, τ₂, (List.append_assoc _ _ _).symm,
        .split hne hpre h1, h2⟩

theorem coinSplit_init_inv {blob coins : HwBytes} {blk : List MachineEvent}
    (h : CoinSplit [.recv blob, .rng coins] blk) :
    ∃ pieces : List HwBytes,
      (∀ p ∈ pieces, p ≠ []) ∧ pieces.flatten <+: coins ∧
      blk = .recv blob :: pieces.map MachineEvent.rng := by
  cases h with
  | keep _ h1 =>
    cases h1 with
    | keep hne _ => exact absurd rfl (hne coins)
    | @split _ pieces _ _ hne hpre h2 =>
      cases h2
      simpa using ⟨pieces, hne, hpre, rfl⟩

theorem coinSplit_send_exit0_inv {stdin coins out : HwBytes} {blk : List MachineEvent}
    (h : CoinSplit [.pt stdin, .rng coins, .send out] blk) :
    ∃ pieces : List HwBytes,
      (∀ p ∈ pieces, p ≠ []) ∧
      pieces.flatten <+: coins ∧
      blk = .pt stdin :: (pieces.map MachineEvent.rng ++ [.send out]) := by
  cases h with
  | keep _ h1 =>
    cases h1 with
    | keep hne _ => exact absurd rfl (hne coins)
    | @split _ pieces _ _ hne hpre h2 =>
      cases h2 with
      | keep _ h3 =>
        cases h3
        exact ⟨pieces, hne, hpre, rfl⟩

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

private theorem map_length_of_forall2_kyberCoin {interp : ExternInterpretation} {r : Records}
    {S : Sem} {g : Ghost} {ent : DY.Bytes} :
    ∀ {ps : List HwBytes} {ks : List Nat},
      List.Forall₂ (EventMatchesEntry interp r S g)
        (ps.map MachineEvent.rng)
        (ks.map fun j => ⟨.rng, [ent], .kyberCoin j, none⟩) →
      ps.map List.length = List.replicate ks.length 4
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hm hrest =>
    congrArg₂ List.cons hm.2.1 (map_length_of_forall2_kyberCoin hrest)

private theorem aliceStart_vis_eq_of_aliceDone {tr : ExecTrace} {a b : Participant}
    {idIdx regIdx : Nat} {h : BundleHandles} {shown : Nat}
    (hanc : (Move.aliceStart a b idIdx regIdx h shown).Anchored tr)
    (hdone : (eventIdx isAliceDone tr ((Move.aliceStart a b idIdx regIdx h shown).next tr)).isSome =
      true) :
    (Move.aliceStart a b idIdx regIdx h shown).vis tr =
      (⟨.recv, received tr ([h.spk, h.spkSig, h.pqpk, h.pqpkSig] ++ h.opk.toList), .bundle,
          none⟩ : VisEntry) ::
        rngEntry (randTerm tr.length 32) ::
          (kyberCoinEntries (randTerm (tr.length + 1) 32) ++
            [{ rngEntry (randTerm (tr.length + 2) 32) with anchor := some (tr.length + 5) }]) := by
  obtain ⟨ikA, ikB, _, spk, _, pqpk, _, opk, _, _, _, _, _, _, _, _, _, _, _, _, htr'⟩ :=
    aliceStart_inv_of_isAliceDone hdone
  let o := iniAliceOut tr ikA ikB spk pqpk opk
  have hexp : exposures tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) = [] :=
    exposures_nil_of_not_leakKind rfl (fun hc => nomatch hc)
  have hev : eventIdx isAliceDone tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) =
      some (tr.length + 5) := by
    rw [htr']; exact eventIdx_isAliceDone_iniAliceStartTr tr a b o
  obtain ⟨v_anc, hv_anc, hva⟩ := hanc.2 (tr.length + 5) hev
  have hv_take : v_anc ∈
      (aliceVis tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) h).take shown := by
    rw [xpl_vis_eq, hexp, List.append_nil] at hv_anc
    exact hv_anc
  have hlen35 : 35 ≤
      ((aliceVis tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) h).take shown).length :=
    XplSteps.xpl_aliceVis_take_anchor hv_take (by rw [hva]; simp)
  have hshown : 35 ≤ shown := by rw [List.length_take] at hlen35; omega
  have hvis_eq := aliceVis_iniAliceStartTr tr a b o h
  have hvis_len := aliceVis_length_le tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) h
  rw [xpl_vis_eq, hexp, List.append_nil]
  change (aliceVis tr ((Move.aliceStart a b idIdx regIdx h shown).next tr) h).take shown = _
  rw [List.take_of_length_le (Nat.le_trans hvis_len hshown), htr', hvis_eq]

theorem init_cut_eq_of_aliceDone {interp : ExternInterpretation} {r : Records} {S : Sem}
    {g : Ghost} {tr : ExecTrace} {a b : Participant} {idIdx regIdx : Nat}
    {h : BundleHandles} {shown : Nat} {blob coins : HwBytes}
    {blk_hw : List MachineEvent}
    (hcoins : coins.length = 192)
    (hrng : ∀ (v : VisEntry) (t : DY.Bytes),
      v ∈ (Move.aliceStart a b idIdx regIdx h shown).vis tr →
      v.kind = .rng → v.layout = .single → v.terms = [t] → (gamma interp S g t).length = 32)
    (hanc : (Move.aliceStart a b idIdx regIdx h shown).Anchored tr)
    (hdone : (eventIdx isAliceDone tr ((Move.aliceStart a b idIdx regIdx h shown).next tr)).isSome =
      true)
    (hcs : CoinSplit [.recv blob, .rng coins] blk_hw)
    (hmatch : List.Forall₂ (EventMatchesEntry interp r S g) blk_hw
      ((Move.aliceStart a b idIdx regIdx h shown).vis tr)) :
    blk_hw = .recv blob :: (initiateDrawsOfCoins coins).map MachineEvent.rng := by
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
            [32] ++ List.replicate 32 4 ++ [32] := by
          simp [hp0_len, hmid_len, hp33_len]
        have htgt_len := initiateDrawsOfCoins_lengths hcoins
        have hlen_eq : (p0 :: (ps_mid ++ [p33])).map List.length =
            (initiateDrawsOfCoins coins).map List.length :=
          hmap_len.trans htgt_len.symm
        have hflat_len : (p0 :: (ps_mid ++ [p33])).flatten.length = coins.length := by
          rw [List.length_flatten, hlen_eq, ← List.length_flatten,
            initiateDrawsOfCoins_flatten hcoins]
        obtain ⟨rest, hrest⟩ := hpre
        have hrest_nil : rest = [] := by
          apply List.eq_nil_of_length_eq_zero
          have hl := congrArg List.length hrest
          rw [List.length_append, hflat_len] at hl
          omega
        subst hrest_nil
        rw [List.append_nil] at hrest
        have hflat_eq : (p0 :: (ps_mid ++ [p33])).flatten =
            (initiateDrawsOfCoins coins).flatten :=
          hrest.trans (initiateDrawsOfCoins_flatten hcoins).symm
        rw [pieces_eq_of_map_length_and_flatten hlen_eq hflat_eq]

private theorem eventIdx_isAliceDone_none_of_noSessionEffect {tr : ExecTrace} {m : Move}
    (heff : NoSessionEffect tr m) :
    eventIdx isAliceDone tr (m.next tr) = none := by
  unfold eventIdx
  apply List.find?_eq_none.mpr
  intro j hj
  rw [Bool.not_eq_true]
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  cases hat : ((m.next tr).at? j : Option PQXDHEntry) with
  | none => rfl
  | some e =>
    dsimp only [Option.map, Option.getD]
    exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.nonSessionPQAt_pred_eq_false
      (heff j hj).2.1 hat ⟨rfl, rfl⟩

private theorem runMoves_vis_nil_of_invisible :
    ∀ (δ : List Move) (tr : ExecTrace),
      MovesFrom InvisibleNoEffect tr δ → (runMoves δ tr).2 = []
  | [], _, _ => rfl
  | m :: δ, tr, ⟨⟨hvis, _⟩, hrest⟩ => by
    rw [runMoves_cons_snd, hvis, List.nil_append]
    exact runMoves_vis_nil_of_invisible δ (m.next tr) hrest

theorem init_exit0_cut_eq_of_prefix {interp : ExternInterpretation} {r : Records} {S : Sem}
    {ok : Nat → Bool} {blob coins : HwBytes}
    {τ₀ : List MachineEvent} {g : Ghost} {ms ms₁ ms₂ : List Move}
    (hok : ok 0 = true) (hcoins : coins.length = 192)
    (hcs : CoinSplit [.recv blob, .rng coins] τ₀)
    (hmp₁ : Symbolic.Swarm.CREF.MatchedPrefix interp r S g ms₁ τ₀)
    (hms : ms = ms₁ ++ ms₂)
    (hof : OutcomeFaithfulCli r ok ms)
    (hrng : RngLengthsFaithfulCli interp r S g ms) :
    τ₀ = .recv blob :: (initiateDrawsOfCoins coins).map MachineEvent.rng := by
  obtain ⟨pieces, _, _, hτ₀⟩ := coinSplit_init_inv hcs
  have h0 : runVis r [] = [] := by
    rcases hv : runVis r [] with _ | ⟨x, rest⟩
    · rfl
    · exfalso
      have hx : (runVis r ms₁)[0]? = some x := by
        have hs := runVis_append r [] ms₁
        rw [List.nil_append, hv, List.cons_append] at hs
        simp [hs]
      obtain ⟨e, he, hk, -⟩ := b5_forall₂_getElem? hmp₁.2.2 hx
      have h0' : runVis r [] = r.setupMove.vis Trace.nil := List.append_nil _
      have hxl : x.kind = .leak :=
        b5_setup_vis_leak r Trace.nil x (by rw [← h0', hv]; exact List.mem_cons_self)
      rw [hτ₀] at he; simp at he; subst he; simp [eventKind, hxl] at hk
  have hB : XplBlock6 interp r S g [] ms₁ [] τ₀ := by
    refine ⟨⟨hmp₁.1, modelRun_prefix_of_reachable (δ := ms₁) hmp₁.2.1
      (matchedPrefix6_prefix_reachable hmp₁ [] ms₁ rfl), h0 ▸ List.Forall₂.nil⟩,
      by simpa using hmp₁.2.1, ?_⟩
    have hsplit := runVis_append r [] ms₁
    rw [List.nil_append, h0, List.nil_append] at hsplit
    rw [← hsplit]
    exact hmp₁.2.2
  have hhead : ∀ e ∈ τ₀.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; rw [hτ₀] at he; simp at he; subst he; exact Or.inl rfl
  have hne : τ₀ ≠ [] := by rw [hτ₀]; simp
  have htail : ∀ e ∈ τ₀.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; rw [hτ₀] at he; simp at he
    obtain ⟨p, _, rfl⟩ := he
    dsimp [eventKind]
    decide
  obtain ⟨pre, m₀, post, hms₁_eq, hpre, ⟨hs₀, ha₀, hm₀⟩, _⟩ :=
    xpl6_oneMove hB hhead hne htail
  let tr₁ := (runMoves pre (setupTrace r)).1
  have htr₁_eq : (runMoves pre (runTraceMoves r [])).1 = tr₁ := rfl
  rw [htr₁_eq] at ha₀ hm₀
  have hpre_vis : runVis r pre = [] := by
    have h1 : runVis r pre = runVis r [] ++ (runMoves pre (setupTrace r)).2 :=
      runVis_append r [] pre
    have h2 : (runMoves pre (setupTrace r)).2 = [] :=
      runMoves_vis_nil_of_invisible pre (setupTrace r) hpre
    rw [h1, h0, h2, List.append_nil]
  have hms_full : ms = pre ++ m₀ :: (post ++ ms₂) := by
    simp [hms, hms₁_eq, List.append_assoc]
  have hm₀_get : ms[pre.length]? = some m₀ := by rw [hms_full]; simp
  have htake_pre : ms.take pre.length = pre := by rw [hms_full]; simp
  have htr_take : runTraceMoves r (ms.take pre.length) = tr₁ := by
    rw [htake_pre, xpl_runTrace_eq]
  rw [hτ₀] at hm₀
  obtain ⟨v₀, hv₀, hvk₀, _⟩ := xpl_head_entry hm₀ (e := .recv blob) rfl
  have hrk : RecvHeadKind m₀ := xpl_recvHeadKind m₀ tr₁ hv₀ hvk₀
  have hm₀_all_kinds : ∀ w ∈ m₀.vis tr₁, w.kind = .recv ∨ w.kind = .rng := by
    intro w hw
    obtain ⟨e, he, hew⟩ := xpl_forall₂_mem_right hm₀ w hw
    have hek := xpl_kind_of_matches hew
    rcases List.mem_cons.mp he with rfl | he'
    · exact Or.inl hek
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp he'
      exact Or.inr hek
  have hm₀_no_send_accept :
      (m₀.vis tr₁).any (fun v => v.kind == .send || v.kind == .accept) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rcases hm₀_all_kinds v hv with h | h <;> simp [h]
  have hm₀_has_recv :
      (m₀.vis tr₁).any (fun v => v.kind == .recv || v.kind == .pt) = true := by
    apply List.any_eq_true.mpr
    exact ⟨v₀, hv₀, by simp [hvk₀, eventKind]⟩
  have hcc0 : callCount (runVis r (ms.take pre.length)) = 0 := by
    rw [htake_pre, hpre_vis]; rfl
  have hdone_or := hof.2 pre.length m₀ hm₀_get
    (by simpa [htr_take] using hm₀_has_recv)
    (by rw [hcc0]; exact hok)
  have hdone : (eventIdx isAliceDone tr₁ (m₀.next tr₁)).isSome = true := by
    rcases hdone_or with h1 | h2
    · rw [htr_take, hm₀_no_send_accept] at h1; cases h1
    · rwa [htr_take] at h2
  have hneff : ¬ NoSessionEffect tr₁ m₀ := by
    intro heff
    rw [eventIdx_isAliceDone_none_of_noSessionEffect heff] at hdone
    cases hdone
  have hnoacc : ∀ w ∈ m₀.vis tr₁, w.kind ≠ .accept := by
    intro w hw hwk
    rcases hm₀_all_kinds w hw with h | h <;> rw [h] at hwk <;> cases hwk
  have hm₀_aliceStart :
      ∃ a b idS regB hb shown, m₀ = .aliceStart a b idS regB hb shown := by
    cases m₀ with
    | aliceStart a b idS regB hb shown => exact ⟨a, b, idS, regB, hb, shown, rfl⟩
    | bobStart b a kh rIdx mh pq sp shown =>
      exact absurd (noSessionEffect_of_no_accept (m := .bobStart b a kh rIdx mh pq sp shown)
        trivial ha₀ hnoacc) hneff
    | decrypt me si mi pq sp w =>
      exact absurd (noSessionEffect_of_no_accept (m := .decrypt me si mi pq sp w)
        trivial ha₀ hnoacc) hneff
    | decryptSkipped me si mi k pq sp w =>
      exact absurd (noSessionEffect_of_no_accept (m := .decryptSkipped me si mi k pq sp w)
        trivial ha₀ hnoacc) hneff
    | reject draws =>
      exact absurd (noSessionEffect_of_no_accept (m := .reject draws)
        trivial ha₀ hnoacc) hneff
    | setup => cases hs₀
    | encrypt | encryptAbort | encryptFail | compromiseIK | compromiseSPK | compromisePQSPK
    | compromiseOPK | exposeKey | exposeSpqr | exposeSkipped | attackerSend | brkDH | brkKEM =>
      exact False.elim hrk
  obtain ⟨a, b, idS, regB, hb, shown, rfl⟩ := hm₀_aliceStart
  have hrng_m₀ : ∀ (v : VisEntry) (t : DY.Bytes),
      v ∈ (Move.aliceStart a b idS regB hb shown).vis tr₁ →
      v.kind = .rng → v.layout = .single → v.terms = [t] → (gamma interp S g t).length = 32 := by
    intro v t hv hvk hvl hvt
    have hrecv_any : ((Move.aliceStart a b idS regB hb shown).vis tr₁).any
        (fun v => v.kind == .recv) = true := by
      apply List.any_eq_true.mpr
      exact ⟨v₀, hv₀, by simp [hvk₀, eventKind]⟩
    exact hrng pre.length (.aliceStart a b idS regB hb shown) hm₀_get
      (by simpa [htr_take] using hrecv_any)
      v t (by simpa [htr_take] using hv) hvk hvl hvt
  rw [hτ₀]
  exact init_cut_eq_of_aliceDone hcoins hrng_m₀ ha₀ hdone (by rw [← hτ₀]; exact hcs) hm₀

theorem init_exit0_cut_eq {interp : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool} {blob coins : HwBytes}
    {τ₁ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hok : ok 0 = true) (hcoins : coins.length = 192)
    (hexp : ExplainsCli interp r S who ok [.recv blob, .rng coins] τ₁ g ms) :
    τ₁ = .recv blob :: (initiateDrawsOfCoins coins).map MachineEvent.rng ∧
    ExplainsMoves interp r S who ok g ms τ₁ :=
  ⟨init_exit0_cut_eq_of_prefix hok hcoins hexp.1 (MatchedPrefix.of_composed hexp.2.1)
    (List.append_nil ms).symm hexp.2.2.1 hexp.2.2.2, ⟨hexp.2.1, hexp.2.2.1.1⟩⟩

theorem explainsCli_init_send_decomp {interp : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool}
    {blob coins pt cB w : HwBytes} {τ₁ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hok : ok 0 = true) (hcoins : coins.length = 192)
    (hexp : ExplainsCli interp r S who ok [.recv blob, .rng coins, .pt pt, .rng cB, .send w] τ₁ g ms) :
    ∃ blk₁,
      τ₁ = (.recv blob :: (initiateDrawsOfCoins coins).map MachineEvent.rng) ++ blk₁ ∧
      CoinSplit [.pt pt, .rng cB, .send w] blk₁ ∧
      ExplainsMoves interp r S who ok g ms τ₁ := by
  obtain ⟨hcs, hmp, hof, hrng⟩ := hexp
  obtain ⟨τ₀, blk₁, rfl, hcs₀, hcs₁⟩ :=
    coinSplit_append_inv (σ₁ := [.recv blob, .rng coins]) (σ₂ := [.pt pt, .rng cB, .send w]) hcs
  obtain ⟨pieces₂, _, _, hblk₁⟩ := coinSplit_send_exit0_inv hcs₁
  have hhead₂ : ∀ e ∈ blk₁.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; rw [hblk₁] at he; simp at he; subst he; exact Or.inr rfl
  have hmp6 := MatchedPrefix.of_composed hmp
  obtain ⟨ms₁, ms₂, hms_eq, hmp₁, _⟩ :=
    matchedPrefix6_split hmp6 hhead₂ (matchedPrefix6_prefix_reachable hmp6)
  have hτ₀ := init_exit0_cut_eq_of_prefix hok hcoins hcs₀ hmp₁ hms_eq hof hrng
  exact ⟨blk₁, congrArg (· ++ blk₁) hτ₀, hcs₁, ⟨hmp, hof.1⟩⟩

theorem encVis_of_coinSplit_send {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : TRState} {cl pq : Nat}
    {wr : Nat × Nat} {pt c w : HwBytes} {blk₂ : List MachineEvent}
    (hcs : CoinSplit [.pt pt, .rng c, .send w] blk₂)
    (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) blk₂
      (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some wr) true)) :
    EventMatchesEntry i r S g (.pt pt)
      ⟨.pt, [randTerm tr₂.length 32], .single, none⟩ ∧
    (∃ n ≤ c.length,
      (cl = 0 ↔ n = 0) ∧
      gamma i S g (randTerm (tr₂.length + 1) cl) = c.take n ∧
      (cl ≠ 0 → EventMatchesEntry i r S g (.rng (c.take n)) (rngEntry (randTerm (tr₂.length + 1) cl)))) ∧
    EventMatchesEntry i r S g (.send w)
      ⟨.send, received tr₂ [wr.1, wr.2] ++ [encOut tr₂ stA cl pq], .preKeySend, none⟩ := by
  obtain ⟨pieces, hne, hpre, rfl⟩ := coinSplit_send_exit0_inv hcs
  unfold encVis encSend at hm₁
  rw [newRandoms_encNextTr, lastSent_encNextTr] at hm₁
  by_cases hcl : cl = 0
  · subst hcl
    simp only [encDraws, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      List.filter_cons, List.filter_nil, List.map_nil, List.cons_append, List.nil_append] at hm₁
    rcases pieces with _ | ⟨p0, ps⟩
    · simp only [List.map_nil, List.nil_append] at hm₁
      rcases hm₁ with (_ | ⟨hpt, _ | ⟨hsnd, _⟩⟩)
      have hγ0 : gamma i S g (randTerm (tr₂.length + 1) 0) = [] := by
        unfold gamma gamma' randTerm
        rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)]
        simp [gRandom, concretizeRandom]
      refine ⟨hpt, ⟨0, Nat.zero_le _, ⟨fun _ => rfl, fun _ => rfl⟩, ?_, fun h => absurd rfl h⟩, hsnd⟩
      rw [hγ0]; simp
    · exfalso
      have hlen := xpl_forall₂_length hm₁
      simp at hlen
  · have hne_cl : (cl != 0) = true := bne_iff_ne.mpr hcl
    simp only [encDraws, List.filter_cons, hne_cl, ↓reduceIte, List.filter_nil,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hm₁
    rcases pieces with _ | ⟨p0, ps⟩
    · exfalso
      have hlen := xpl_forall₂_length hm₁
      simp at hlen
    · rcases ps with _ | ⟨p1, ps'⟩
      · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at hm₁
        rcases hm₁ with (_ | ⟨hpt, _ | ⟨hrng, _ | ⟨hsnd, _⟩⟩⟩)
        obtain ⟨rest, hcoins_eq⟩ := hpre
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hcoins_eq
        have hp0_ne : p0 ≠ [] := hne p0 (List.mem_cons_self ..)
        have hp0_pos : 0 < p0.length := List.length_pos_iff.mpr hp0_ne
        have hp0_le : p0.length ≤ c.length := by
          rw [← hcoins_eq, List.length_append]; omega
        have hp0_take : c.take p0.length = p0 := by
          rw [← hcoins_eq, List.take_left]
        have hγ : gamma i S g (randTerm (tr₂.length + 1) cl) = p0 := by
          have hb := hrng.2
          dsimp only [rngEntry, List.map, eventBytes] at hb
          simp only [List.cons.injEq, and_true] at hb
          exact hb
        exact ⟨hpt, ⟨p0.length, hp0_le, ⟨fun h => absurd h hcl, fun h0 => by omega⟩,
          hγ.trans hp0_take.symm, fun _ => by rw [hp0_take]; exact hrng⟩, hsnd⟩
      · exfalso
        have hlen := xpl_forall₂_length hm₁
        simp at hlen

theorem mem_inits_of_take {α : Type} :
    ∀ (xs : List α) {n : Nat}, n ≤ xs.length → xs.take n ∈ List.inits xs
  | [], 0, _ => by simp
  | _ :: _, 0, _ => by simp
  | x :: xs, n + 1, hn => by
    simp only [List.length_cons] at hn
    simp only [List.take_succ_cons, List.inits_cons, List.mem_cons, List.mem_map]
    exact Or.inr ⟨xs.take n, mem_inits_of_take xs (by omega), rfl⟩

theorem freshSafeTerm_draws_of_encVis_split {i : ExternInterpretation} {r : Records} {S : Sem}
    {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : TRState} {cl pq : Nat}
    {wr : Nat × Nat} {pt c w : HwBytes} {blk₂ : List MachineEvent}
    (hcs : CoinSplit [.pt pt, .rng c, .send w] blk₂)
    (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) blk₂
      (encVis tr₂ (encNextTr tr₂ me sIdx stA cl pq) (some wr) true))
    (hpt : pt.length ≠ 64)
    (hc : ∀ c' ∈ List.inits c, ∀ t ∈ ([11, 16, 17] : List Nat),
      c' ≠ fillFresh t 64) :
    Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct.FreshSafeTerm i S g
      (randTerm tr₂.length 32) ∧
    (g.σ tr₂.length 32).length ≠ 64 ∧
    Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct.FreshSafeTerm i S g
      (randTerm (tr₂.length + 1) cl) ∧
    (∀ t ∈ ([11, 16, 17] : List Nat),
      gamma i S g (randTerm (tr₂.length + 1) cl) ≠
        fillFresh t 64) ∧
    gamma i S g (randTerm (tr₂.length + 1) cl) ∈ List.inits c := by
  obtain ⟨hem_pt, ⟨n, hn, _, hγ, hem_rng⟩, _⟩ := encVis_of_coinSplit_send hcs hm₁
  have hpt_safe := freshSafeTerm_randTerm_of_single_pt_len hem_pt hpt
  have hmem : c.take n ∈ List.inits c := mem_inits_of_take c hn
  have hfst_cl : Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct.FreshSafeTerm i S g
      (randTerm (tr₂.length + 1) cl) := by
    by_cases hcl : cl = 0
    · subst hcl; exact freshSafeTerm_randTerm_zero i S g (tr₂.length + 1)
    · exact (freshSafeTerm_randTerm_of_single_rng (hem_rng hcl) (hc (c.take n) hmem)).1
  exact ⟨hpt_safe.1, (hpt_safe.2 (by decide)).2, hfst_cl,
    fun t ht => hγ ▸ hc (c.take n) hmem t ht, hγ ▸ hmem⟩

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
open Symbolic.BugInjection.Proofs.Common443.CompRX0Decomp
open Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Wire
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRX0Mem (sendMatches_append_inv)
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0

theorem invert_send_move_split {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {tr : ExecTrace} {m : Move} {w : HwBytes} {blk₂ : List MachineEvent}
    (hmem_send : MachineEvent.send w ∈ blk₂)
    (hm : List.Forall₂ (EventMatchesEntry i r S g) blk₂ (m.vis tr)) :
    ∃ me sIdx cl pq wrap,
      m = .encrypt me sIdx cl pq wrap ∧
      lastSent tr (m.next tr) ≠ none ∧
      (wrap = none → w.head? = some TripleRatchet.Refinement.wireWhisperTag) ∧
      List.Forall₂ (EventMatchesEntry i r S g) blk₂ (encVis tr (m.next tr) wrap true) := by
  obtain ⟨v_s, hv_s, hev_s⟩ := xpl_forall₂_mem_left hm (.send w) hmem_send
  have hvk_s : v_s.kind = .send := xpl_kind_of_matches hev_s
  obtain ⟨me, sIdx, cl, pq, wrap, rfl⟩ : ∃ me sIdx cl pq wrap, m = .encrypt me sIdx cl pq wrap := by
    rcases xpl_vis_kind m tr hv_s with h | ⟨_, h⟩ | ⟨_, h⟩
    · rw [hvk_s] at h; cases h
    · rcases h with h | h | ⟨_, h⟩
      · rw [hvk_s] at h; cases h
      · rw [hvk_s] at h; cases h
      · exact h
    · rw [hvk_s] at h; rcases h with h | h | h <;> cases h
  have hex : exposures tr ((Move.encrypt me sIdx cl pq wrap).next tr) = [] :=
    exposures_nil_of_not_leakKind rfl (fun h => nomatch h)
  have hvis : (Move.encrypt me sIdx cl pq wrap).vis tr =
      encVis tr ((Move.encrypt me sIdx cl pq wrap).next tr) wrap true := by
    rw [xpl_vis_eq, hex, List.append_nil]; rfl
  rw [hvis] at hm hv_s
  have hls : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) ≠ none ∧
      (wrap = none → w.head? = some TripleRatchet.Refinement.wireWhisperTag) := by
    unfold encVis at hv_s; simp only [↓reduceIte, List.mem_append] at hv_s
    rcases hv_s with hd | hsnd
    · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk_s] at hk; cases hk)
    · unfold encSend at hsnd
      rcases hls_eq : lastSent tr ((Move.encrypt me sIdx cl pq wrap).next tr) with _ | wt
      · rw [hls_eq] at hsnd; cases hsnd
      · refine ⟨by simp, fun hw_none => ?_⟩
        rw [hls_eq, hw_none, List.mem_singleton] at hsnd; subst hsnd
        obtain ⟨_, t, _, hw_eq⟩ := hev_s; change w = _ at hw_eq; rw [hw_eq]; rfl
  exact ⟨me, sIdx, cl, pq, wrap, rfl, hls.1, hls.2, hm⟩

theorem matchedPrefix_ini_send_struct_split {i : ExternInterpretation} {r : Records} {S : Sem}
    {g : Ghost} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} {pt c w : HwBytes}
    {blk₂ : List MachineEvent}
    (hcs : CoinSplit [.pt pt, .rng c, .send w] blk₂)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms ((.recv bun :: rs) ++ blk₂))
    (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng)
    (hw : w.head? ≠ some TripleRatchet.Refinement.wireWhisperTag) :
    ∃ pre a b idS regB hb shown mid me sIdx cl pq wr post,
      ms = pre ++ .aliceStart a b idS regB hb shown :: mid ++
          .encrypt me sIdx cl pq (some wr) :: post ∧
      let tr₁ := (runMoves pre (setupTrace r)).1
      let m₀ := Move.aliceStart a b idS regB hb shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let m₁ := Move.encrypt me sIdx cl pq (some wr)
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) post ∧
      35 ≤ shown ∧ (eventIdx isAliceDone tr₁ (m₀.next tr₁)).isSome = true ∧
      lastSent tr₂ (m₁.next tr₂) ≠ none ∧
      List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (m₀.next tr₁) hb) ∧
      List.Forall₂ (EventMatchesEntry i r S g) blk₂ (encVis tr₂ (m₁.next tr₂) (some wr) true) := by
  obtain ⟨pieces, _, _, hblk₂⟩ := coinSplit_send_exit0_inv hcs
  let blk₁ : List MachineEvent := .recv bun :: rs
  have hhead₂ : ∀ e ∈ blk₂.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp [hblk₂] at he; subst he; exact Or.inr rfl
  obtain ⟨ms₁, δ₂, hms, hmp₁, hfor₂⟩ :=
    matchedPrefix6_split hmp hhead₂ (matchedPrefix6_prefix_reachable hmp)
  have hB₂ : XplBlock6 i r S g ms₁ δ₂ blk₁ blk₂ := ⟨hmp₁, hms ▸ hmp.2.1, hfor₂⟩
  have hhead₁ : ∀ e ∈ blk₁.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp [blk₁] at he; subst he; exact Or.inl rfl
  have hmp₁' : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms₁ ([] ++ blk₁) := by simpa using hmp₁
  obtain ⟨ms₀, δ₁, hms₁, hmp₀, hfor₁⟩ :=
    matchedPrefix6_split hmp₁' hhead₁ (matchedPrefix6_prefix_reachable hmp₁')
  have hB₁ : XplBlock6 i r S g ms₀ δ₁ [] blk₁ := ⟨hmp₀, hms₁ ▸ hmp₁.2.1, hfor₁⟩
  have hne₁ : blk₁ ≠ [] := by simp [blk₁]
  have htail₁ : ∀ e ∈ blk₁.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; have hk := hrs_kind e he; rw [hk]; decide
  obtain ⟨pre₁, m₀, post₁, rfl, hpre₁, ⟨hs₀, ha₀, hm₀⟩, hpost₁⟩ :=
    xpl6_oneMove hB₁ hhead₁ hne₁ htail₁
  have hne₂ : blk₂ ≠ [] := by simp [hblk₂]
  have htail₂ : ∀ e ∈ blk₂.tail, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    simp only [hblk₂, List.tail_cons, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨p, _, rfl⟩ | rfl <;> { dsimp [eventKind]; decide }
  obtain ⟨pre₂, m₁, post₂, rfl, hpre₂, ⟨_, _, hm₁⟩, hpost₂⟩ :=
    xpl6_oneMove hB₂ hhead₂ hne₂ htail₂
  let pre := ms₀ ++ pre₁
  let mid := post₁ ++ pre₂
  let tr₁ := (runMoves pre (setupTrace r)).1
  have htr₁_eq : (runMoves pre₁ (runTraceMoves r ms₀)).1 = tr₁ := by
    dsimp [tr₁, pre]; rw [runMoves_append_fst, ← xpl_runTrace_eq]
  rw [htr₁_eq] at ha₀ hm₀ hpost₁
  have hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre := by
    rw [movesFrom_append, ← xpl_runTrace_eq]
    exact ⟨movesFrom_invisibleNoEffect_of_matchedPrefix_nil hmp₀, hpre₁⟩
  let tr₂ := (runMoves mid (m₀.next tr₁)).1
  have hms₁_eq : ms₁ = pre ++ m₀ :: post₁ := by simp [hms₁, pre, List.append_assoc]
  have hrun_ms₁ : runTraceMoves r ms₁ = (runMoves post₁ (m₀.next tr₁)).1 := by
    rw [hms₁_eq, xpl_runTrace_eq, runMoves_append_fst, runMoves_cons_fst]
  have htr₂_eq : (runMoves pre₂ (runTraceMoves r ms₁)).1 = tr₂ := by
    dsimp [tr₂, mid]; rw [runMoves_append_fst, ← hrun_ms₁]
  rw [htr₂_eq] at hm₁ hpost₂
  have hmid : MovesFrom InvisibleNoEffect (m₀.next tr₁) mid := by
    rw [movesFrom_append, ← hrun_ms₁]; exact ⟨hpost₁, hpre₂⟩
  have hmem_send : MachineEvent.send w ∈ blk₂ := by simp [hblk₂]
  obtain ⟨me, sIdx, cl, pq, wrap, rfl, hls, hwrap_none, hm₁_vis⟩ :=
    invert_send_move_split hmem_send hm₁
  have hneff : ¬ NoSessionEffect tr₁ m₀ := by
    intro heff
    have hno₁ : NoTRState tr₁ :=
      noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre
    have hno_m₀ : NoTRState (m₀.next tr₁) := noTRState_of_noSessionEffect hno₁ heff
    have hno₂ : NoTRState tr₂ := noTRState_of_movesFrom_invisibleNoEffect hno_m₀ hmid
    exact hls (encrypt_lastSent_none_of_noTRState hno₂ me sIdx cl pq wrap)
  obtain ⟨a, b, idS, regB, hb, shown, rfl, hshown, hdone, hm₀_vis⟩ :=
    invert_ini_move_of_not_noSessionEffect hs₀ ha₀ hm₀ hrs_len hrs_kind hneff
  cases wrap with
  | none => exact absurd (hwrap_none rfl) hw
  | some wr =>
    refine ⟨pre, a, b, idS, regB, hb, shown, mid, me, sIdx, cl, pq, wr, post₂, ?_, hpre, hmid,
      hpost₂, hshown, hdone, hls, hm₀_vis, hm₁_vis⟩
    simp [hms, hms₁, pre, mid, List.append_assoc]

private theorem movesAnchored_append_left :
    ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), MovesAnchored (ms₁ ++ ms₂) tr → MovesAnchored ms₁ tr
  | [], _, _, _ => trivial
  | m :: ms₁, ms₂, tr, ⟨hm, hrest⟩ => ⟨hm, movesAnchored_append_left ms₁ ms₂ (m.next tr) hrest⟩

theorem matchedPrefix_ini_send_bundle_legacy_split {i : ExternInterpretation} {r : Records}
    {S : Sem} {g : Ghost} {ms : List Move} {bun : HwBytes} {rs : List MachineEvent}
    {pt c w : HwBytes} {blk₂ : List MachineEvent}
    (hNe : r.alice ≠ r.bob) (hnb : CompSetupSecrecy.NoBrk r ms)
    (hcs : CoinSplit [.pt pt, .rng c, .send w] blk₂)
    (hmp : Symbolic.Swarm.CREF.MatchedPrefix i r S g ms ((.recv bun :: rs) ++ blk₂))
    (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng)
    (hbun4 : bun[4]? ≠ some 1#8)
    (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) :
    ∃ pre a idS hb shown mid me sIdx cl pq wr post ikA spkSig pqpkSig,
      ms = pre ++ .aliceStart a r.bob idS 6 hb shown :: mid ++
          .encrypt me sIdx cl pq (some wr) :: post ∧
      let tr₁ := (runMoves pre (setupTrace r)).1
      let o := aliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
      let m₀ := Move.aliceStart a r.bob idS 6 hb shown
      let tr₂ := (runMoves mid (m₀.next tr₁)).1
      let m₁ := Move.encrypt me sIdx cl pq (some wr)
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect (m₀.next tr₁) mid ∧
      MovesFrom InvisibleNoEffect (m₁.next tr₂) post ∧
      35 ≤ shown ∧ hb.opk = none ∧ bun[4]? = some 0#8 ∧
      ((idS = 4 ∧ a = r.alice ∧ ikA = setupSecret r 0) ∨
        (idS = 9 ∧ a = r.bob ∧ ikA = setupSecret r 1)) ∧
      NetMsgAt (setupPublic r 4) hb.spk tr₁ ∧ NetMsgAt spkSig hb.spkSig tr₁ ∧
      NetMsgAt (setupPublic r 6) hb.pqpk tr₁ ∧ NetMsgAt pqpkSig hb.pqpkSig tr₁ ∧
      BundleCore i S g bun (setupPublic r 4) spkSig (setupPublic r 6) pqpkSig ∧
      m₀.next tr₁ = aliceStartTrOfOut tr₁ a r.bob o ∧
      lastSent tr₂ (m₁.next tr₂) ≠ none ∧
      List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (m₀.next tr₁) hb) ∧
      List.Forall₂ (EventMatchesEntry i r S g) blk₂ (encVis tr₂ (m₁.next tr₂) (some wr) true) := by
  obtain ⟨pre, a, b, idS, regB, hb, shown, mid, me, sIdx, cl, pq, wr, post, hms, hpre, hmid,
    hpost, hshown, hdone, hls, hm₀_vis, hm₁_vis⟩ :=
    matchedPrefix_ini_send_struct_split hcs hmp hrs_len hrs_kind hw
  have hms_split : ms = pre ++ (.aliceStart a b idS regB hb shown :: mid ++
      .encrypt me sIdx cl pq (some wr) :: post) := by simp [hms, List.append_assoc]
  have hreach₁ : (runMoves pre (setupTrace r)).1.Reachable reachability := by
    rw [← xpl_runTrace_eq]; exact matchedPrefix6_prefix_reachable hmp pre _ hms_split
  have hnb_pre : CompSetupSecrecy.NoBrk r pre :=
    CompSetupSecrecy.noBrk_of_le (by rw [hms_split, xpl_runTrace_eq (ms := pre ++ _), runMoves_append_fst (ms₁ := pre), ← xpl_runTrace_eq]; exact Symbolic.Swarm.CREF.runMoves_le _ _) hnb
  have hs_pre : ∀ m ∈ pre, m.isSetup = false :=
    fun m hm => hmp.2.1.2.1 m (by rw [hms_split]; exact List.mem_append_left _ hm)
  have ha_pre : MovesAnchored pre (setupTrace r) := by
    have ha_all := hmp.2.1.2.2.1.2.1; rw [hms_split] at ha_all
    exact movesAnchored_append_left pre _ (setupTrace r) ha_all
  obtain ⟨rfl, rfl, hhb_opk, hbun0, ikA, spkSig, pqpkSig, hid, hspk, hspkSig, hpq, hpqSig, _, _,
    hcore, hnext⟩ := pia_bundle_inv hNe hnb_pre hs_pre ha_pre hpre hreach₁ hdone hm₀_vis hbun4
  exact ⟨pre, a, idS, hb, shown, mid, me, sIdx, cl, pq, wr, post, ikA, spkSig, pqpkSig, hms, hpre,
    hmid, hpost, hshown, hhb_opk, hbun0, hid, hspk, hspkSig, hpq, hpqSig, hcore, hnext, hls,
    hm₀_vis, hm₁_vis⟩

theorem sendMatches_of_encVis_split {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {tr tr' : ExecTrace} {e c' : Nat} {o : DY.Bytes} {pt c w : HwBytes} {blk₂ : List MachineEvent}
    (hcs : CoinSplit [.pt pt, .rng c, .send w] blk₂)
    (hls : lastSent tr tr' = some o)
    (hm : List.Forall₂ (EventMatchesEntry i r S g) blk₂ (encVis tr tr' (some (e, c')) true)) :
    CompRPreKeyWire.SendMatchesMoves i r S g w (received tr [e, c'] ++ [o]) := by
  obtain ⟨pieces, _, _, rfl⟩ := coinSplit_send_exit0_inv hcs
  have hmem : MachineEvent.send w ∈ (.pt pt :: (pieces.map MachineEvent.rng ++ [.send w])) := by
    simp
  obtain ⟨v, hv, hev⟩ := xpl_forall₂_mem_left hm (.send w) hmem
  have hvk : v.kind = .send := xpl_kind_of_matches hev
  unfold encVis at hv; simp only [↓reduceIte, List.mem_append] at hv
  rcases hv with hd | hsnd
  · rcases encDraws_kind _ hd with hk | hk <;> (rw [hvk] at hk; cases hk)
  · unfold encSend at hsnd; rw [hls, List.mem_singleton] at hsnd; subst hsnd; exact hev.2

theorem pia_x0_decomp_split {r : Records} {S : Sem} {who : List Participant} {g : Ghost}
    {ms : List Move} {bun : HwBytes} {rs : List MachineEvent} {pt c w : HwBytes}
    {blk₂ : List MachineEvent}
    (hNe : r.alice ≠ r.bob) (hnb : CompSetupSecrecy.NoBrk r ms)
    (hcs : CoinSplit [.pt pt, .rng c, .send w] blk₂)
    (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who g ms
      ((.recv bun :: rs) ++ blk₂))
    (hrs_len : rs.length = 34) (hrs_kind : ∀ e ∈ rs, eventKind e = .rng)
    (hbun4 : bun[4]? ≠ some 1#8)
    (hw : w.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) :
    ∃ (pre : List Move) (a : Participant) (idS : Nat) (hb : DY.Libsignal.PQXDH.BundleHandles)
      (shown : Nat) (mid : List Move) (cl e c' : Nat) (post : List Move) (ikA : DY.Bytes)
      (tr₁ tr₂ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
      (stA : DY.Libsignal.TripleRatchet.TRState),
      tr₁ = (runMoves pre (setupTrace r)).1 ∧
      o = aliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none ∧
      stA = aliceStartState tr₁ r.bob o ∧
      tr₂ = (runMoves mid ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁)).1 ∧
      ms = pre ++ .aliceStart a r.bob idS 6 hb shown :: mid ++
          .encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post ∧
      ((idS = 4 ∧ a = r.alice ∧ ikA = setupSecret r 0) ∨
        (idS = 9 ∧ a = r.bob ∧ ikA = setupSecret r 1)) ∧
      NetMsgAt o.ek (tr₁.length + 3) tr₂ ∧ NetMsgAt o.ct (tr₁.length + 4) tr₂ ∧
      o.ek.AttackerKnows (runTraceMoves r ms) ∧ o.ct.AttackerKnows (runTraceMoves r ms) ∧
      (encOut tr₂ stA cl (tr₂.length + 2)).AttackerKnows (runTraceMoves r ms) ∧
      bobDoneBaseKeys (runTraceMoves r ms) = [] ∧
      List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs)
        (aliceVis tr₁ ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) hb) ∧
      CompRPreKeyWire.SendMatchesMoves compI0 r S g w (received tr₂ [e, c'] ++ [encOut tr₂ stA cl (tr₂.length + 2)]) ∧
      (Move.aliceStart a r.bob idS 6 hb shown).next tr₁ = aliceStartTrOfOut tr₁ a r.bob o ∧
      MovesFrom InvisibleNoEffect (setupTrace r) pre ∧
      MovesFrom InvisibleNoEffect ((Move.aliceStart a r.bob idS 6 hb shown).next tr₁) mid ∧
      MovesFrom InvisibleNoEffect
        ((Move.encrypt a (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post := by
  have hmp' := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp
  obtain ⟨pre, a, idS, hb, shown, mid, me, sIdx, cl, pq, wr, post, ikA, spkSig, pqpkSig, hms,
    hrest⟩ :=
    matchedPrefix_ini_send_bundle_legacy_split hNe hnb hcs hmp' hrs_len hrs_kind hbun4 hw
  dsimp only at hrest
  obtain ⟨hpre, hmid, hpost, _hshown, _hopk, _hbun0, hdisj, _hspk, _hspkSig, _hpqpk, _hpqpkSig,
    _hcore, hm₀, hls, hvis₀, hvis₁⟩ := hrest
  rcases wr with ⟨e, c'⟩
  have hown : ownSaltsFrom (setupTrace r) ms = true := hmp'.2.1.2.2.2.2.1
  have hntr : NoTRState (runMoves pre (setupTrace r)).1 :=
    noTRState_of_movesFrom_invisibleNoEffect (noTRState_setupTrace r) hpre
  have hek₁ : NetMsgAt (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2)
      (setupPublic r 4) (setupPublic r 6) none).ek ((runMoves pre (setupTrace r)).1.length + 3)
      ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) := by
    rw [hm₀]; exact netMsgAt_ek_iniAliceStartTr _ _ _ _
  have hct₁ : NetMsgAt (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2)
      (setupPublic r 4) (setupPublic r 6) none).ct ((runMoves pre (setupTrace r)).1.length + 4)
      ((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1) := by
    rw [hm₀]; exact netMsgAt_ct_iniAliceStartTr _ _ _ _
  have hst₁ : ∀ j : Nat,
      (((Move.aliceStart a r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1).at? j :
        Option TRStEntry) =
      if j = (runMoves pre (setupTrace r)).1.length + 8 then
        some (TRStE a (aliceStartState (runMoves pre (setupTrace r)).1 r.bob
          (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2) (setupPublic r 4)
            (setupPublic r 6) none)))
      else none := by
    rw [hm₀]; exact at?_trSt_iniAliceStartTr_of_noTRState hntr _ _ _
  obtain ⟨_hE1, hme, hsIdx, hpq, _hns, _hnext, hlastSent, hek₂, hct₂, _hekr, _hctr, _hencr,
    hekK, hctK, hencK, hnil⟩ :=
    pia_enc_inv (stA := aliceStartState (runMoves pre (setupTrace r)).1 r.bob
      (aliceOut (runMoves pre (setupTrace r)).1 ikA (setupPublic r 2) (setupPublic r 4)
        (setupPublic r 6) none)) hms hpre hmid hpost hown hek₁ hct₁ hst₁ hls
  have hsm := sendMatches_of_encVis_split hcs hlastSent hvis₁
  subst hme hsIdx hpq
  exact ⟨pre, me, idS, hb, shown, mid, cl, e, c', post, ikA, (runMoves pre (setupTrace r)).1,
    (runMoves mid ((Move.aliceStart me r.bob idS 6 hb shown).next (runMoves pre (setupTrace r)).1)).1,
    _, _, rfl, rfl, rfl, rfl, hms, hdisj, hek₂, hct₂, hekK, hctK, hencK, hnil, hvis₀, hsm, hm₀,
    hpre, hmid, hpost⟩

end Symbolic.BugInjection.Proofs.Common443.CliCoinSplit
