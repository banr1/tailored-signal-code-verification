/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridgeBase
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplit

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.BugInjection
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose (coinSplit_nonRng_cons coinSplit_rng_cons)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull

local elab "chars_of_hex_cli" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "str_of_hex_cli" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private def cliCoins2Chars : List Char := chars_of_hex_cli cliCoins2
private theorem cliCoins2_eq_hex : cliCoins2 = hexBytes (str_of_hex_cli cliCoins2) := rfl
private theorem cliCoins2Str_eq : (str_of_hex_cli cliCoins2) = String.ofList cliCoins2Chars := rfl
theorem cliCoins2_eq_fast : cliCoins2 = PtPrefixInv78b.cliCoins2Fast := by
  change cliCoins2 = hexBytes.go SpecTop.hexDigit cliCoins2Chars
  rw [cliCoins2_eq_hex, cliCoins2Str_eq, SpecTop.hexBytes_ofList]
theorem cliCoins2_inits_sub : ∀ c ∈ cliCoins2.inits, c ∈ PtPrefixInv78b.cliCoins2Fast.inits := by
  rw [cliCoins2_eq_fast]; exact fun _ h => h
private def cliCoins0Chars : List Char := chars_of_hex_cli cliCoins0
private def cliCoins4Chars : List Char := chars_of_hex_cli cliCoins4
private theorem cliCoins0_eq_hex : cliCoins0 = hexBytes (str_of_hex_cli cliCoins0) := rfl
private theorem cliCoins4_eq_hex : cliCoins4 = hexBytes (str_of_hex_cli cliCoins4) := rfl
private theorem cliCoins0Str_eq : (str_of_hex_cli cliCoins0) = String.ofList cliCoins0Chars := rfl
private theorem cliCoins4Str_eq : (str_of_hex_cli cliCoins4) = String.ofList cliCoins4Chars := rfl
private def cliCoins0Fast : HwBytes := hexBytes.go SpecTop.hexDigit cliCoins0Chars
private def cliCoins4Fast : HwBytes := hexBytes.go SpecTop.hexDigit cliCoins4Chars
private theorem cliCoins0_eq_fast : cliCoins0 = cliCoins0Fast := by
  change cliCoins0 = hexBytes.go SpecTop.hexDigit cliCoins0Chars
  rw [cliCoins0_eq_hex, cliCoins0Str_eq, SpecTop.hexBytes_ofList]
private theorem cliCoins4_eq_fast : cliCoins4 = cliCoins4Fast := by
  change cliCoins4 = hexBytes.go SpecTop.hexDigit cliCoins4Chars
  rw [cliCoins4_eq_hex, cliCoins4Str_eq, SpecTop.hexBytes_ofList]
theorem cliCoins0_length : cliCoins0.length = 192 := by rw [cliCoins0_eq_fast]; rfl
theorem cliCoins4_length : cliCoins4.length = 192 := by rw [cliCoins4_eq_fast]; rfl
private def initiateCharChunks (cs : List Char) : List (List Char) :=
  [cs.take 64] ++ (List.range 32).map (fun j => (cs.drop (64 + 8 * j)).take 8) ++ [(cs.drop 320).take 64]
private theorem map_rng_hexBytes_ofList (css : List (List Char)) :
    css.map (fun cs => MachineEvent.rng (hexBytes (String.ofList cs))) =
    css.map (fun cs => MachineEvent.rng (hexBytes.go SpecTop.hexDigit cs)) := by
  induction css with
  | nil => rfl
  | cons cs css _ => simp only [List.map_cons, SpecTop.hexBytes_ofList]
private theorem call0Rng_eq_ofList :
    PtDead35.call0Rng = (initiateCharChunks cliCoins0Chars).map (fun cs => MachineEvent.rng (hexBytes (String.ofList cs))) := rfl
private theorem call4Rng_eq_ofList :
    PtDead78.call4Rng = (initiateCharChunks cliCoins4Chars).map (fun cs => MachineEvent.rng (hexBytes (String.ofList cs))) := rfl
theorem initiateDrawsOfCoins_cliCoins0_eq :
    (CliCoinSplit.initiateDrawsOfCoins cliCoins0).map MachineEvent.rng = PtDead35.call0Rng := by
  rw [cliCoins0_eq_fast, call0Rng_eq_ofList, map_rng_hexBytes_ofList]; rfl
theorem initiateDrawsOfCoins_cliCoins4_eq :
    (CliCoinSplit.initiateDrawsOfCoins cliCoins4).map MachineEvent.rng = PtDead78.call4Rng := by
  rw [cliCoins4_eq_fast, call4Rng_eq_ofList, map_rng_hexBytes_ofList]; rfl
theorem init_draws_cliCoins0_eq :
    .recv (wireAt 0) :: (CliCoinSplit.initiateDrawsOfCoins cliCoins0).map MachineEvent.rng =
    Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace.take 35 := by
  rw [initiateDrawsOfCoins_cliCoins0_eq]; rfl
theorem init_draws_cliCoins4_eq :
    .recv (wireAt 43) :: (CliCoinSplit.initiateDrawsOfCoins cliCoins4).map MachineEvent.rng =
    (Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1.trace.drop 43).take 35 := by
  rw [initiateDrawsOfCoins_cliCoins4_eq]; rfl
theorem cliTrace_length : cliTrace.length = 19 := rfl
theorem cliTrace_pt_fin :
    ∀ k : Fin cliTrace.length, SpecTop.isPtKindAt cliTrace k.1 = true → k.1 = 2 ∨ k.1 = 5 ∨ k.1 = 13 := by decide
theorem cliTrace_acceptedRecv_fin :
    ∀ k : Fin cliTrace.length, SpecTop.isAcceptedRecvKindAt cliTrace k.1 = true → k.1 = 8 ∨ k.1 = 16 := by decide
theorem cliTrace_pt_index {n : Nat} (hn : n < cliTrace.length) (h : SpecTop.isPtKindAt cliTrace n = true) :
    n = 2 ∨ n = 5 ∨ n = 13 := cliTrace_pt_fin ⟨n, hn⟩ h
theorem cliTrace_acceptedRecv_index {n : Nat} (hn : n < cliTrace.length) (h : SpecTop.isAcceptedRecvKindAt cliTrace n = true) :
    n = 8 ∨ n = 16 := cliTrace_acceptedRecv_fin ⟨n, hn⟩ h
theorem cliTrace_getElem?_2 : cliTrace[2]? = some (.pt (ptAt 35)) := rfl
theorem cliTrace_getElem?_5 : cliTrace[5]? = some (.pt (ptAt 38)) := rfl
theorem cliTrace_getElem?_8 : cliTrace[8]? = some (.recv (wireAt 40)) := rfl
theorem cliTrace_getElem?_13 : cliTrace[13]? = some (.pt (ptAt 78)) := rfl
theorem cliTrace_getElem?_16 : cliTrace[16]? = some (.recv (wireAt 81)) := rfl
abbrev PrefixGhostsCli := DY.Libsignal.Composed.Refinement.Cli.PrefixExplainingGhostsMoves
theorem mem_prefixGhostsCli_self {i : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool} {σ₁ τ₁ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hex : ExplainsCli i r S who ok σ₁ τ₁ g ms) : g ∈ PrefixGhostsCli i r S who g ms σ₁ :=
  ⟨rfl, τ₁, hex.1, hex.2.1⟩

private theorem forall2_rng_kind {interp : ExternInterpretation} {r : Records} {S : Sem}
    {g : Ghost} {pieces : List HwBytes} {vs : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interp r S g) (pieces.map MachineEvent.rng) vs) :
    ∀ v ∈ vs, v.kind = .rng := by
  induction pieces generalizing vs with
  | nil => cases h; intro _ hv; cases hv
  | cons p ps ih =>
    cases h with
    | cons hm hrest =>
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hmem
      · exact hm.1.symm
      · exact ih hrest v hmem

theorem outcomeFaithful_prefix_of_append {r : Records} {ok : Nat → Bool}
    {ms₁ ms₂ : List Move} (h : OutcomeFaithful r ok (ms₁ ++ ms₂)) :
    OutcomeFaithful r ok ms₁ := by
  intro i m hi
  have hlt : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  have htake : (ms₁ ++ ms₂).take i = ms₁.take i := List.take_append_of_le_length (Nat.le_of_lt hlt)
  simpa [htake] using h i m (by rwa [List.getElem?_append_left hlt])

theorem outcomeFaithfulCli_prefix_of_append {r : Records} {ok : Nat → Bool}
    {ms₁ ms₂ : List Move} (h : OutcomeFaithfulCli r ok (ms₁ ++ ms₂)) :
    OutcomeFaithfulCli r ok ms₁ := by
  refine ⟨outcomeFaithful_prefix_of_append h.1, fun i m hi => ?_⟩
  have hlt : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  have htake : (ms₁ ++ ms₂).take i = ms₁.take i := List.take_append_of_le_length (Nat.le_of_lt hlt)
  simpa [htake] using h.2 i m (by rwa [List.getElem?_append_left hlt])

theorem rngLengthsFaithfulCli_prefix_of_append {interp : ExternInterpretation}
    {r : Records} {S : Sem} {g : Ghost}
    {ms₁ ms₂ : List Move} (h : RngLengthsFaithfulCli interp r S g (ms₁ ++ ms₂)) :
    RngLengthsFaithfulCli interp r S g ms₁ := by
  intro i m hi
  have hlt : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  have htake : (ms₁ ++ ms₂).take i = ms₁.take i := List.take_append_of_le_length (Nat.le_of_lt hlt)
  simpa [htake] using h i m (by rwa [List.getElem?_append_left hlt])

open Symbolic.Swarm.CREF Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
private theorem runVis_append_local (r : Records) (ms₁ ms₂ : List Move) :
    runVis r (ms₁ ++ ms₂) = runVis r ms₁ ++ (runMoves ms₂ (runTraceMoves r ms₁)).2 := by
  unfold runVis runTraceMoves; rw [← List.cons_append, runMoves_append_snd]

private theorem callCount_eq_callStarts_length_local {interp : ExternInterpretation} {r : Records}
    {S : Sem} {g : Ghost} {τ : List MachineEvent} {vs : List VisEntry}
    (h : List.Forall₂ (EventMatchesEntry interp r S g) τ vs) :
    callCount vs = (callStarts τ).length := by
  induction h with
  | nil => rfl
  | @cons _ _ _ _ hm _ ih =>
    unfold callCount callStarts at ih ⊢
    simp only [List.filter_cons, hm.1]
    split <;> simp [ih]

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure in
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice in
theorem init_blk_cut_eq
    {interp : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool}
    {τ_pre blk : List MachineEvent} {blob coins : HwBytes}
    {g : Ghost} {ms_pre δ ms_post : List Move}
    (hcoins : coins.length = 192)
    (hcs_blk : CoinSplit [.recv blob, .rng coins] blk)
    (hB_blk : XplBlock interp r S who g ms_pre δ τ_pre blk)
    (_hmp_0 : DY.Libsignal.Composed.Refinement.MatchedPrefix interp r S who g (ms_pre ++ δ) (τ_pre ++ blk))
    (hof : OutcomeFaithfulCli r ok ((ms_pre ++ δ) ++ ms_post))
    (hrng : RngLengthsFaithfulCli interp r S g ((ms_pre ++ δ) ++ ms_post))
    (_hwho_pre : who[(callStarts τ_pre).length]? = some r.alice)
    (hok_pre : ok (callStarts τ_pre).length = true) :
    blk = .recv blob :: (CliCoinSplit.initiateDrawsOfCoins coins).map MachineEvent.rng := by
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs_blk
  obtain ⟨pieces, τ2, _, _, rfl, hcs2⟩ := coinSplit_rng_cons hcs1
  cases hcs2
  simp only [List.append_nil] at hcs_blk hB_blk ⊢
  have hB6 : XplBlock6 interp r S g ms_pre δ τ_pre (.recv blob :: pieces.map MachineEvent.rng) :=
    ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hB_blk.pre, hB_blk.run, hB_blk.matched⟩
  have hhead : ∀ e ∈ (MachineEvent.recv blob :: pieces.map MachineEvent.rng).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hne : (MachineEvent.recv blob :: pieces.map MachineEvent.rng) ≠ [] := List.cons_ne_nil _ _
  have htail : ∀ e ∈ (MachineEvent.recv blob :: pieces.map MachineEvent.rng).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    simp only [List.tail_cons, List.mem_map] at he
    obtain ⟨d, _, rfl⟩ := he; dsimp [eventKind]; decide
  obtain ⟨pre, m₀, post, rfl, hpre, ⟨hs₀, ha₀, hm₀⟩, _⟩ := xpl6_oneMove hB6 hhead hne htail
  let tr_m := runTraceMoves r (ms_pre ++ pre)
  have htr_eq : (runMoves pre (runTraceMoves r ms_pre)).1 = tr_m :=
    (CompPrefixInvStruct.runTrace_append r ms_pre pre).symm
  rw [htr_eq] at ha₀ hm₀
  have hms_full : (ms_pre ++ (pre ++ m₀ :: post)) ++ ms_post =
      (ms_pre ++ pre) ++ (m₀ :: (post ++ ms_post)) := by
    simp [List.append_assoc]
  let idx := (ms_pre ++ pre).length
  have hidx : ((ms_pre ++ (pre ++ m₀ :: post)) ++ ms_post)[idx]? = some m₀ := by
    rw [hms_full, List.getElem?_append_right (Nat.le_refl idx), Nat.sub_self]; rfl
  have htake : ((ms_pre ++ (pre ++ m₀ :: post)) ++ ms_post).take idx = ms_pre ++ pre := by
    rw [hms_full, List.take_append_of_le_length (Nat.le_refl idx), List.take_length]
  have hvis_pre : runVis r (ms_pre ++ pre) = runVis r ms_pre := by
    rw [runVis_append_local, PtPrefixInv38.runMoves_snd_of_movesFrom_invisibleNoEffect hpre,
      List.append_nil]
  have hcc : callCount (runVis r (((ms_pre ++ (pre ++ m₀ :: post)) ++ ms_post).take idx)) =
      (callStarts τ_pre).length := by
    rw [htake, hvis_pre]; exact callCount_eq_callStarts_length_local hB_blk.pre.2.2.2.2.2
  obtain ⟨v₀, hv₀, hvk₀, _⟩ := xpl_head_entry hm₀ (e := .recv blob) rfl
  have hrk : RecvHeadKind m₀ := xpl_recvHeadKind m₀ tr_m hv₀ hvk₀
  have hm₀_all_kinds : ∀ w ∈ m₀.vis tr_m, w.kind = .recv ∨ w.kind = .rng := by
    intro w hw
    obtain ⟨e, he, hew⟩ := xpl_forall₂_mem_right hm₀ w hw
    have hek := xpl_kind_of_matches hew
    rcases List.mem_cons.mp he with rfl | he'
    · exact Or.inl hek
    · obtain ⟨p, _, rfl⟩ := List.mem_map.mp he'
      exact Or.inr hek
  have hany_out : (m₀.vis tr_m).any (fun v => v.kind == .send || v.kind == .accept) = false := by
    apply List.any_eq_false.mpr
    intro v hv
    rcases hm₀_all_kinds v hv with h | h <;> simp [h]
  have hany_in : (m₀.vis tr_m).any (fun v => v.kind == .recv || v.kind == .pt) = true := by
    apply List.any_eq_true.mpr
    exact ⟨v₀, hv₀, by simp [hvk₀, eventKind]⟩
  have hout_step := hof.2 idx m₀ hidx
  rw [hcc, htake] at hout_step
  have hor := hout_step hany_in hok_pre
  have hdone : (eventIdx isAliceDone tr_m (m₀.next tr_m)).isSome = true := by
    rcases hor with hout_true | hdone
    · rw [hany_out] at hout_true; cases hout_true
    · exact hdone
  have hneff : ¬ NoSessionEffect tr_m m₀ := by
    intro heff
    have hnone : eventIdx isAliceDone tr_m (m₀.next tr_m) = none :=
      Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.eventIdx_eq_none_of_nonSessionPQExt
        (m₀.le_next tr_m)
        (fun j hge hlt => (heff j (List.mem_range'.mpr ⟨j - tr_m.length, by omega, by omega⟩)).2.1)
    rw [hnone] at hdone; cases hdone
  have hnoacc : ∀ w ∈ m₀.vis tr_m, w.kind ≠ .accept := by
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
  obtain ⟨a', b', idIdx, regIdx, bh, shown, rfl⟩ := hm₀_aliceStart
  have hany_recv : ((Move.aliceStart a' b' idIdx regIdx bh shown).vis tr_m).any
      (fun v => v.kind == .recv) = true := by
    apply List.any_eq_true.mpr
    exact ⟨v₀, hv₀, by simp [hvk₀, eventKind]⟩
  have hrng_step := hrng idx _ hidx
  rw [htake] at hrng_step
  have hrng' := hrng_step hany_recv
  exact CliCoinSplit.init_cut_eq_of_aliceDone
    hcoins hrng' ha₀ hdone hcs_blk hm₀

theorem not_pt_cli_2_self {r : Records} {S : Sem} {τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 2) τ₁ g ms)
    (hem : EventMatchesEntry SpecTop.compI0 r S g (.pt (ptAt 35)) (ptEntryOfNextEncrypt r ms))
    (hmemo : MemoCollisionOn SpecTop.compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms) : False := by
  have htake2 : cliTrace.take 2 = [.recv (wireAt 0), .rng cliCoins0] := rfl
  have hex' : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok [.recv (wireAt 0), .rng cliCoins0] τ₁ g ms :=
    htake2 ▸ hex
  obtain ⟨hτ₁, hexp⟩ := CliCoinSplit.init_exit0_cut_eq (by decide) cliCoins0_length hex'
  rw [init_draws_cliCoins0_eq] at hτ₁
  subst hτ₁
  exact PtPrefixInv35.ptDeadAt35_self r S g ms hfits hnb hexp hem hmemo

theorem not_pt_cli_2 {r : Records} {S : Sem} {τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 2) τ₁ g ms)
    (hem : EventMatchesEntry SpecTop.compI0 r S g (.pt (ptAt 35)) (ptEntryOfNextEncrypt r ms))
    (hmemo : ∀ g' ∈ PrefixGhostsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
        g ms (cliTrace.take 2),
      MemoCollisionOn SpecTop.compI0 r S g' (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms) : False :=
  not_pt_cli_2_self hfits hnb hex hem (hmemo g (mem_prefixGhostsCli_self hex))

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc in
theorem send_blk_inits_of_xplBlock6
    {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost}
    {ms₀ δ : List Move} {τ_pre blk : List MachineEvent} {pt coins w : HwBytes}
    (hcs : CoinSplit [.pt pt, .rng coins, .send w] blk)
    (hB : XplBlock6 i r S g ms₀ δ τ_pre blk) :
    ∃ rs : List MachineEvent,
      blk = .pt pt :: (rs ++ [.send w]) ∧
      (∀ e ∈ rs, eventKind e = .rng) ∧
      (∀ c, .rng c ∈ rs → c ∈ coins.inits) := by
  obtain ⟨pieces, _, hpre_p, rfl⟩ := CliCoinSplit.coinSplit_send_exit0_inv hcs
  have hhead : ∀ e ∈ (.pt pt :: (pieces.map MachineEvent.rng ++ [.send w])).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp at he; subst he; exact Or.inr rfl
  have hne : (.pt pt :: (pieces.map MachineEvent.rng ++ [.send w])) ≠ [] := List.cons_ne_nil _ _
  have htail : ∀ e ∈ (.pt pt :: (pieces.map MachineEvent.rng ++ [.send w])).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he
    simp only [List.tail_cons, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨p, _, rfl⟩ | rfl <;> { dsimp [eventKind]; decide }
  obtain ⟨pre, m, post, rfl, _, ⟨_, _, hm⟩, _⟩ := xpl6_oneMove hB hhead hne htail
  obtain ⟨me, sIdx, cl, pq, wrap, rfl, hls, _, hm_enc⟩ :=
    CliCoinSplit.invert_send_move_split (w := w) (by simp) hm
  obtain ⟨st, hst, hns⟩ := encrypt_state_of_lastSent_ne_none hls
  have hown : ownSaltsFrom (setupTrace r) (ms₀ ++ (pre ++ Move.encrypt me sIdx cl pq wrap :: post)) = true :=
    hB.run.2.2.2.2.1
  have hms_eq : ms₀ ++ (pre ++ Move.encrypt me sIdx cl pq wrap :: post) =
      (ms₀ ++ pre) ++ Move.encrypt me sIdx cl pq wrap :: post := by simp [List.append_assoc]
  have hpq' := pq_eq_of_ownSaltsFrom_split hown hms_eq
  rw [runMoves_append_fst, ← xpl_runTrace_eq] at hpq'
  rw [encrypt_next_eq_encNextTr_of_ownSalt hst hns hpq'] at hm_enc
  refine ⟨pieces.map MachineEvent.rng, rfl, CliCoinSplitClose.map_rng_kind, ?_⟩
  rcases (PtPrefixInv38.encVis_rs_cases CliCoinSplitClose.map_rng_kind hm_enc).2 with
    ⟨_, hrs_nil⟩ | ⟨_, c, hrs_eq, _⟩
  · intro c hc; rw [hrs_nil] at hc; cases hc
  · intro c' hc'
    rw [hrs_eq, List.mem_singleton, MachineEvent.rng.injEq] at hc'
    subst c'
    rcases pieces with _ | ⟨p0, _ | ⟨p1, _⟩⟩ <;> simp at hrs_eq
    obtain ⟨rest, hcoins_eq⟩ := hpre_p
    simp only [hrs_eq, List.flatten_cons, List.flatten_nil, List.append_nil] at hcoins_eq
    have hc_le : c.length ≤ coins.length := by rw [← hcoins_eq, List.length_append]; omega
    have hc_take : coins.take c.length = c := by rw [← hcoins_eq, List.take_left]
    rw [← hc_take]
    exact CliCoinSplit.mem_inits_of_take coins hc_le

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
theorem not_pt_cli_5_self {r : Records} {S : Sem} {τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 5) τ₁ g ms)
    (hem : EventMatchesEntry SpecTop.compI0 r S g (.pt (ptAt 38)) (ptEntryOfNextEncrypt r ms))
    (hmemo : MemoCollisionOn SpecTop.compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms) : False := by
  have htake5 : cliTrace.take 5 =
      [.recv (wireAt 0), .rng cliCoins0, .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] := rfl
  have hex' : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok
      [.recv (wireAt 0), .rng cliCoins0, .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)]
      τ₁ g ms := htake5 ▸ hex
  obtain ⟨blk₁, hτ₁, hcs₁, hexp⟩ :=
    CliCoinSplit.explainsCli_init_send_decomp (by decide) cliCoins0_length hex'
  rw [init_draws_cliCoins0_eq] at hτ₁
  have htake35 : Witnesses.Cheval26WeakStateIdx1.trace.take 35 =
      .recv PtDead35.bundle0 :: PtDead35.call0Rng := rfl
  rw [htake35] at hτ₁
  subst hτ₁
  have hmp6 := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hexp.1
  obtain ⟨pieces, _, _, hblk₁⟩ := CliCoinSplit.coinSplit_send_exit0_inv hcs₁
  have hhead₁ : ∀ e ∈ blk₁.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; rw [hblk₁] at he; simp at he; subst he; exact Or.inr rfl
  obtain ⟨ms₀, δ₁, hms_eq, hmp₀, hfor₁⟩ :=
    matchedPrefix6_split hmp6 hhead₁ (matchedPrefix6_prefix_reachable hmp6)
  obtain ⟨rs₁, rfl, hrs₁_kind, hrs₁_inits⟩ :=
    send_blk_inits_of_xplBlock6 hcs₁ ⟨hmp₀, hms_eq ▸ hmp6.2.1, hfor₁⟩
  have hinv := (PtPrefixInv38.take38_inv_cref_rs hfits.1.1 hnb hrs₁_kind hrs₁_inits hmp6 (.inl rfl)).2.2.1
  exact Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt.not_pt_collision_of_ne_bytes_full hem
    (PtDead38.ptAvoidFull_prefixTerms_of_pre38PrefixInv hfits.1.1 hexp.1 (.inl rfl) hinv)
    hmemo

theorem not_pt_cli_5 {r : Records} {S : Sem} {τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 5) τ₁ g ms)
    (hem : EventMatchesEntry SpecTop.compI0 r S g (.pt (ptAt 38)) (ptEntryOfNextEncrypt r ms))
    (hmemo : ∀ g' ∈ PrefixGhostsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
        g ms (cliTrace.take 5),
      MemoCollisionOn SpecTop.compI0 r S g' (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms) : False :=
  not_pt_cli_5_self hfits hnb hex hem (hmemo g (mem_prefixGhostsCli_self hex))

theorem callStarts_map_rng_append (pieces : List HwBytes) (τ : List MachineEvent) :
    callStarts (pieces.map MachineEvent.rng ++ τ) = callStarts τ := by
  unfold callStarts
  induction pieces with
  | nil => rfl
  | cons p ps ih => exact ih

theorem coinSplit_callStarts_eq {σ τ : List MachineEvent} (h : CoinSplit σ τ) :
    callStarts τ = callStarts σ := by
  induction h with
  | nil => rfl
  | keep _ _ ih =>
    unfold callStarts at ih ⊢
    simp only [List.filter_cons]
    split <;> simp [ih]
  | split _ _ _ ih =>
    rw [callStarts_map_rng_append]
    unfold callStarts at ih ⊢
    exact ih

theorem map_rng_kind_local {pieces : List HwBytes} :
    ∀ e ∈ pieces.map MachineEvent.rng, eventKind e = .rng := by
  intro e he
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp he
  rfl

theorem map_rng_snoc_send_kind_local {pieces : List HwBytes} {w : HwBytes} :
    ∀ e ∈ pieces.map MachineEvent.rng ++ [MachineEvent.send w],
      eventKind e = .rng ∨ eventKind e = .send := by
  intro e he
  rcases List.mem_append.mp he with h1 | h2
  · exact Or.inl (map_rng_kind_local e h1)
  · simp only [List.mem_singleton] at h2
    subst h2; exact Or.inr rfl

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure in
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace in
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
theorem rpk_blk_cut_eq {r : Records} {S : Sem} {g : Ghost}
    {τ₀ blk : List MachineEvent} {b_wire coins b_pt : HwBytes}
    {ms₀ δ ms_post : List Move} {p : PreKeyFields}
    (hcoins : coins.length = 32)
    (hcs_blk : CoinSplit [.recv b_wire, .rng coins, .accept b_pt] blk)
    (hw : b_wire.head? = some 3#8)
    (hp : parsePreKeyWire b_wire = some p)
    (hnk : ¬ KnownBaseKey SpecTop.compI0 r S g ms₀ p)
    (hB : XplBlock6 SpecTop.compI0 r S g ms₀ δ τ₀ blk)
    (hrng : RngLengthsFaithfulCli SpecTop.compI0 r S g ((ms₀ ++ δ) ++ ms_post)) :
    blk = [.recv b_wire, .rng coins, .accept b_pt] := by
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs_blk
  obtain ⟨pieces, τ2, _, hp_pref, rfl, hcs2⟩ := coinSplit_rng_cons hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs2
  cases hcs3
  let rs := pieces.map MachineEvent.rng
  have hrs : ∀ e ∈ rs, eventKind e = .rng := map_rng_kind_local
  have hhead : ∀ e ∈ ((.recv b_wire :: (rs ++ [.accept b_pt])) : List MachineEvent).head?,
      eventKind e = .recv ∨ eventKind e = .pt := by
    intro e he; simp at he; subst he; exact Or.inl rfl
  have htail : ∀ e ∈ ((.recv b_wire :: (rs ++ [.accept b_pt])) : List MachineEvent).tail,
      eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak := by
    intro e he; simp only [List.tail_cons, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · rw [hrs e he]; exact ⟨by decide, by decide, by decide⟩
    · exact ⟨by nofun, by nofun, by nofun⟩
  obtain ⟨pre₁, m, post₁, rfl, hpre, ⟨_, ha, hm⟩, _⟩ :=
    xpl6_oneMove hB hhead (by simp) htail
  set tr_pre := (runMoves pre₁ (runTraceMoves r ms₀)).1
  have hbob_eq := bobDoneBaseKeys_runMoves_of_movesFrom (runTraceMoves r ms₀) pre₁ hpre
  have hact : ActorIn ((moveActor m).getD r.bob) m := by
    unfold ActorIn; rcases moveActor m with _ | _ <;> simp
  have hmem_acc : MachineEvent.accept b_pt ∈ (.recv b_wire :: (rs ++ [.accept b_pt])) := by simp
  obtain ⟨v_acc, hv_acc, hev_acc⟩ := xpl_forall₂_mem_left hm (.accept b_pt) hmem_acc
  have hk_acc : v_acc.kind = .accept := by rw [xpl_kind_of_matches hev_acc]; rfl
  rcases xpl_accept_by m tr_pre hv_acc hk_acc hact with hbob | hdec
  · unfold BobStartBy at hbob
    cases m with
    | bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown =>
      let m₀ := Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx shown
      have htr_eq : tr_pre = runTraceMoves r (ms₀ ++ pre₁) :=
        (CompPrefixInvStruct.runTrace_append r ms₀ pre₁).symm
      have hms_full : (ms₀ ++ (pre₁ ++ m₀ :: post₁)) ++ ms_post =
          (ms₀ ++ pre₁) ++ (m₀ :: (post₁ ++ ms_post)) := by simp [List.append_assoc]
      let idx := (ms₀ ++ pre₁).length
      have hidx : ((ms₀ ++ (pre₁ ++ m₀ :: post₁)) ++ ms_post)[idx]? = some m₀ := by
        rw [hms_full, List.getElem?_append_right (Nat.le_refl idx), Nat.sub_self]; rfl
      have htake : ((ms₀ ++ (pre₁ ++ m₀ :: post₁)) ++ ms_post).take idx = ms₀ ++ pre₁ := by
        rw [hms_full, List.take_append_of_le_length (Nat.le_refl idx), List.take_length]
      obtain ⟨v₀, _, hv₀_match, _, hvu⟩ := xpl_forall₂_cons_left hm
      have hv₀_mem : v₀ ∈ m₀.vis tr_pre := by rw [hvu]; exact List.mem_cons_self ..
      have hv₀_kind : v₀.kind = .recv := hv₀_match.1.symm
      have hany_recv : (m₀.vis tr_pre).any (fun v => v.kind == .recv) = true :=
        List.any_eq_true.mpr ⟨v₀, hv₀_mem, by simp [hv₀_kind]⟩
      have hrng_m : ∀ (v : VisEntry) (t : DY.Bytes),
          v ∈ m₀.vis tr_pre → v.kind = .rng → v.layout = .single → v.terms = [t] →
          (gamma SpecTop.compI0 S g t).length = 32 := by
        intro v t hv hvk hvl hvt
        have hrng_step := hrng idx m₀ hidx
        rw [htake, ← htr_eq] at hrng_step
        exact hrng_step hany_recv v t hv hvk hvl hvt
      obtain ⟨w⟩ := CompSetupSecrecy.bobStart_accept_ok hv_acc hk_acc
      have hm_next : m₀.next tr_pre = PtPrefixInv78a.bobStartTr tr_pre b a w :=
        PtPrefixInv78a.bobStart_next_eq w
      have hnr : newRandoms tr_pre (m₀.next tr_pre) = [(randTerm tr_pre.length 32, 32)] := by
        rw [hm_next]
        have hlt : tr_pre.length < (PtPrefixInv78a.bobStartTr tr_pre b a w).length :=
          PtPrefixInv78a.length_lt_bobStartTr w
        obtain ⟨k, hk⟩ : ∃ k, (PtPrefixInv78a.bobStartTr tr_pre b a w).length - tr_pre.length = k + 1 :=
          ⟨(PtPrefixInv78a.bobStartTr tr_pre b a w).length - tr_pre.length - 1, by omega⟩
        unfold newRandoms newIndices
        rw [hk, List.range'_succ, List.filterMap_cons, PtPrefixInv78a.at?_rnd_bobStartTr w tr_pre.length]
        simp only [↓reduceIte, Option.map_some, List.cons.injEq, true_and]
        rw [List.filterMap_eq_nil_iff]
        intro j hj
        rw [List.mem_range'_1] at hj
        have hj_ne : j ≠ tr_pre.length := by omega
        have hj_ge : ¬ j < tr_pre.length := by omega
        rw [PtPrefixInv78a.at?_rnd_bobStartTr w j]
        simp only [hj_ne, ↓reduceIte, Option.map_eq_none_iff]
        exact Symbolic.Swarm.CREF.at?_ge_length tr_pre (by omega)
      have hvis_eq := PtPrefixInv78b.bobStart_vis_eq tr_pre b a kh regIdxA mh pqIdx spqrMsgIdx shown
      change m₀.vis tr_pre = (bobVis tr_pre (m₀.next tr_pre) mh (bobOpkPk b kh tr_pre)).take shown at hvis_eq
      rw [hvis_eq] at hm hv_acc
      rcases hpt : receivedPlaintext tr_pre (m₀.next tr_pre) with _ | ptTerm
      · exfalso
        have hv' := List.mem_of_mem_take hv_acc
        unfold bobVis at hv'
        rw [hnr, hpt] at hv'
        dsimp only [List.map, Option.map, Option.toList, List.cons_append, List.append_nil] at hv'
        rcases List.mem_cons.mp hv' with rfl | hv''
        · cases hk_acc
        · rcases List.mem_cons.mp hv'' with rfl | hv'''
          · cases hk_acc
          · cases hv'''
      · unfold bobVis at hm hv_acc
        rw [hnr, hpt] at hm hv_acc
        dsimp only [List.map, Option.map, Option.toList, List.cons_append, List.nil_append] at hm hv_acc
        have hsh3 : 3 ≤ shown := by
          rcases shown with _ | _ | _ | sh'
          · simp at hv_acc
          · simp at hv_acc; subst hv_acc; cases hk_acc
          · simp at hv_acc; rcases hv_acc with rfl | rfl <;> cases hk_acc
          · omega
        rw [List.take_of_length_le hsh3] at hm
        rcases pieces with _ | ⟨d, _ | ⟨d2, rest⟩⟩
        · have hlen := hm.length_eq; simp at hlen
        · rcases hm with _ | ⟨_, _ | ⟨hm_rng, _⟩⟩
          have hd_eq : [gamma SpecTop.compI0 S g (randTerm tr_pre.length 32)] = [d] := hm_rng.2
          injection hd_eq with hd_eq'
          have hd_len : d.length = 32 := by
            rw [← hd_eq']
            refine hrng_m (rngEntry (randTerm tr_pre.length 32)) (randTerm tr_pre.length 32) ?_ rfl rfl rfl
            rw [hvis_eq]; unfold bobVis; rw [hnr, hpt]
            dsimp only [List.map, Option.map, Option.toList, List.cons_append, List.nil_append]
            rw [List.take_of_length_le hsh3]; simp
          obtain ⟨rest_c, hcoins_eq⟩ := hp_pref
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hcoins_eq
          have hrest_nil : rest_c = [] := by
            apply List.eq_nil_of_length_eq_zero
            have hcl := congrArg List.length hcoins_eq
            rw [List.length_append, hd_len, hcoins] at hcl; omega
          subst hrest_nil; rw [List.append_nil] at hcoins_eq; subst hcoins_eq; rfl
        · have hlen := hm.length_eq; simp at hlen
    | _ => exact False.elim hbob
  · exfalso
    obtain ⟨v, u', hv, _, hvu⟩ := xpl_forall₂_cons_left hm
    have hv_mem : v ∈ m.vis tr_pre := by rw [hvu]; exact List.mem_cons_self ..
    have hvk : v.kind = .recv := hv.1.symm
    rw [xpl_vis_eq] at hv_mem
    rcases List.mem_append.1 hv_mem with hown | hexp
    · unfold DecryptBy at hdec
      cases m with
      | decrypt _ _ _ _ _ wrapped | decryptSkipped _ _ _ _ _ _ wrapped =>
        dsimp only [xpl_ownVis, decVis] at hown
        rcases List.mem_append.1 hown with h12 | h3
        · rcases List.mem_append.1 h12 with h1 | h2
          · obtain ⟨b_msg, _, rfl⟩ := Option.map_eq_some_iff.1 (Option.mem_toList.1 h1)
            cases wrapped
            · exact not_eventMatchesEntry_whisper_of_head SpecTop.compI0 r S g b_wire [b_msg] none hw hv
            · refine preKeyInner_rejected_of_foreign SpecTop.compI0 r S g b_wire p
                (sessionBaseKeys tr_pre _) [b_msg] none hp ?_ hv
              exact fun ek hek hbk =>
                hnk ⟨ek, hbob_eq ▸ mem_bobDoneBaseKeys_of_mem_sessionBaseKeys hek, hbk⟩
          · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h2; cases hvk
        · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 (Option.mem_toList.1 h3); cases hvk
      | _ => exact False.elim hdec
    · have hk := xpl_exposures_kind hexp; rw [hvk] at hk; cases hk

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
theorem not_pt_cli_13_self {r : Records} {S : Sem} {τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 13) τ₁ g ms)
    (hem : EventMatchesEntry SpecTop.compI0 r S g (.pt (ptAt 78)) (ptEntryOfNextEncrypt r ms))
    (hmemo : MemoCollisionOn SpecTop.compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms) : False := by
  have ⟨hcs, hmp, hof, hrng⟩ := hex
  have halice : r.alice = "alice" :=
    Symbolic.BugInjection.Proofs.Common443.CompFitsNames.compFits_alice hfits
  have htr_eq : cliTrace.take 13 =
      [.recv (wireAt 0), .rng cliCoins0,
       .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37),
       .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40),
       .recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42),
       .recv (wireAt 43), .rng cliCoins4] := rfl
  rw [htr_eq] at hcs
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs
  obtain ⟨p0, τ2, hp0_ne, hp0_pref, rfl, hcs2⟩ := coinSplit_rng_cons hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs2
  obtain ⟨p1, τ4, hp1_ne, hp1_pref, rfl, hcs4⟩ := coinSplit_rng_cons hcs3
  obtain ⟨τ5, rfl, hcs5⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs4
  obtain ⟨τ6, rfl, hcs6⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs5
  obtain ⟨p2, τ7, hp2_ne, hp2_pref, rfl, hcs7⟩ := coinSplit_rng_cons hcs6
  obtain ⟨τ8, rfl, hcs8⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs7
  obtain ⟨τ9, rfl, hcs9⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs8
  obtain ⟨p3, τ10, hp3_ne, hp3_pref, rfl, hcs10⟩ := coinSplit_rng_cons hcs9
  obtain ⟨τ11, rfl, hcs11⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs10
  obtain ⟨τ12, rfl, hcs12⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs11
  obtain ⟨p4, τ13, hp4_ne, hp4_pref, rfl, hcs13⟩ := coinSplit_rng_cons hcs12
  cases hcs13
  let b0 : List MachineEvent := .recv (wireAt 0) :: p0.map .rng
  let b1 : List MachineEvent := .pt (ptAt 35) :: (p1.map .rng ++ [.send (sendAt 37)])
  let b2 : List MachineEvent := .pt (ptAt 38) :: (p2.map .rng ++ [.send (wireAt 40)])
  let b3 : List MachineEvent := .recv (wireAt 40) :: p3.map .rng ++ [.accept (acceptAt 42)]
  let b4 : List MachineEvent := .recv (wireAt 43) :: p4.map .rng
  have hmp_assoc : DY.Libsignal.Composed.Refinement.MatchedPrefix SpecTop.compI0 r S
      Witnesses.Cheval26WeakStateIdx1.who g ms ((((b0 ++ b1) ++ b2) ++ b3) ++ b4) := by
    simpa [b0, b1, b2, b3, b4, List.append_assoc] using hmp
  obtain ⟨ms₄, δ₄, hms₄_eq, hmp₄_comp, hfor₄⟩ :=
    matchedPrefix_split hmp_assoc (by intro e he; simp [b4] at he; subst he; exact Or.inl rfl)
  obtain ⟨ms₃, δ₃, hms₃_eq, hmp₃_comp, hfor₃⟩ :=
    matchedPrefix_split hmp₄_comp (by intro e he; simp [b3] at he; subst he; exact Or.inl rfl)
  obtain ⟨ms₂, δ₂, hms₂_eq, hmp₂_comp, hfor₂⟩ :=
    matchedPrefix_split hmp₃_comp (by intro e he; simp [b2] at he; subst he; exact Or.inr rfl)
  obtain ⟨ms₁, δ₁, hms₁_eq, hmp₁_comp, hfor₁⟩ :=
    matchedPrefix_split hmp₂_comp (by intro e he; simp [b1] at he; subst he; exact Or.inr rfl)
  have hmp₁_nil : DY.Libsignal.Composed.Refinement.MatchedPrefix SpecTop.compI0 r S
      Witnesses.Cheval26WeakStateIdx1.who g ms₁ ([] ++ b0) := hmp₁_comp
  obtain ⟨ms₀, δ₀, hms₀_eq, hmp₀_comp, hfor₀⟩ :=
    matchedPrefix_split hmp₁_nil (by intro e he; simp [b0] at he; subst he; exact Or.inl rfl)
  have hcs_b0 : CoinSplit [.recv (wireAt 0), .rng cliCoins0] b0 := by
    simpa [b0] using CoinSplit.keep (fun _ h => by cases h) (.split hp0_ne hp0_pref .nil)
  have hcs_b1 : CoinSplit [.pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37)] b1 :=
    .keep (fun _ h => by cases h) (.split hp1_ne hp1_pref (.keep (fun _ h => by cases h) .nil))
  have hcs_b2 : CoinSplit [.pt (ptAt 38), .rng cliCoins2, .send (wireAt 40)] b2 :=
    .keep (fun _ h => by cases h) (.split hp2_ne hp2_pref (.keep (fun _ h => by cases h) .nil))
  have hcs_b3 : CoinSplit [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] b3 :=
    .keep (fun _ h => by cases h) (.split hp3_ne hp3_pref (.keep (fun _ h => by cases h) .nil))
  have hcs_b4 : CoinSplit [.recv (wireAt 43), .rng cliCoins4] b4 := by
    simpa [b4] using CoinSplit.keep (fun _ h => by cases h) (.split hp4_ne hp4_pref .nil)
  have hcs_pre4 : CoinSplit (cliTrace.take 11) (((b0 ++ b1) ++ b2) ++ b3) := by
    have htake11 : cliTrace.take 11 =
        [.recv (wireAt 0), .rng cliCoins0,
         .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37),
         .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40),
         .recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] := rfl
    rw [htake11]
    simpa [b0, b1, b2, b3, List.append_assoc] using
      CoinSplit.keep (fun _ h => by cases h) (.split hp0_ne hp0_pref
        (.keep (fun _ h => by cases h) (.split hp1_ne hp1_pref
          (.keep (fun _ h => by cases h) (.keep (fun _ h => by cases h) (.split hp2_ne hp2_pref
            (.keep (fun _ h => by cases h) (.keep (fun _ h => by cases h) (.split hp3_ne hp3_pref
              (.keep (fun _ h => by cases h) .nil))))))))))
  have hms_from_1 : ms = (ms₀ ++ δ₀) ++ (δ₁ ++ δ₂ ++ δ₃ ++ δ₄) := by
    simp [hms₄_eq, hms₃_eq, hms₂_eq, hms₁_eq, hms₀_eq, List.append_assoc]
  have hb0_eq : b0 = .recv PtDead35.bundle0 :: PtDead35.call0Rng := by
    have h := init_blk_cut_eq cliCoins0_length hcs_b0
      ⟨hmp₀_comp, hms₀_eq ▸ hmp₁_comp.2.1, hfor₀⟩
      (hms₀_eq ▸ hmp₁_nil)
      (hms_from_1 ▸ hof)
      (hms_from_1 ▸ hrng)
      (by rw [halice]; rfl) rfl
    rw [init_draws_cliCoins0_eq] at h
    exact h
  have hcc_pre4 : (callStarts (((b0 ++ b1) ++ b2) ++ b3)).length = 4 := by
    rw [coinSplit_callStarts_eq hcs_pre4]; rfl
  have hms_from_4 : ms = (ms₄ ++ δ₄) ++ [] := by simp [hms₄_eq]
  have hb4_eq : b4 = seg 43 35 := by
    have h := init_blk_cut_eq cliCoins4_length hcs_b4
      ⟨hmp₄_comp, hms₄_eq ▸ hmp_assoc.2.1, hfor₄⟩
      (hms₄_eq ▸ hmp_assoc)
      (hms_from_4 ▸ hof)
      (hms_from_4 ▸ hrng)
      (by rw [hcc_pre4, halice]; rfl)
      (by rw [hcc_pre4]; rfl)
    rw [init_draws_cliCoins4_eq] at h
    exact h
  obtain ⟨rs₁, hb1_eq, hrs₁_kind, hrs₁_inits⟩ :=
    send_blk_inits_of_xplBlock6 hcs_b1
      ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₁_comp,
       hms₁_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₂_comp).2.1, hfor₁⟩
  obtain ⟨rs₂, hb2_eq, hrs₂_kind, hrs₂_inits'⟩ :=
    send_blk_inits_of_xplBlock6 hcs_b2
      ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₂_comp,
       hms₂_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₃_comp).2.1, hfor₂⟩
  have hrs₂_inits : ∀ c, .rng c ∈ rs₂ → c ∈ PtPrefixInv78b.cliCoins2Fast.inits :=
    fun c hc => cliCoins2_inits_sub c (hrs₂_inits' c hc)
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  have hb0_bd : AllBobDone (fun _ => False) (runTraceMoves r ms₁) := by
    rw [hms₀_eq]
    exact allBobDone_xplBlock_ini
      ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₀_comp,
       hms₀_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₁_comp).2.1, hfor₀⟩
      map_rng_kind_local
      (allBobDone_matchedPrefix_nil (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₀_comp))
  have hb1_bd : AllBobDone (fun _ => False) (runTraceMoves r ms₂) := by
    rw [hms₁_eq]
    exact allBobDone_xplBlock_send
      ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₁_comp,
       hms₁_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₂_comp).2.1, hfor₁⟩
      map_rng_snoc_send_kind_local hb0_bd
  have hb2_bd : AllBobDone (fun _ => False) (runTraceMoves r ms₃) := by
    rw [hms₂_eq]
    exact allBobDone_xplBlock_send
      ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₂_comp,
       hms₂_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₃_comp).2.1, hfor₂⟩
      map_rng_snoc_send_kind_local hb1_bd
  have hnk40 : ¬ KnownBaseKey SpecTop.compI0 r S g ms₃ p40 :=
    not_knownBaseKey_of_allBobDone_false hb2_bd
  have hms_from_3 : ms = (ms₃ ++ δ₃) ++ δ₄ := by simp [hms₄_eq, hms₃_eq]
  have hb3_eq : b3 = seg 40 3 :=
    rpk_blk_cut_eq PtPrefixInv78b.rngAt41_length hcs_b3 wireAt40_head? hp40 hnk40
      ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₃_comp,
       hms₃_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₄_comp).2.1, hfor₃⟩
      (hms_from_3 ▸ hrng)
  have hwire40_eq_send39 : wireAt 40 = sendAt 39 := rfl
  rw [hwire40_eq_send39] at hb2_eq
  rw [hb0_eq, hb1_eq, hb2_eq, hb3_eq, hb4_eq] at hmp_assoc
  have hinv := PtPrefixInv78b.pre78PrefixInv_rs hfits.1.1 hnb
    hrs₁_kind hrs₁_inits hrs₂_kind hrs₂_inits hmp_assoc
  exact Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt.not_pt_collision_of_ne_bytes_full hem
    (PtDead78.ptAvoidFull_prefixTerms_of_pre78PrefixInv hfits.1.1 hex.2.1 hinv)
    hmemo

theorem not_pt_cli_13 {r : Records} {S : Sem} {τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hnb : CompSetupSecrecy.NoBrk r ms)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 13) τ₁ g ms)
    (hem : EventMatchesEntry SpecTop.compI0 r S g (.pt (ptAt 78)) (ptEntryOfNextEncrypt r ms))
    (hmemo : ∀ g' ∈ PrefixGhostsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
        g ms (cliTrace.take 13),
      MemoCollisionOn SpecTop.compI0 r S g' (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms) : False :=
  not_pt_cli_13_self hfits hnb hex hem (hmemo g (mem_prefixGhostsCli_self hex))

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
theorem not_knownBaseKey_cli_8 {r : Records} {S : Sem} {τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move} {p : PreKeyFields}
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 8) τ₁ g ms) :
    ¬ KnownBaseKey SpecTop.compI0 r S g ms p := by
  have ⟨hcs, hmp, _, _⟩ := hex
  have htr_eq : cliTrace.take 8 =
      [.recv (wireAt 0), .rng cliCoins0,
       .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37),
       .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40)] := rfl
  rw [htr_eq] at hcs
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs
  obtain ⟨p0, τ2, _, _, rfl, hcs2⟩ := coinSplit_rng_cons hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs2
  obtain ⟨p1, τ4, _, _, rfl, hcs4⟩ := coinSplit_rng_cons hcs3
  obtain ⟨τ5, rfl, hcs5⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs4
  obtain ⟨τ6, rfl, hcs6⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs5
  obtain ⟨p2, τ7, _, _, rfl, hcs7⟩ := coinSplit_rng_cons hcs6
  obtain ⟨τ8, rfl, hcs8⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs7
  cases hcs8
  let b0 : List MachineEvent := .recv (wireAt 0) :: p0.map .rng
  let b1 : List MachineEvent := .pt (ptAt 35) :: (p1.map .rng ++ [.send (sendAt 37)])
  let b2 : List MachineEvent := .pt (ptAt 38) :: (p2.map .rng ++ [.send (wireAt 40)])
  have hmp_cref : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms ((b0 ++ b1) ++ b2) := by
    have h0 := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp
    simpa [b0, b1, b2, List.append_assoc] using h0
  obtain ⟨ms₂, δ₂, rfl, hmp₂, hfor₂⟩ := matchedPrefix6_split hmp_cref
    (by intro e he; simp [b2] at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable hmp_cref)
  obtain ⟨ms₁, δ₁, rfl, hmp₁, hfor₁⟩ := matchedPrefix6_split hmp₂
    (by intro e he; simp [b1] at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable hmp₂)
  have hmp₁' : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₁ ([] ++ b0) := hmp₁
  obtain ⟨ms₀, δ₀, rfl, hmp₀, hfor₀⟩ := matchedPrefix6_split hmp₁'
    (by intro e he; simp [b0] at he; subst he; exact Or.inl rfl) (matchedPrefix6_prefix_reachable hmp₁')
  have hb0 : AllBobDone (fun _ => False) (runTraceMoves r (ms₀ ++ δ₀)) :=
    allBobDone_xplBlock_ini ⟨hmp₀, hmp₁.2.1, hfor₀⟩ map_rng_kind_local (allBobDone_matchedPrefix_nil hmp₀)
  have hb1 : AllBobDone (fun _ => False) (runTraceMoves r ((ms₀ ++ δ₀) ++ δ₁)) :=
    allBobDone_xplBlock_send ⟨hmp₁, hmp₂.2.1, hfor₁⟩ map_rng_snoc_send_kind_local hb0
  have hb2 : AllBobDone (fun _ => False) (runTraceMoves r (((ms₀ ++ δ₀) ++ δ₁) ++ δ₂)) :=
    allBobDone_xplBlock_send ⟨hmp₂, hmp_cref.2.1, hfor₂⟩ map_rng_snoc_send_kind_local hb1
  exact not_knownBaseKey_of_allBobDone_false hb2

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
theorem not_knownBaseKey_cli_16 {r : Records} {S : Sem} {τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move} {p : PreKeyFields} (hp : parsePreKeyWire (wireAt 81) = some p)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 16) τ₁ g ms) :
    ¬ KnownBaseKey SpecTop.compI0 r S g ms p := by
  have ⟨hcs, hmp, _, hrng⟩ := hex
  have htr_eq : cliTrace.take 16 =
      [.recv (wireAt 0), .rng cliCoins0, .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37),
       .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40), .recv (wireAt 40), .rng (rngAt 41),
       .accept (acceptAt 42), .recv (wireAt 43), .rng cliCoins4, .pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80)] := rfl
  rw [htr_eq] at hcs
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs
  obtain ⟨p0, τ2, _, _, rfl, hcs2⟩ := coinSplit_rng_cons hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs2
  obtain ⟨p1, τ4, _, _, rfl, hcs4⟩ := coinSplit_rng_cons hcs3
  obtain ⟨τ5, rfl, hcs5⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs4
  obtain ⟨τ6, rfl, hcs6⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs5
  obtain ⟨p2, τ7, _, _, rfl, hcs7⟩ := coinSplit_rng_cons hcs6
  obtain ⟨τ8, rfl, hcs8⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs7
  obtain ⟨τ9, rfl, hcs9⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs8
  obtain ⟨p3, τ10, hp3_ne, hp3_pref, rfl, hcs10⟩ := coinSplit_rng_cons hcs9
  obtain ⟨τ11, rfl, hcs11⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs10
  obtain ⟨τ12, rfl, hcs12⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs11
  obtain ⟨p4, τ13, _, _, rfl, hcs13⟩ := coinSplit_rng_cons hcs12
  obtain ⟨τ14, rfl, hcs14⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs13
  obtain ⟨p5, τ15, _, _, rfl, hcs15⟩ := coinSplit_rng_cons hcs14
  obtain ⟨τ16, rfl, hcs16⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs15
  cases hcs16
  let b0 : List MachineEvent := .recv (wireAt 0) :: p0.map .rng
  let b1 : List MachineEvent := .pt (ptAt 35) :: (p1.map .rng ++ [.send (sendAt 37)])
  let b2 : List MachineEvent := .pt (ptAt 38) :: (p2.map .rng ++ [.send (wireAt 40)])
  let b3 : List MachineEvent := .recv (wireAt 40) :: p3.map .rng ++ [.accept (acceptAt 42)]
  let b4 : List MachineEvent := .recv (wireAt 43) :: p4.map .rng
  let b5 : List MachineEvent := .pt (ptAt 78) :: (p5.map .rng ++ [.send (sendAt 80)])
  have hmp_cref : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms
      (((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5) := by
    have h0 := Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp
    simpa [b0, b1, b2, b3, b4, b5, List.append_assoc] using h0
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  have hp40_bk : p40.baseKey.take 33 = ecKey ek1PubKey := baseKey_of_map wireAt40_baseKey hp40
  have hb0 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ b0 →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    have h' : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ([] ++ b0) := h
    obtain ⟨ms_nil, δ₀, rfl, hmp_nil, hfor₀⟩ := matchedPrefix6_split h'
      (by intro e he; simp [b0] at he; subst he; exact Or.inl rfl) (matchedPrefix6_prefix_reachable h')
    exact allBobDone_xplBlock_ini ⟨hmp_nil, h.2.1, hfor₀⟩ map_rng_kind_local (allBobDone_matchedPrefix_nil hmp_nil)
  have hb1 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ (b0 ++ b1) →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨ms_0, δ₁, rfl, hmp_0, hfor₁⟩ := matchedPrefix6_split h
      (by intro e he; simp [b1] at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable h)
    exact allBobDone_xplBlock_send ⟨hmp_0, h.2.1, hfor₁⟩ map_rng_snoc_send_kind_local (hb0 ms_0 hmp_0)
  have hb2 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ((b0 ++ b1) ++ b2) →
      AllBobDone (fun _ => False) (runTraceMoves r ms₀) := by
    intro ms₀ h
    obtain ⟨ms_1, δ₂, rfl, hmp_1, hfor₂⟩ := matchedPrefix6_split h
      (by intro e he; simp [b2] at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable h)
    exact allBobDone_xplBlock_send ⟨hmp_1, h.2.1, hfor₂⟩ map_rng_snoc_send_kind_local (hb1 ms_1 hmp_1)
  have hnk40 : ∀ ms₀, Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms₀ ((b0 ++ b1) ++ b2) →
      ¬ KnownBaseKey SpecTop.compI0 r S g ms₀ p40 := fun ms₀ h => not_knownBaseKey_of_allBobDone_false (hb2 ms₀ h)
  obtain ⟨ms_4, δ_5, rfl, hmp_4, hfor_5⟩ := matchedPrefix6_split hmp_cref
    (by intro e he; simp [b5] at he; subst he; exact Or.inr rfl) (matchedPrefix6_prefix_reachable hmp_cref)
  obtain ⟨ms_3, δ_4, rfl, hmp_3, hfor_4⟩ := matchedPrefix6_split hmp_4
    (by intro e he; simp [b4] at he; subst he; exact Or.inl rfl) (matchedPrefix6_prefix_reachable hmp_4)
  obtain ⟨ms_2, δ_3, hms_3_eq, hmp_2, hfor_3⟩ := matchedPrefix6_split hmp_3
    (by intro e he; simp [b3] at he; subst he; exact Or.inl rfl) (matchedPrefix6_prefix_reachable hmp_3)
  have hcs_b3 : CoinSplit [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] b3 :=
    .keep (fun _ h => by cases h) (.split hp3_ne hp3_pref (.keep (fun _ h => by cases h) .nil))
  have hms_from_3 : (ms_3 ++ δ_4) ++ δ_5 = (ms_2 ++ δ_3) ++ (δ_4 ++ δ_5) := by simp [hms_3_eq, List.append_assoc]
  have hb3_eq : b3 = [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] :=
    rpk_blk_cut_eq PtPrefixInv78b.rngAt41_length hcs_b3 wireAt40_head? hp40 (hnk40 ms_2 hmp_2)
      ⟨hmp_2, hms_3_eq ▸ hmp_3.2.1, hfor_3⟩ (hms_from_3 ▸ hrng)
  have hmp_3' : Symbolic.Swarm.CREF.MatchedPrefix SpecTop.compI0 r S g ms_3
      (((b0 ++ b1) ++ b2) ++ [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)]) := by rwa [← hb3_eq]
  have hb3 : AllBobDone (fun ek => ecKey (gamma SpecTop.compI0 S g ek) = ecKey ek1PubKey) (runTraceMoves r ms_3) :=
    allBobDone_matchedPrefix_rpk wireAt40_head? hp40 hnk40
      (fun m₀ hm₀ => allBobDone_of_bobDoneBaseKeys fun ek hek => False.elim (bobDoneBaseKeys_of_allBobDone (hb2 m₀ hm₀) ek hek))
      (fun ek hek => by rw [hek, hp40_bk]) hmp_3'
  have hb4 : AllBobDone (fun ek => ecKey (gamma SpecTop.compI0 S g ek) = ecKey ek1PubKey) (runTraceMoves r (ms_3 ++ δ_4)) :=
    allBobDone_xplBlock_ini ⟨hmp_3, hmp_4.2.1, hfor_4⟩ map_rng_kind_local hb3
  have hb5 : AllBobDone (fun ek => ecKey (gamma SpecTop.compI0 S g ek) = ecKey ek1PubKey) (runTraceMoves r ((ms_3 ++ δ_4) ++ δ_5)) :=
    allBobDone_xplBlock_send ⟨hmp_4, hmp_cref.2.1, hfor_5⟩ map_rng_snoc_send_kind_local hb4
  exact wireAt81_not_knownBaseKey_of_allBobDone_ek1 hp hb5

theorem explains_of_explainsCli {interp : ExternInterpretation} {r : Records} {S : Sem}
    {who : List Participant} {ok : Nat → Bool} {σ₁ τ₁ : List MachineEvent}
    {g : Ghost} {ms : List Move}
    (h : ExplainsCli interp r S who ok σ₁ τ₁ g ms) :
    ExplainsMoves interp r S who ok g ms τ₁ :=
  ⟨h.2.1, h.2.2.1.1⟩

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge
