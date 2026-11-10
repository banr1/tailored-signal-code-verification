/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Memo
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryFixed

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Top

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs (callsOf SchedFits flatEvents)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_nil explainsClassical_of)
open Symbolic.BugInjection
open Symbolic.BugInjection.Synthetic
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
  (evInit evSend rngMsg39 ptB_eq_ptMsg35 schedFits_evInit schedFits_evInit_evSend)
open Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Defs
open Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Memo
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private theorem breakFree_cliEventsIR : BreakFree cliEventsIR :=
  breakFree_cons_run _ (breakFree_cons_run _ (breakFree_cons_run _ breakFree_nil))

private theorem callsOf_cliEventsIR :
    callsOf cliEventsIR = [("alice", true), ("alice", true), ("bob", true)] := rfl

set_option linter.unnecessarySeqFocus false in
private theorem schedFits_cliEventsIR :
    SchedFits (callsOf cliEventsIR)
      Witnesses.Cheval26SmallSubgroupHighBitComp.who
      Witnesses.Cheval26SmallSubgroupHighBitComp.ok := by
  rw [callsOf_cliEventsIR]
  refine ⟨by decide, fun k p b hget => ?_⟩
  rcases k with _ | _ | _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

private theorem runWrapped_evSend : runWrapped evSend = true := by
  unfold runWrapped evSend
  dsimp only [Option.bind]
  rw [CompRPlantWire.sentWireBytes_eq]
  decide

private theorem list_eq_three_splits {α : Type} {a b c x : α} {xs ys : List α}
    (h : [a, b, c] = xs ++ x :: ys) :
    (xs = [] ∧ x = a ∧ ys = [b, c]) ∨
    (xs = [a] ∧ x = b ∧ ys = [c]) ∨
    (xs = [a, b] ∧ x = c ∧ ys = []) := by
  rcases xs with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, xs⟩⟩⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
  · simp at h

private theorem not_knownBaseKeyOn_of_bobDone_nil {i : ExternInterpretation} {S : Sem}
    {g : Ghost} {tr : ExecTrace} {p : PreKeyFields}
    (h : bobDoneBaseKeys tr = []) : ¬ KnownBaseKeyOn i S g tr p := by
  rintro ⟨ek, hek, _⟩; rw [h] at hek; cases hek

private theorem coinSplit_rng_only :
    ∀ {c : HwBytes} {xs : List MachineEvent},
      CoinSplit [.rng c] xs → ∀ e ∈ xs, eventKind e = .rng := by
  intro c xs hcs
  cases hcs with
  | keep hne _ => exact absurd rfl (hne c)
  | split _ _ hrest =>
    cases hrest with
    | nil =>
      intro e he
      rw [List.append_nil, List.mem_map] at he
      obtain ⟨_, _, rfl⟩ := he
      rfl

private theorem coinSplit_rng_send :
    ∀ {c w : HwBytes} {xs : List MachineEvent},
      CoinSplit [.rng c, .send w] xs →
      ∀ e ∈ xs, eventKind e = .rng ∨ eventKind e = .send := by
  intro c w xs hcs
  cases hcs with
  | keep hne _ => exact absurd rfl (hne c)
  | split _ _ hrest =>
    cases hrest with
    | keep _ hnil =>
      cases hnil with
      | nil =>
        intro e he
        rcases List.mem_append.mp he with hr | hs
        · rw [List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr; exact Or.inl rfl
        · simp only [List.mem_singleton] at hs; subst hs; exact Or.inr rfl

private theorem coinSplit_rng_accept :
    ∀ {c acc : HwBytes} {xs : List MachineEvent},
      CoinSplit [.rng c, .accept acc] xs →
      (∀ e ∈ xs, eventKind e ≠ .recv ∧ eventKind e ≠ .pt ∧ eventKind e ≠ .leak) ∧
      (∃ e ∈ xs, eventKind e = .accept) := by
  intro c acc xs hcs
  cases hcs with
  | keep hne _ => exact absurd rfl (hne c)
  | split _ _ hrest =>
    cases hrest with
    | keep _ hnil =>
      cases hnil with
      | nil =>
        refine ⟨fun e he => ?_, .accept acc, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
        rcases List.mem_append.mp he with hr | ha
        · rw [List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr
          exact ⟨(fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩
        · simp only [List.mem_singleton] at ha; subst ha
          exact ⟨(fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h)⟩

private theorem coinSplit_keep_inv {e : MachineEvent} {σ τ : List MachineEvent}
    (hne : ∀ b, e ≠ .rng b) (h : CoinSplit (e :: σ) τ) :
    ∃ τ', τ = e :: τ' ∧ CoinSplit σ τ' := by
  cases h with
  | keep _ h' => exact ⟨_, rfl, h'⟩
  | split _ _ _ => exact absurd rfl (hne _)

private theorem coinSplit_rng_inv {c : HwBytes} {σ τ : List MachineEvent}
    (h : CoinSplit (.rng c :: σ) τ) :
    ∃ (pieces : List HwBytes) (τ' : List MachineEvent),
      τ = pieces.map MachineEvent.rng ++ τ' ∧ CoinSplit σ τ' := by
  cases h with
  | keep hne _ => exact absurd rfl (hne c)
  | split _ _ h' => exact ⟨_, _, rfl, h'⟩

private theorem no_coinSplit_matchedPrefix_ir
    {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move}
    {τhw : List MachineEvent}
    (hcs : CoinSplit (flatEvents cliEventsIR) τhw) :
    ¬ DY.Libsignal.Composed.Refinement.MatchedPrefix compI0 r S who₀ g ms τhw := by
  intro hmp
  change CoinSplit
    ([.recv CompRX0SS38.bunBytes, .rng cliCoins0,
      .pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes,
      .recv msg38_ir, .rng rngMsg39, .accept []]) τhw at hcs
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_keep_inv (by rintro _ ⟨⟩) hcs
  obtain ⟨pieces0, τ2, rfl, hcs2⟩ := coinSplit_rng_inv hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_keep_inv (by rintro _ ⟨⟩) hcs2
  obtain ⟨pieces1, τ4, rfl, hcs4⟩ := coinSplit_rng_inv hcs3
  obtain ⟨τ5, rfl, hcs5⟩ := coinSplit_keep_inv (by rintro _ ⟨⟩) hcs4
  obtain ⟨rest, rfl, hcs6⟩ := coinSplit_keep_inv (by rintro _ ⟨⟩) hcs5
  let rs0 : List MachineEvent := pieces0.map .rng
  let b0 : List MachineEvent := .recv CompRX0SS38.bunBytes :: rs0
  let tail1 : List MachineEvent := pieces1.map .rng ++ [.send CompRPlantWire.sentWireBytes]
  let b1 : List MachineEvent := .pt CompRX0SS38.ptB :: tail1
  obtain ⟨hrest_ne, hacc⟩ := coinSplit_rng_accept hcs6
  have hrs0 : ∀ e ∈ rs0, eventKind e = .rng := by
    intro e he; rw [List.mem_map] at he; obtain ⟨_, _, rfl⟩ := he; rfl
  have htail1 : ∀ e ∈ tail1, eventKind e = .rng ∨ eventKind e = .send := by
    intro e he
    rcases List.mem_append.mp he with hr | hs
    · rw [List.mem_map] at hr; obtain ⟨_, _, rfl⟩ := hr; exact Or.inl rfl
    · simp only [List.mem_singleton] at hs; subst hs; exact Or.inr rfl
  have hτ_eq :
      (MachineEvent.recv CompRX0SS38.bunBytes :: (pieces0.map .rng ++
        (.pt CompRX0SS38.ptB :: (pieces1.map .rng ++
          (.send CompRPlantWire.sentWireBytes :: (.recv msg38_ir :: rest)))))) =
      (b0 ++ b1) ++ (.recv msg38_ir :: rest) := by
    simp [b0, b1, rs0, tail1, List.append_assoc]
  have hnoleak : ∀ e ∈ (b0 ++ b1) ++ (.recv msg38_ir :: rest), eventKind e ≠ .leak := by
    intro e he
    rcases List.mem_append.mp he with hb01 | hr2
    · rcases List.mem_append.mp hb01 with hb0' | hb1'
      · rcases List.mem_cons.mp hb0' with rfl | hrs
        · decide
        · rw [hrs0 e hrs]; decide
      · rcases List.mem_cons.mp hb1' with rfl | ht1
        · decide
        · rcases htail1 e ht1 with h | h <;> rw [h] <;> decide
    · rcases List.mem_cons.mp hr2 with rfl | hrest
      · decide
      · exact (hrest_ne e hrest).2.2
  have hmp_cref : Symbolic.Swarm.CREF.MatchedPrefix compI0 r S g ms
      ((b0 ++ b1) ++ (.recv msg38_ir :: rest)) := by
    rw [← hτ_eq]
    exact ⟨hmp.1, hmp.2.1, hmp.2.2.2.2.2⟩
  exact not_matchedPrefix_ir_tail (sw := CompRPlantWire.sentWireBytes)
    rfl hrs0 rfl htail1 hrest_ne hacc hnoleak hmp_cref

theorem spec_half_pinned :
    cliCompShape.SpecHalf
      (cliCompFitsPinned Witnesses.ImplicitRejectMacCli.setup)
      Witnesses.ImplicitRejectMacCli.trace := by
  rw [← cliEventsIR_eq]
  intro (iw : cliCompShape.Interp) (r : Records) hfits
  have hfits_hb : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup iw.1 r :=
    compFitsPinned_hb_of_ir hfits.1
  have hwf : ProtocolSetupWF r := hfits_hb.1.1
  have hiw : iw.1 = compI0 := hfits_hb.2.1
  have hfits0 : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r :=
    hiw ▸ hfits_hb
  refine ⟨hwf, fun (S : Sem) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis cliEventsIR) ∨
    CollisionAfterExplainedPrefix iw.1 r S cliEventsIR at hdisj
  rw [hiw] at hdisj
  have ⟨hhead38, hq38, _, _⟩ := msg38_ir_props
  rcases hdisj with ⟨g, ss, vis, hex⟩ | hcol
  · have hex_cl := explainsClassical_of hex breakFree_cliEventsIR
    have hnrc : ¬ ReadCollisionCliClassical compI0 r S g ss cliEventsIR := by
      refine not_readCollisionCliClassical_of_preKey_recv hwf.1 hex_cl.2.2.2 ?_
      intro evs₁ ev evs₂ out hevs ⟨peer, hcmd⟩ _
      rcases list_eq_three_splits hevs with ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩
      · injection hev with hev'; subst hev'; cases hcmd
      · injection hev with hev'; subst hev'; cases hcmd
      · injection hev with hev'; subst hev'
        refine ⟨hq38, ?_⟩
        intro ev' out' hev' ⟨p', hcmd'⟩ _
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hev'
        rcases hev' with h1 | h2
        · injection h1 with h1'; subst h1'; cases hcmd'
        · injection h2 with h2'; subst h2'; cases hcmd'
    obtain ⟨τ, ms, hex_cli, _, _, _⟩ :=
      xlate_inv_with_noBrk hwf schedFits_cliEventsIR hex_cl hnrc
    exact no_coinSplit_matchedPrefix_ir hex_cli.1 hex_cli.2.1
  · refine not_collisionAfterExplainedPrefix_of_splits breakFree_cliEventsIR ?_ hcol
    intro evs₁ ev evs₂ g ss vis hevs hex
    rcases list_eq_three_splits hevs with ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩
    · injection hev with hev'; subst hev'
      exact not_nextEventCollidesClassical_init rfl
    · injection hev with hev'; subst hev'
      have hnrc₁ : ¬ ReadCollisionCliClassical compI0 r S g ss [.run evInit] := by
        refine not_readCollisionCliClassical_of_no_recv ?_
        intro ev' out' hev' ⟨p', hcmd'⟩ _
        simp only [List.mem_singleton] at hev'
        injection hev' with hev''; subst hev''; cases hcmd'
      refine not_nextEventCollidesClassical_send hwf schedFits_evInit hex hnrc₁ rfl ?_
      intro τ ms hex_cli _ hnb hbme hmcol
      obtain ⟨hτ, hex_hw⟩ := CliCoinSplit.init_exit0_cut_eq (by decide) cliCoins0_length hex_cli
      subst hτ
      dsimp only [evInit, evSend] at hex_hw hbme
      rw [init_draws_cliCoins0_eq_hb, trace_take_35_eq] at hex_hw
      have hem : EventMatchesEntry compI0 r S g (.pt ptMsg35)
          (ptEntryOfNextEncrypt r ms) :=
        ⟨rfl, by simpa [EventMatchesEntry, BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt,
          ptB_eq_ptMsg35, eventBytes] using hbme⟩
      have hmcol' : MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
          (runTraceMoves r ms) (runVis r ms)
          (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
        simpa [MemoCollisionOn, ptEntryAt, ptEntryOfNextEncrypt] using hmcol
      exact ptDead35_self hwf hnb hex_hw hem hmcol'
    · injection hev with hev'; subst hev'
      have hnrc₂ : ¬ ReadCollisionCliClassical compI0 r S g ss [.run evInit, .run evSend] := by
        refine not_readCollisionCliClassical_of_no_recv ?_
        intro ev' out' hev' ⟨p', hcmd'⟩ _
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hev'
        rcases hev' with h1 | h2
        · injection h1 with h1'; subst h1'; cases hcmd'
        · injection h2 with h2'; subst h2'; cases hcmd'
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hq38
      rcases hmsg : msg38_ir with _ | ⟨tag, body⟩
      · rw [hmsg] at hp; cases hp
      · have htag : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by
          intro h; apply hhead38; rw [hmsg, h]; rfl
        have hbob_nil : bobDoneBaseKeys (runTrace r ss) = [] := by
          refine bobDoneBaseKeys_nil_of_matchesEventsClassical_no_recv hwf.1 hex.2.2.2 ?_
          intro ev' out' hev' ⟨p', hcmd'⟩ _
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hev'
          rcases hev' with h1 | h2
          · injection h1 with h1'; subst h1'; cases hcmd'
          · injection h2 with h2'; subst h2'; cases hcmd'
        have hnkb : ¬ KnownBaseKeyOn compI0 S g (runTrace r ss) p :=
          not_knownBaseKeyOn_of_bobDone_nil hbob_nil
        have hnkm : ¬ KyberMismatch compI0 r p := not_kyberMismatch_compI0 r p
        refine not_nextEventCollidesClassical_recv_preKey hwf schedFits_evInit_evSend hex hnrc₂
          rfl hmsg htag (hmsg ▸ hp) hnkb hnkm ?_
        intro τ ms hex_cli _ hnb htr hsalts hpre_vis hpt_vis
        obtain ⟨blk₁, hτ, hcs₁, _⟩ :=
          CliCoinSplit.explainsCli_init_send_decomp (by decide) cliCoins0_length hex_cli
        rw [initiateDrawsOfCoins_cliCoins0_eq] at hτ
        subst hτ
        obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hpre, hmid, hpost, hm₀, x, hx, hnbsc⟩ :=
          noBsc_ir_cli_swap hcs₁ r S g ms p hfits0 hnb hex_cli hp
        subst hms_eq
        let tr₁ := (runMoves pre (setupTrace r)).1
        let o := aliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
        let m₀ := Move.aliceStart r.alice r.bob 4 6 hb_eq shown
        let tr₂ := (runMoves mid (m₀.next tr₁)).1
        let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post
        have htr' : runTraceMoves r ms' = runTrace r ss :=
          (CompRVariantFree38.runTrace_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
            (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))).symm.trans htr
        have hsalts' : honestSalts r ms' = honestSaltsOf r ss :=
          (honestSalts_split38_swap_eq r pre mid post m₀ r.alice (tr₁.length + 8) cl (tr₂.length + 2)
            (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))).symm.trans hsalts
        have hpre' : prefixTerms r (runTrace r ss) (runVis r ms') = prefixTerms r (runTrace r ss) vis :=
          prefixTerms_split38_swap_eq_of_init_send hwf.1 rfl rfl rfl rfl runWrapped_evSend hex.2.2.2
            rfl hpre hmid hpost hm₀ htr hpre_vis hpt_vis
        have hpt' : plaintextTerms (runVis r ms') = plaintextTerms vis :=
          (plaintextTerms_split38_swap_eq hwf.1 (some (e, c')) (some (tr₁.length + 3, tr₁.length + 4))
            hpre hmid hpost).trans hpt_vis
        have hx' : x ∈ preKeyRepresentations compI0 r S g ms' (tag :: body) := by
          rwa [← hmsg]
        exact ⟨ms', x, htr', hsalts', hpre', hpt', hx', hnbsc⟩

theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned Witnesses.ImplicitRejectMacCli.setup iw r :=
  Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.cliCompFitsPinned_satisfiable_of_plausible
    Witnesses.ImplicitRejectMacCli.setup
    (by decide +kernel)
    (fun _ h => nomatch h)

theorem not_signalSessionSecure_of_implHalf {bytes : List (BitVec 8)}
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      cliCompShape.ImplHalf (cliCompFitsPinned Witnesses.ImplicitRejectMacCli.setup) elf
        Witnesses.ImplicitRejectMacCli.trace) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecure bytes :=
  not_signalSessionSecure_of_witness spec_half_pinned hi
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_implicitRejectMacCli

end Symbolic.BugInjection.Proofs.SyntheticImplicitRejectMac.Top
