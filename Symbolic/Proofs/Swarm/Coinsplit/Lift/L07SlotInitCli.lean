/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.UA.Defs
public import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPure
import Symbolic.Proofs.Refinement.Composed.Cli.ParD3ModelV2SlotsBase
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateRecord
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateRecordAux
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlots
import Symbolic.Proofs.Swarm.CREF.Cli.World.CallCountPure
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureB
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureC
import Symbolic.Proofs.Swarm.CREF.Initiate.ModelPure
import Symbolic.Proofs.Swarm.CREF.ModelSplit
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.Coinsplit.Slots.S2InitCut

/-!
# Cut-Polymorphic `init` Slot Refinement

Proves `SlotInitCliSpec`, lifting `slot_init_d7_pqModelRel` from single-cut `CliLiveAt` to
cut-polymorphic `CliLiveAtCli`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Coinsplit.Lift.L07

open CryptoProofLib.Refinement (ExternInterpretation)
open _root_.DY (Participant ExecTrace)
open _root_.DY.Libsignal (HwBytes)
open _root_.DY.Libsignal.HwEvents (MachineEvent)
open _root_.DY.Libsignal.Composed
open _root_.DY.Libsignal.Composed.Refinement
open _root_.DY.Libsignal.Composed.Refinement.Cli
open _root_.DY.Libsignal.Composed.Refinement.Cli.ParD3
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.Coinsplit.S1 (NoAdjRng)
open Symbolic.Swarm.Coinsplit.Lift

private theorem coinSplit_append_inv {σ₁ σ₂ τ : List MachineEvent}
    (hcs : CoinSplit (σ₁ ++ σ₂) τ) :
    ∃ τ₁ τ₂, τ = τ₁ ++ τ₂ ∧ CoinSplit σ₁ τ₁ ∧ CoinSplit σ₂ τ₂ := by
  induction σ₁ generalizing τ with
  | nil => exact ⟨[], τ, rfl, .nil, hcs⟩
  | cons x xs ih =>
    cases hcs with
    | keep hnx hcs_xs =>
      obtain ⟨τ₁, τ₂, rfl, h₁, h₂⟩ := ih hcs_xs
      exact ⟨x :: τ₁, τ₂, rfl, .keep hnx h₁, h₂⟩
    | split hne hpref hcs_xs =>
      obtain ⟨τ₁, τ₂, rfl, h₁, h₂⟩ := ih hcs_xs
      exact ⟨_, τ₂, (List.append_assoc _ _ _).symm, .split hne hpref h₁, h₂⟩

private theorem coinSplit_init_inv {blob coins : HwBytes} {blk_hw : List MachineEvent}
    (hcs : CoinSplit [.recv blob, .rng coins] blk_hw) :
    ∃ pieces : List HwBytes,
      (∀ p ∈ pieces, p ≠ []) ∧
      pieces.flatten <+: coins ∧
      blk_hw = .recv blob :: pieces.map MachineEvent.rng := by
  cases hcs with
  | keep _ hcs_rng =>
    cases hcs_rng with
    | keep hnr _ => exact absurd rfl (hnr coins)
    | split hne hpref hcs_nil =>
      cases hcs_nil
      exact ⟨_, hne, hpref, by simp⟩

private theorem outcomeFaithfulCli_prefix {r : ProtocolSetup} {ok : Nat → Bool} {ms₁ ms₂ : List Move}
    (h : OutcomeFaithfulCli r ok (ms₁ ++ ms₂))
    (hof₁ : OutcomeFaithful r ok ms₁) :
    OutcomeFaithfulCli r ok ms₁ := by
  refine ⟨hof₁, fun i m hi => ?_⟩
  have hi_lt : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi_app : (ms₁ ++ ms₂)[i]? = some m := by
    rw [List.getElem?_append_left hi_lt]; exact hi
  have htake : (ms₁ ++ ms₂).take i = ms₁.take i :=
    List.take_append_of_le_length (Nat.le_of_lt hi_lt)
  have hstep := h.2 i m hi_app
  rwa [htake] at hstep

private theorem rngLengthsFaithfulCli_prefix {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ms₁ ms₂ : List Move}
    (h : RngLengthsFaithfulCli interp r S g (ms₁ ++ ms₂)) :
    RngLengthsFaithfulCli interp r S g ms₁ := by
  intro i m hi
  have hi_lt : i < ms₁.length := (List.getElem?_eq_some_iff.mp hi).1
  have hi_app : (ms₁ ++ ms₂)[i]? = some m := by
    rw [List.getElem?_append_left hi_lt]; exact hi
  have htake : (ms₁ ++ ms₂).take i = ms₁.take i :=
    List.take_append_of_le_length (Nat.le_of_lt hi_lt)
  have hstep := h i m hi_app
  rwa [htake] at hstep

private theorem explainsCli_split_recv {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {σ_pre τ' : List MachineEvent} {blob coins : HwBytes} {g' : Ghost} {ms' : List Move}
    (hex' : ExplainsCli interp r S who ok (σ_pre ++ [.recv blob, .rng coins]) τ' g' ms')
    (hnrc' : ¬ ReadCollision interp r S g' ms' τ') :
    ∃ τ'_pre blk' ms'_pre δ,
      τ' = τ'_pre ++ blk' ∧
      ms' = ms'_pre ++ δ ∧
      CoinSplit σ_pre τ'_pre ∧
      CoinSplit [.recv blob, .rng coins] blk' ∧
      ExplainsCli interp r S who ok σ_pre τ'_pre g' ms'_pre ∧
      ¬ ReadCollision interp r S g' ms'_pre τ'_pre ∧
      XplBlock interp r S who g' ms'_pre δ τ'_pre blk' := by
  obtain ⟨τ'_pre, blk', rfl, hcs_pre, hcs_blk⟩ := coinSplit_append_inv hex'.1
  obtain ⟨pieces, _, _, hblk_eq⟩ := coinSplit_init_inv hcs_blk
  have hhead : ∀ e ∈ blk'.head?, eventKind e = .recv ∨ eventKind e = .pt := by
    rw [hblk_eq]; intro e he
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he; exact Or.inl rfl
  have hcl' : Clean interp r S who ok g' ms' (τ'_pre ++ blk') :=
    explainsCli_toClean hex' hnrc'
  obtain ⟨ms'_pre, δ, rfl, hmp_pre, hmatch⟩ := matchedPrefix_split hcl'.matched hhead
  have hcl'_pre : Clean interp r S who ok g' ms'_pre τ'_pre :=
    clean_prefix hmp_pre.2.2.2.2.2.length_eq hcl'
  have hex'_pre : ExplainsCli interp r S who ok σ_pre τ'_pre g' ms'_pre :=
    ⟨hcs_pre, hcl'_pre.matched,
      outcomeFaithfulCli_prefix hex'.2.2.1 hcl'_pre.1.2,
      rngLengthsFaithfulCli_prefix hex'.2.2.2⟩
  exact ⟨τ'_pre, blk', ms'_pre, δ, rfl, rfl, hcs_pre, hcs_blk, hex'_pre, hcl'_pre.2,
    ⟨hmp_pre, hcl'.matched.2.1, hmatch⟩⟩

private theorem forall2_rng_kind {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
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
      ·exact hm.1.symm
      · exact ih hrest v hmem

private theorem eventIdx_none_of_quietExt {tr tr' : ExecTrace}
    {p : _root_.DY.Libsignal.PQXDH.PQXDHEvent → Bool}
    (hq : IniSndPure.XplQuiet.QuietExt tr tr')
    (hp : p .BrokenDH = false ∧ p .BrokenKEM = false := by exact ⟨rfl, rfl⟩) :
    eventIdx p tr tr' = none := by
  have hlen : tr.length ≤ tr'.length := IniSndPure.XplQuiet.quietExt_len hq
  exact Symbolic.Proofs.Swarm.CREF.Cli.MoveBrkLemmas.eventIdx_eq_none_of_nonSessionPQExt hq.1
    (fun i h1 h2 => (hq.2 i h1 h2).2.1) hp

private theorem init_exit0_cut_eq
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {who : List Participant} {ok : Nat → Bool}
    {σ_pre τ'_pre blk' : List MachineEvent} {blob coins : HwBytes}
    {g' : Ghost} {ms'_pre δ : List Move}
    (hcoins : coins.length = 192)
    (hcs_blk : CoinSplit [.recv blob, .rng coins] blk')
    (hB_blk : XplBlock interp r S who g' ms'_pre δ τ'_pre blk')
    (hex' : ExplainsCli interp r S who ok (σ_pre ++ [.recv blob, .rng coins])
      (τ'_pre ++ blk') g' (ms'_pre ++ δ))
    (hnrc' : ¬ ReadCollision interp r S g' (ms'_pre ++ δ) (τ'_pre ++ blk'))
    (hwho_pre : who[(callStarts τ'_pre).length]? = some r.alice)
    (hok_pre : ok (callStarts τ'_pre).length = true) :
    blk' = .recv blob :: (Slots.initiateDrawsOfCoins coins).map MachineEvent.rng := by
  obtain ⟨pieces, _, _, rfl⟩ := coinSplit_init_inv hcs_blk
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
    obtain ⟨d, _, rfl⟩ := he; simp [eventKind]
  have hbi : IniBlockShape (.recv blob :: pieces.map MachineEvent.rng) := by
    refine ⟨⟨blob, rfl⟩, fun e he => ?_⟩
    simp only [List.tail_cons, List.mem_map] at he
    obtain ⟨d, _, rfl⟩ := he; rfl
  obtain ⟨pre, m, post, rfl, hpre, ⟨hs, ha, hvis_m⟩, _⟩ := xpl_oneMove hB_blk hhead hne htail
  have hcl' : Clean interp r S who ok g' (ms'_pre ++ (pre ++ m :: post))
      (τ'_pre ++ (.recv blob :: pieces.map MachineEvent.rng)) :=
    explainsCli_toClean hex' hnrc'
  have hdf : DeltaFaithful r.alice (runTraceMoves r ms'_pre) (pre ++ m :: post) :=
    IniPure.ini_deltaFaithful_of_explains hB_blk hcl'.1 hwho_pre
  have hact_m : ActorIn r.alice m :=
    actorIn_of_vis_ne_nil hdf (vis_ne_nil_of_forall₂ hvis_m hne)
  have hstep_m : IniStep r.alice (.recv blob :: pieces.map MachineEvent.rng)
      (runMoves pre (runTraceMoves r ms'_pre)).1 m :=
    xplStep_ini hs ha hvis_m hbi hact_m
  let tr_m := runTraceMoves r (ms'_pre ++ pre)
  have htr_eq : (runMoves pre (runTraceMoves r ms'_pre)).1 = tr_m :=
    (TR.runTrace_append r ms'_pre pre).symm
  rw [htr_eq] at ha hvis_m hstep_m
  let idx := ms'_pre.length + pre.length
  have hidx : (ms'_pre ++ (pre ++ m :: post))[idx]? = some m :=
    IniPure.ini_getElem?_append_middle ms'_pre pre post m
  have htake : (ms'_pre ++ (pre ++ m :: post)).take idx = ms'_pre ++ pre :=
    IniPure.ini_take_append_middle ms'_pre pre post m
  have hvis_pre : runVis r (ms'_pre ++ pre) = runVis r ms'_pre := by
    rw [CREF.runVis_append, IniPure.ini_invisible_nil pre (runTraceMoves r ms'_pre) hpre,
      List.append_nil]
  have hcc : callCount (runVis r ((ms'_pre ++ (pre ++ m :: post)).take idx)) =
      (callStarts τ'_pre).length := by
    rw [htake, hvis_pre]; exact CREF.callCount_eq_callStarts_length hB_blk.pre.2.2.2.2.2
  have hvis_blk := hvis_m
  cases hm_vis : m.vis tr_m with
  | nil => rw [hm_vis] at hvis_blk; cases hvis_blk
  | cons v₀ vs_tl =>
    rw [hm_vis] at hvis_blk
    cases hvis_blk with
    | cons hm_recv hm_rng =>
      have hv₀_kind : v₀.kind = .recv := hm_recv.1.symm
      have hany_recv : (m.vis tr_m).any (fun v => v.kind == .recv) = true := by
        rw [hm_vis]; simp [hv₀_kind]
      have hany_in : (m.vis tr_m).any (fun v => v.kind == .recv || v.kind == .pt) = true := by
        rw [hm_vis]; simp [hv₀_kind]
      have hany_out : (m.vis tr_m).any (fun v => v.kind == .send || v.kind == .accept) = false := by
        rw [hm_vis]
        apply List.any_eq_false.mpr
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hmem
        · simp [hv₀_kind]
        · simp [forall2_rng_kind hm_rng v hmem]
      have hout_step := hex'.2.2.1.2 idx m hidx
      rw [hcc, htake] at hout_step
      have hor := hout_step hany_in hok_pre
      have hdone : (eventIdx isAliceDone tr_m (m.next tr_m)).isSome = true := by
        rcases hor with hout_true | hdone
        · rw [hany_out] at hout_true; cases hout_true
        · exact hdone
      rcases hstep_m.2 with hini | hnse
      · cases m with
        | aliceStart a' b' idIdx regIdx bh shown =>
          have hrng_step := hex'.2.2.2 idx _ hidx
          rw [htake] at hrng_step
          have hrng := hrng_step hany_recv
          exact Symbolic.Swarm.Coinsplit.S2.init_cut_eq_of_aliceDone
            hcoins hrng ha hdone hcs_blk hvis_m
        | reject draws =>
          have hfalse := (hex'.2.2.1.1 idx (.reject draws) hidx).1 draws rfl
          rw [hcc, hok_pre] at hfalse; cases hfalse
        | attackerSend msg =>
          rw [vis_attackerSend_nil] at hm_vis; cases hm_vis
        | _ => cases hini
      · have hnone := eventIdx_none_of_quietExt (p := isAliceDone)
            (IniSndPure.XplQuiet.quietExt_of_noSessionEffect hnse)
        rw [hnone] at hdone; cases hdone

private theorem noAdjRng_append_recv_rng {σ_pre : List MachineEvent} {blob coins : HwBytes}
    (hadj : NoAdjRng σ_pre) :
    NoAdjRng (σ_pre ++ [.recv blob, .rng coins]) :=
  noAdjRng_append_of_head_nonRng hadj
    ⟨Or.inl (fun hc => by cases hc), trivial⟩
    (fun y hy => by
      simp only [List.head?_cons, Option.some.injEq] at hy
      subst hy; intro hc; cases hc)

private theorem inputsEquiv_pqInitInputsF {c : CliCall} {P : PEParams} {st : PqParty}
    {tape : List.Vector (BitVec 8) initiateTapeLen} {i : Inputs}
    (hi : InputsFor c (filesOf (encodeDir P st)) i)
    (hflat : BundleFilesFlat c.bundle)
    (hcmd : c.cmd = .init (partyAddress st.party.other) bundleDir)
    (hstdin : c.stdin = [])
    (htape : c.coins = tape.toList) :
    InputsEquiv i (pqInitInputsF P st c.bundle tape) := by
  obtain ⟨hargv, hdirs, his, hfiles, _⟩ := hi
  have hextra_reg : RegularFileList c.extra :=
    (regularFileList_of_bundleFilesFlat hflat).append
      (regularFile_root (by decide) (by decide) (by decide) (by decide))
  refine ⟨by rw [hargv, hcmd]; rfl, by rw [hdirs, hcmd]; rfl, by rw [his, hstdin]; rfl, fun p => ?_⟩
  by_cases hp : p ∈ stdioPaths
  · rw [filesOf_eq_none_of_mem_stdioPaths _ hp, filesOf_eq_none_of_mem_stdioPaths _ hp]
  · rw [hfiles p hp]
    unfold pqInitInputsF pqInputs
    rw [← htape]
    have hcomb : encodeDir P st ++ c.bundle ++ [(coinsFile, c.coins)] =
        encodeDir P st ++ c.extra := by simp [CliCall.extra, List.append_assoc]
    change _ = filesOf (encodeDir P st ++ c.bundle ++ [(coinsFile, c.coins)]) p
    rw [hcomb, filesOf_append_of_regular (regularFileList_encodeDir P st) hextra_reg p]

/-- Binary witness for a CLI `init` call, covering exit-1 rejection and exit-0 bundle acceptance. -/
def SlotInitWitness (interp' : ExternInterpretation) (r : ProtocolSetup)
    (t_clean t_clean' : CliTurn) (c : CliCall) (code : Nat) (out : HwBytes) : Prop :=
  (code = 1 ∧ out = [] ∧ t_clean' = t_clean ∧ t_clean.records r r.alice = none) ∨
  (code = 0 ∧ out = [] ∧
    ∃ (pb : PublicBundle) (recState : HwBytes),
      let ds := Slots.initiateDrawsOfCoins c.coins
      parseBundleFiles (filesOf c.bundle) = some pb ∧
      HonestBundle interp' r (bundleBlob pb) ∧
      IniOkBin (bundleBlob pb) ds ∧
      IniPure.AliceInitiatedV1PostPure interp' r (bundleBlob pb) ds recState ∧
      t_clean'.leakRecords r r.alice = some recState)

private def CliSlotPostStrong (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (t t_clean : CliTurn) (c : CliCall) (code : Nat) (out : HwBytes) (files : DirectorySnapshot)
    (accepted : List HwBytes) (σ_pre : List MachineEvent) : Prop :=
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let blk_cli := cliEntryEvents c ++ cliExitEvents c code out
  ∃ (t_clean' : CliTurn) (accepted' : List HwBytes),
    PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted' ∧
    SlotInitWitness interp' r t_clean t_clean' c code out ∧
    ∀ (who : List Participant) (ok : Nat → Bool),
      who[(callStarts σ_pre).length]? = some c.party →
      CliLiveAtCli interp' r S who ok t_clean accepted σ_pre →
      ((∃ τ_out g ms, CoinSplit (σ_pre ++ blk_cli) τ_out ∧
          MatchedPrefix interp' r S who g ms τ_out) ∨
        CollisionAfterExplainedPrefixMoves interp' r S who ok (σ_pre ++ blk_cli)) ∧
      (ok (callStarts σ_pre).length = decide (code = 0) →
        CliLiveAtCli interp' r S who ok t_clean' accepted' (σ_pre ++ blk_cli))

private theorem exit1_cliSlotPost
    (hGood : GoodExit0CutSpec) (hB : BridgeBQuietFailSpec)
    {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {t t_clean : CliTurn} {c : CliCall} {files : DirectorySnapshot} {blob : HwBytes}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hr : ProtocolSetupWF r)
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (halice : c.party = r.alice)
    (hcmd : c.cmd = .init (peerOf r r.alice) bundleDir)
    (hp_ne : c.party ≠ r.bob)
    (hrec_clean_none : t_clean.records r r.alice = none)
    (hscr : scrub files = t_clean.dirs r.alice)
    (hent : cliEntryEvents c ++ cliExitEvents c 1 [] = [.recv blob, .rng c.coins]) :
    CliSlotPostStrong interp P r t t_clean c 1 [] files accepted σ_pre := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  let blk_cli := cliEntryEvents c ++ cliExitEvents c 1 []
  let c1 := toCliCallNone c
  have hafter_clean : t_clean.after r c1 1 [] files = t_clean := by
    cases t_clean
    dsimp only [CliTurn.after]
    congr 1
    · funext q
      by_cases hqa : q = c1.party
      · subst hqa; simpa [c1, toCliCallNone, halice] using hscr
      · simp [hqa]
    · simp [c1, toCliCallNone, hcmd]
    · simp
  have hDir1 : PqDirInv interp' P r (t_clean.after r c1 1 [] files) accepted := by
    rw [hafter_clean]; exact hsim.dirInv
  have hsim' := pqTurnSim1A_nonBob_after (c1 := c1) hsim hp_ne rfl rfl rfl hDir1
  rw [hafter_clean] at hsim'
  refine ⟨t_clean, accepted, hsim', Or.inl ⟨rfl, rfl, rfl, hrec_clean_none⟩, fun who ok _ hlive => ?_⟩
  obtain ⟨τ_acc, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
  have hcl₀ : Clean interp' r S who ok g₀ ms₀ τ_acc := explainsCli_toClean hex₀ hnrc₀
  have hcs_blk_rej : CoinSplit blk_cli [.recv blob] := by
    change CoinSplit (cliEntryEvents c ++ cliExitEvents c 1 []) [.recv blob]
    rw [hent]; exact Slots.coinSplit_init_reject blob c.coins
  have hmp_rej : MatchedPrefix interp' r S who g₀
      (Sanitize.sanitizeMoves (setupTrace r) ms₀ ++ [.reject []])
      (τ_acc ++ [.recv blob]) := by
    simpa using IniPure.ini_matchedPrefix_reject interp' r S who g₀ ms₀ τ_acc blob [] hcl₀.matched
  refine ⟨Or.inl ⟨τ_acc ++ [.recv blob], g₀,
      Sanitize.sanitizeMoves (setupTrace r) ms₀ ++ [.reject []],
      IniPure.coinSplit_append hex₀.1 hcs_blk_rej, hmp_rej⟩,
    fun hok => ?_⟩
  have hok_false : ok (callStarts σ_pre).length = false := by simpa using hok
  have hok_acc : ok (callStarts τ_acc).length = false := by
    rwa [coinSplit_callStarts_eq hex₀.1]
  have hcl_rej : Clean interp' r S who ok g₀
      (Sanitize.sanitizeMoves (setupTrace r) ms₀ ++ [.reject []])
      (τ_acc ++ [.recv blob]) := by
    simpa using IniPure.ini_clean_reject blob [] hcl₀ hok_acc
  have ⟨hex_out, hnrc_out⟩ :=
    hGood hex₀ hcs_blk_rej (.callRecvFail hok_acc) (Or.inr rfl) (fun _ _ _ => rfl) hcl_rej
  refine ⟨?_, ⟨τ_acc ++ [.recv blob], g₀, _, hex_out, hnrc_out⟩, fun τ' ⟨g', ms', hex', hnrc'⟩ => ?_⟩
  · rw [hent]; exact noAdjRng_append_recv_rng hlive.noAdjRng
  · have hex'_ent : ExplainsCli interp' r S who ok (σ_pre ++ [.recv blob, .rng c.coins]) τ' g' ms' := by
      simpa only [blk_cli, hent] using hex'
    obtain ⟨τ'_pre, blk', ms'_pre, _, rfl, _, hcs_pre, hcs_blk, hex'_pre, hnrc'_pre, _⟩ :=
      explainsCli_split_recv hex'_ent hnrc'
    obtain ⟨hrel_pre, hopk_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms'_pre, hex'_pre, hnrc'_pre⟩
    have hok_pre : ok (callStarts τ'_pre).length = false := by
      rwa [coinSplit_callStarts_eq hcs_pre]
    exact hB hr (Or.inl rfl) hcs_blk hok_pre hrel_pre hopk_pre

private theorem slot_init_cli_strong
    (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (halice : c.party = r.alice)
    (hcmd : c.cmd = .init (peerOf r r.alice) bundleDir)
    (hstdin : c.stdin = [])
    (hcoins : c.coins.length = initiateTapeLen)
    (hrec_none : t.records r r.alice = none)
    (hflat : BundleFilesFlat c.bundle)
    (hhon_files : HonestBundleFiles interp r c.bundle)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    CliSlotPostStrong interp P r t t_clean c code out files accepted σ_pre := by
  let interp' := interpOfParams interp P
  let S := compSemOf interp' r
  have hext' : ExternContractsHoldCli interp' := externContractsHoldCli_interpOfParams P hext
  have hagree' : Slots.ModelAgree interp' P :=
    (slotsModelAgree_iff _ P).mpr ((modelAgree_interpOfParams interp P).mpr hagree)
  have hp_ne : c.party ≠ r.bob := halice ▸ hr.1
  have hd_alice : t_clean.dirs r.alice = t.dirs r.alice := hsim.dirs_other r.alice hr.1
  have hrec_clean_none : t_clean.records r r.alice = none := by
    simpa [CliTurn.records, hd_alice] using hrec_none
  obtain ⟨stA, hA⟩ := hsim.dirInv.1
  have hA_init := aliceInitPartyInv_of_pqPartyInv hext' hr hA
  obtain ⟨hsess_none, hdA⟩ :=
    hA_init.toAliceDirState_of_records_none hagree' hext'.1 hr hrec_clean_none
  let tape : List.Vector (BitVec 8) initiateTapeLen := ⟨c.coins, hcoins⟩
  have hcmd_stA : c.cmd = .init (partyAddress stA.party.other) bundleDir := by
    rw [hcmd, peerOf_eq_addrE_other, ← hA.party_eq]
  have hi_enc : InputsFor c (filesOf (encodeDir P stA)) i := by
    rwa [halice, ← hd_alice, hA.dir_eq] at hin
  have heq_f := inputsEquiv_pqInitInputsF (tape := tape) hi_enc hflat hcmd_stA hstdin rfl
  have hp := PqModelRel.exited_iff.mp hRel
  have hb_reg := regularFileList_of_bundleFilesFlat hflat
  have hb_scr := isScrubbedPath_of_bundleFilesFlat hflat
  cases hpb : parseBundleFiles (filesOf c.bundle) with
  | none =>
    have hobs := hp.initReject stA c.bundle tape hdA.wf hsess_none hflat hpb heq_f
    injection hobs with hcode hout hfiles
    subst hcode hout hfiles
    have hscr : scrub (filesOf (pqInitInputsF P stA c.bundle tape).files) =
        t_clean.dirs r.alice := by
      rw [hA.dir_eq]
      exact scrub_filesOf_pqInputs_reject P stA _ c.bundle _ [] hb_reg hb_scr
    exact exit1_cliSlotPost (blob := []) hGood hB hr hsim halice hcmd hp_ne hrec_clean_none hscr
      (by simp [cliEntryEvents, cliExitEvents, hcmd, hpb])
  | some pb =>
    have hbt : BundleTyped pb := ParD3.bundleTyped_of_parseBundleFiles hpb
    let bE := Slots.bundleEOfPublic pb
    have hb_eq : publicBundleOf bE = pb := Slots.publicBundleOf_bundleEOfPublic hbt
    have hpbE : parseBundleFiles (filesOf c.bundle) = some (publicBundleOf bE) := hb_eq.symm ▸ hpb
    have hhon_b : HonestBundle interp r (bundleBlob pb) := hhon_files pb hpb
    have hhon_b' : HonestBundle interp' r (bundleBlob pb) := by
      simpa only [HonestBundle, show interp' = interpOfParams interp P from rfl,
        pubBytes_interpOfParams] using hhon_b
    have hhonDirE : HonestBundleDir interp' r (publicBundleOf bE) := by
      rw [hb_eq]; exact ⟨hbt, hhon_b'⟩
    let X := Xof interp' P
    have hscr_ag := hp.initFiles X stA c.bundle bE tape hdA.wf hsess_none hflat hpbE heq_f
    unfold pqInitModel at hscr_ag
    cases htrust : stA.trusts ⟨⟨bE.idPub⟩⟩
    · simp only [htrust, Bool.not_false, ↓reduceIte, pqxdhExpectedOutcome, ScrubAgree] at hscr_ag
      rcases hscr_ag with ⟨rfl, rfl, hag⟩
      have hs1 : scrub (filesOf (pqInitInputsF P stA c.bundle tape).files) =
          t_clean.dirs r.alice := by
        rw [hA.dir_eq]
        exact scrub_filesOf_pqInputs_reject P stA _ c.bundle _ [] hb_reg hb_scr
      exact exit1_cliSlotPost (blob := bundleBlob pb) hGood hB hr hsim halice hcmd hp_ne
        hrec_clean_none ((funext hag).trans hs1) (by simp [cliEntryEvents, cliExitEvents, hcmd, hpb])
    · simp only [htrust, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hscr_ag
      rcases hinit : CryptoVerification.E2E.initiateState X P stA.party stA.me bE tape
          with _ | ⟨x, g⟩
      · simp only [hinit, pqxdhExpectedOutcome, ScrubAgree] at hscr_ag
        rcases hscr_ag with ⟨rfl, rfl, hag⟩
        have hs1 : scrub (filesOf (pqInitInputsF P stA c.bundle tape).files) =
            t_clean.dirs r.alice := by
          rw [hA.dir_eq]
          exact scrub_filesOf_pqInputs_reject P stA _ c.bundle _ [] hb_reg hb_scr
        exact exit1_cliSlotPost (blob := bundleBlob pb) hGood hB hr hsim halice hcmd hp_ne
          hrec_clean_none ((funext hag).trans hs1)
          (by simp [cliEntryEvents, cliExitEvents, hcmd, hpb])
      · let st' : PqParty := { stA with peerId := some ⟨⟨bE.idPub⟩⟩, session := some (x, g) }
        simp only [hinit, pqxdhExpectedOutcome, ScrubAgree] at hscr_ag
        rcases hscr_ag with ⟨rfl, rfl, hag⟩
        let c1 : CliCall :=
          { party := r.alice, cmd := c.cmd, bundle := (publicBundleOf bE).files bundleDir,
            stdin := [], coins := c.coins }
        obtain ⟨hal', _, _, hwf'⟩ :=
          Slots.wfPq_after_initiateState hagree' hext'.1 hr hdA.alice hdA.wf htrust hinit
        obtain ⟨hd', hdirs_other, hsent, hbobOff, hopk, hleakRec⟩ :=
          hdA.after_exit0 hagree' hext'.1 hr hsess_none (c := c1) rfl hcmd bE tape hal' hwf' x g rfl
        let files1 := filesOf ((pqInitInputs P stA bE tape).files ++ encodeDir P st')
        have hDir1' : PqDirInv interp' P r (t_clean.after r c1 0 [] files1) accepted :=
          pqDirInv_update_alice hext' hr hsim.dirInv hdirs_other hbobOff hd'
        have hmod_ok : pqInitModel X P stA bE tape = some (some (st', [])) := by
          simp [pqInitModel, htrust, hinit, st']
        obtain ⟨_, _, hsub⟩ := pqPartyInv_of_pqInitModel hA hmod_ok
        have hs1 : scrub (filesOf ((pqInitInputsF P stA c.bundle tape).files ++ encodeDir P st')) =
            filesOf (encodeDir P st') :=
          scrub_filesOf_pqInputs_accept P stA st' _ c.bundle _ [] hb_reg hb_scr hsub
        have hs2 : scrub files1 = filesOf (encodeDir P st') :=
          scrub_filesOf_pqInputs_accept P stA st' _ _ _ []
            (regularFileList_bundle_files _) (isScrubbedPath_bundle_files _) hsub
        have hscr_eq : scrub files = scrub files1 := (funext hag).trans (hs1.trans hs2.symm)
        have hsim' := pqTurnSim1A_nonBob_after (c1 := c1) hsim hp_ne halice.symm rfl hscr_eq hDir1'
        let recState := encodeRecordUnderExtras (fun _ => x) g
        let ds := Slots.initiateDrawsOfCoins c.coins
        let blk_hw : List MachineEvent := .recv (bundleBlob pb) :: ds.map MachineEvent.rng
        have hent_eq : cliEntryEvents c ++ cliExitEvents c 0 [] =
            [.recv (bundleBlob pb), .rng c.coins] := by
          simp [cliEntryEvents, cliExitEvents, hcmd, hpb]
        have hcs : CoinSplit (cliEntryEvents c ++ cliExitEvents c 0 []) blk_hw := by
          rw [hent_eq]
          exact Slots.coinSplit_init_ok (bundleBlob pb) hcoins
        obtain ⟨_, _, hout_pureE⟩ :=
          Slots.initiateState_ok_post hext' hagree' hr hdA.alice hdA.wf hhonDirE tape hinit
        rw [hb_eq] at hout_pureE
        obtain ⟨_, _, hhon, hbin, hV1⟩ := hout_pureE
        have hleak_alice :
            (t_clean.after r c1 0 [] files1).leakRecords r r.alice = some recState := by
          simpa using congrFun hleakRec r.alice
        refine ⟨t_clean.after r c1 0 [] files1, accepted, hsim',
          Or.inr ⟨rfl, rfl, pb, recState, hpb, hhon, hbin, hV1, hleak_alice⟩,
          fun who ok hwho hlive => ?_⟩
        obtain ⟨τ_acc, g₀, ms₀, hex₀, hnrc₀⟩ := hlive.witness
        have hcl₀ : Clean interp' r S who ok g₀ ms₀ τ_acc := explainsCli_toClean hex₀ hnrc₀
        have hwho_acc : who[(callStarts τ_acc).length]? = some r.alice := by
          rw [coinSplit_callStarts_eq hex₀.1, ← halice]; exact hwho
        obtain ⟨ms_opk, bh₀, g₀', -, -, -, hm₀'⟩ :=
          IniPure.ini_matchedPrefix_initOk interp' hext' r hr who g₀ ms₀ τ_acc
            (bundleBlob pb) ds hcl₀.matched hwho_acc hhon hbin
        refine ⟨Or.inl ⟨τ_acc ++ blk_hw, g₀', _, IniPure.coinSplit_append hex₀.1 hcs, hm₀'⟩,
          fun hok => ?_⟩
        have hok_true : ok (callStarts σ_pre).length = true := by simpa using hok
        have hok_acc : ok (callStarts τ_acc).length = true := by
          rwa [coinSplit_callStarts_eq hex₀.1]
        obtain ⟨ms_opk_cl, bh_cl, g_cl, -, -, hσ_lt, hc_cl⟩ :=
          IniPure.ini_clean_initOk interp' hext' r hr who ok g₀ ms₀ τ_acc
            (bundleBlob pb) ds hcl₀ hwho_acc hok_acc hhon hbin
        have hc_cl' : Clean interp' r S who ok g_cl
            (Sanitize.sanitizeMoves (setupTrace r) ms₀ ++
              (ms_opk_cl ++ [.aliceStart r.alice r.bob 4 6 bh_cl 35]))
            (τ_acc ++ blk_hw) := by
          simpa only [List.append_assoc] using hc_cl
        have hds_lens : ds.map List.length = initiateFullDrawLengths :=
          IniPure.initiateDrawsOfCoins_lengths hcoins
        have hds_len : ds.length = 34 := Slots.initiateDrawsOfCoins_length c.coins
        have hds0 : ds[0]?.map List.length = some 32 := by
          rw [← List.getElem?_map, hds_lens]; decide
        have hds33 : ds[33]?.map List.length = some 32 := by
          rw [← List.getElem?_map, hds_lens]; decide
        have ⟨hex_out, hnrc_out⟩ :=
          hGood hex₀ hcs (.callInit34 hds_len hds0 hds33 hok_acc)
            (Or.inr rfl) (fun ts hts sz => hσ_lt ts sz hts) hc_cl'
        refine ⟨?_, ⟨τ_acc ++ blk_hw, g_cl, _, hex_out, hnrc_out⟩,
          fun τ' ⟨g', ms', hex', hnrc'⟩ => ?_⟩
        · change NoAdjRng (σ_pre ++ (cliEntryEvents c ++ cliExitEvents c 0 []))
          rw [hent_eq]; exact noAdjRng_append_recv_rng hlive.noAdjRng
        · have hex'_ent : ExplainsCli interp' r S who ok
              (σ_pre ++ [.recv (bundleBlob pb), .rng c.coins]) τ' g' ms' := by
            simpa only [hent_eq] using hex'
          obtain ⟨τ'_pre, blk', ms'_pre, δ, rfl, rfl, hcs_pre, hcs_blk, hex'_pre, hnrc'_pre, hB_blk⟩ :=
            explainsCli_split_recv hex'_ent hnrc'
          obtain ⟨hrel_pre, hopk_pre⟩ := hlive.cutRel τ'_pre ⟨g', ms'_pre, hex'_pre, hnrc'_pre⟩
          have hcl'_pre : Clean interp' r S who ok g' ms'_pre τ'_pre :=
            explainsCli_toClean hex'_pre hnrc'_pre
          have hwho_pre : who[(callStarts τ'_pre).length]? = some r.alice := by
            rw [coinSplit_callStarts_eq hcs_pre, ← halice]; exact hwho
          have hok_pre : ok (callStarts τ'_pre).length = true := by
            rwa [coinSplit_callStarts_eq hcs_pre]
          have hblk'_eq : blk' = blk_hw :=
            init_exit0_cut_eq hcoins hcs_blk hB_blk hex'_ent hnrc' hwho_pre hok_pre
          rw [hblk'_eq]
          obtain ⟨_, _, hcont⟩ :=
            IniPure.ini_ok_pure_step interp' hext' r hr S rfl who ok
              (t_clean.leakRecords r) t_clean.sent accepted (t_clean.opkUsed r) τ'_pre
              (bundleBlob pb) ds recState ⟨g', ms'_pre, hcl'_pre⟩ hrel_pre hopk_pre
              hwho_pre hhon hbin hV1
          obtain ⟨_, hrel', hopk'⟩ := hcont hok_pre
          refine ⟨?_, ?_⟩
          · rw [hleakRec, hsent]; exact hrel'
          · rw [hopk]; exact hopk'

/-- Combined cut-polymorphic continuation and `SlotInitWitness` for a CLI `init` step. -/
theorem slot_init_cli_ua
    (hGood : GoodExit0CutSpec)
    (hB : BridgeBQuietFailSpec)
    (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (hext : ExternContractsHoldCli interp) (hagree : ModelAgree interp P) (hr : ProtocolSetupWF r)
    {t t_clean : CliTurn} {c : CliCall} {i : Inputs}
    {code : Nat} {out : HwBytes} {files : DirectorySnapshot}
    {accepted : List HwBytes} {σ_pre : List MachineEvent}
    (hsim : PqTurnSim1A (interpOfParams interp P) P r t t_clean accepted)
    (halice : c.party = r.alice)
    (hcmd : c.cmd = .init (peerOf r r.alice) bundleDir)
    (hstdin : c.stdin = [])
    (hcoins : c.coins.length = initiateTapeLen)
    (hrec_none : t.records r r.alice = none)
    (hflat : BundleFilesFlat c.bundle)
    (hhon_files : HonestBundleFiles interp r c.bundle)
    (hin : InputsFor c (t.dirs c.party) i)
    (hRel : PqModelRel interp P i (some (.exited code out files))) :
    let interp' := interpOfParams interp P
    let S := compSemOf interp' r
    let blk_cli := cliEntryEvents c ++ cliExitEvents c code out
    ∃ (t_clean' : CliTurn) (accepted' : List HwBytes),
      PqTurnSim1A interp' P r (CliTurn.after t r c code out files) t_clean' accepted' ∧
      SlotInitWitness interp' r t_clean t_clean' c code out ∧
      ∀ (who : List Participant) (ok : Nat → Bool),
        who[(callStarts σ_pre).length]? = some c.party →
        CliLiveAtCli interp' r S who ok t_clean accepted σ_pre →
        ok (callStarts σ_pre).length = decide (code = 0) →
        CliLiveAtCli interp' r S who ok t_clean' accepted' (σ_pre ++ blk_cli) := by
  obtain ⟨t_clean', accepted', hsim', hwit, hpost⟩ :=
    slot_init_cli_strong hGood hB interp P r hext hagree hr
      (σ_pre := σ_pre) hsim halice hcmd hstdin hcoins hrec_none hflat hhon_files hin hRel
  exact ⟨t_clean', accepted', hsim', hwit, fun who ok hwho hlive hok =>
    (hpost who ok hwho hlive).2 hok⟩

end Symbolic.Swarm.Coinsplit.Lift.L07
