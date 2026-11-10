/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridgePt
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecHalf
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
public import Symbolic.BugInjection.Proofs.Common443.CliEventBridge
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp40
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoCloseFinal
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Decomp81
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe81
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81Enum
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoCloseFinal
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# CLI Bridge for `Cheval26WeakStateIdx1`

Decomposes the 7-call CLI trace of `Witnesses.Cheval26WeakStateIdx1Cli` at its pre-key receive
sites (`noBscCliAt_8_sub`, `noBscCliAt_16_sub`) and proves `spec_half_pinned`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent EnvEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs Symbolic.Proofs.Swarm.UA.ClassicalBridge Symbolic.BugInjection
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED.CompInv
open Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CliEventBridge
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.MacGuardGen
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.NoFull

def ev0 : RunEvent := { party := "alice", cmd := .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle", input := wireAt 0, coins := cliCoins0, exit := some (0, []) }
def ev1 : RunEvent := { party := "alice", cmd := .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩, input := ptAt 35, coins := rngAt 36, exit := some (0, sendAt 37) }
def ev2 : RunEvent := { party := "alice", cmd := .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩, input := ptAt 38, coins := cliCoins2, exit := some (0, wireAt 40) }
def ev3 : RunEvent := { party := "bob", cmd := .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩, input := wireAt 40, coins := rngAt 41, exit := some (0, acceptAt 42) }
def ev4 : RunEvent := { party := "alice", cmd := .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle", input := wireAt 43, coins := cliCoins4, exit := some (0, []) }
def ev5 : RunEvent := { party := "alice", cmd := .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩, input := ptAt 78, coins := rngAt 79, exit := some (0, sendAt 80) }
def ev6 : RunEvent := { party := "bob", cmd := .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩, input := wireAt 81, coins := rngAt 82, exit := some (0, acceptAt 83) }

def cliEvents : List CliEvent := [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4, .run ev5, .run ev6]
theorem cliEvents_eq : cliEvents = Witnesses.Cheval26WeakStateIdx1Cli.trace := rfl
theorem cliSetup_eq : Witnesses.Cheval26WeakStateIdx1.setup = Witnesses.Cheval26WeakStateIdx1Cli.setup := rfl
theorem cliEvents_breakFree : BreakFree cliEvents := breakFree_map_run [ev0, ev1, ev2, ev3, ev4, ev5, ev6]

theorem memoCollisionOn_mono_prefixTerms {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop} {tr : ExecTrace}
    {v₁ v₂ : List VisEntry} {newTerms newPts : List DY.Bytes}
    (hsub : ∀ u ∈ prefixTerms r tr v₁, u ∈ prefixTerms r tr v₂) (hpt : plaintextTerms v₂ = plaintextTerms v₁)
    (h : MemoCollisionOn interp r S g known tr v₁ newTerms newPts) :
    MemoCollisionOn interp r S g known tr v₂ newTerms newPts := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hne, hinj, h1, h2, hbytes⟩ := h
  refine ⟨x₁, hx₁, x₂, ?_, hne, hinj, by rwa [hpt], by rwa [hpt], hbytes⟩
  rcases List.mem_append.mp hx₂ with hpre | hnew
  · obtain ⟨u, hu, hxm⟩ := List.mem_flatMap.mp hpre
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨u, hsub u hu, hxm⟩)
  · exact List.mem_append_right _ hnew

theorem prefixTerms_sub_of_sendTerms_sub {r : ProtocolSetup} {tr : ExecTrace} {v₁ v₂ : List VisEntry}
    (hsend : ∀ u ∈ (v₁.filter (·.kind == .send)).flatMap (·.terms), u ∈ prefixTerms r tr v₂)
    (hpt : plaintextTerms v₂ = plaintextTerms v₁) :
    ∀ u ∈ prefixTerms r tr v₁, u ∈ prefixTerms r tr v₂ := by
  intro u hu; unfold prefixTerms principalTerms at hu
  rcases List.mem_append.mp hu with hpr | hpt_u
  · rcases List.mem_append.mp hpr with h1 | hst
    · rcases List.mem_append.mp h1 with hsnd | hsec
      · exact hsend u hsnd
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hsec))
    · exact List.mem_append_left _ (List.mem_append_right _ hst)
  · rw [← hpt] at hpt_u; exact List.mem_append_right _ hpt_u

theorem bobStartCollision_of_bobStartCollisionOn_sub {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ms' : List Move}
    {tr : ExecTrace} {vis : List VisEntry} {salts : List DY.Bytes} {p : PreKeyFields} {x : PreKeyRep}
    (htr : runTraceMoves r ms' = tr) (hsalts : honestSalts r ms' = salts)
    (hsend : ∀ u ∈ (vis.filter (·.kind == .send)).flatMap (·.terms),
      u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms'))
    (hpt : plaintextTerms (runVis r ms') = plaintextTerms vis)
    (h : BobSessionStartCollidesOrImplicitRejectsOn interp r S g tr vis salts p x) :
    BobStartCollision interp r S g ms' p x := by
  subst htr; subst hsalts; have hsub := prefixTerms_sub_of_sendTerms_sub hsend hpt
  unfold BobStartCollision BobSessionStartCollidesOrImplicitRejects
  unfold BobSessionStartCollidesOrImplicitRejectsOn at h; dsimp only at h ⊢
  cases hP : DY.Libsignal.TripleRatchet.parseTrSignalMsg x.msg with
  | none => rw [hP] at h; exact memoCollisionOn_mono_prefixTerms hsub hpt h
  | some msg => rw [hP] at h; exact h.imp (memoCollisionOn_mono_prefixTerms hsub hpt) id

theorem not_nextEventCollidesClassical_recv_preKey_sub {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {who : List Participant} {ok : Nat → Bool}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs₁ : List CliEvent} {ev : RunEvent}
    {peer : CryptoVerification.SignalSession.Address} {tag : BitVec 8} {body : HwBytes} {p : PreKeyFields}
    (hwf : ProtocolSetupWF r) (hsched : SchedFits (callsOf evs₁) who ok)
    (hex : ExplainsClassical interp r S g ss vis evs₁) (hnrc : ¬ ReadCollisionCliClassical interp r S g ss evs₁)
    (hcmd : ev.cmd = .recv peer) (hinp : ev.input = tag :: body)
    (htag : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) (hp : parsePreKeyWire (tag :: body) = some p)
    (hnkb : ¬ KnownBaseKeyOn interp S g (runTrace r ss) p) (hnkm : ¬ KyberMismatch interp r p)
    (hno_bsc : ∀ (τ : List MachineEvent) (ms : List Move),
      ExplainsCli interp r S who ok (flatEvents evs₁) τ g ms →
      ¬ ReadCollision interp r S g ms τ → CompSetupSecrecy.NoBrk r ms →
      runTraceMoves r ms = runTrace r ss → honestSalts r ms = honestSaltsOf r ss →
      prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis →
      plaintextTerms (runVis r ms) = plaintextTerms vis →
      ∃ (ms' : List Move) (x : PreKeyRep),
        runTraceMoves r ms' = runTrace r ss ∧ honestSalts r ms' = honestSaltsOf r ss ∧
        (∀ u ∈ (vis.filter (·.kind == .send)).flatMap (·.terms), u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms')) ∧
        plaintextTerms (runVis r ms') = plaintextTerms vis ∧
        x ∈ preKeyRepresentations interp r S g ms' (tag :: body) ∧ ¬ BobStartCollision interp r S g ms' p x) :
    ¬ NextEventCollidesClassical interp r S g ss vis evs₁ ev := by
  intro hcol; simp only [NextEventCollidesClassical, hcmd, hinp] at hcol
  rcases hcol.2 with ⟨htag_eq, _⟩ | ⟨p', hp', ⟨hkb, _⟩ | ⟨_, hpk⟩⟩
  · exact htag htag_eq
  · rw [hp] at hp'; cases Option.some.inj hp'; exact hnkb hkb
  · rw [hp] at hp'; cases Option.some.inj hp'
    rcases hpk.2 with hkm | hall
    · exact hnkm hkm
    · obtain ⟨τ, ms, hex_cli, hnrc_cli, hnb, htr, hsalts, hpre, hpt⟩ := xlate_inv_with_noBrk hwf hsched hex hnrc
      obtain ⟨ms', x, htr', hsalts', hsend', hpt', hx, hnbsc⟩ := hno_bsc τ ms hex_cli hnrc_cli hnb htr hsalts hpre hpt
      have hx_on : x ∈ preKeyRepresentationsOn interp r S g (runTrace r ss) (tag :: body) := by
        rwa [← Symbolic.Proofs.Swarm.UA.XlateSteps.preKeyRepresentations_eq htr']
      exact hnbsc (bobStartCollision_of_bobStartCollisionOn_sub htr' hsalts' hsend' hpt' (hall g ss vis hex hnrc x hx_on))

theorem received_two_length_le (tr : ExecTrace) (e c : Nat) : (received tr [e, c]).length ≤ 2 := by
  unfold received; exact List.length_filterMap_le _ [e, c]

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem cliTrace_take_8_eq : cliTrace.take 8 =
    [ .recv (wireAt 0), .rng cliCoins0, .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37),
      .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40) ] := rfl

theorem cliTrace_take_16_eq : cliTrace.take 16 =
    [ .recv (wireAt 0), .rng cliCoins0, .pt (ptAt 35), .rng (rngAt 36), .send (sendAt 37),
      .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40), .recv (wireAt 40), .rng (rngAt 41),
      .accept (acceptAt 42), .recv (wireAt 43), .rng cliCoins4, .pt (ptAt 78), .rng (rngAt 79), .send (sendAt 80) ] := rfl

theorem not_kyberMismatch_cli_8 {i : ExternInterpretation} {r : Records}
    (hfits : compFits Witnesses.Cheval26WeakStateIdx1.setup i r) :
    ∀ p, parsePreKeyWire (wireAt 40) = some p → ¬ KyberMismatch i r p := not_kyberMismatch_at (Or.inl rfl) hfits

theorem not_kyberMismatch_cli_16 {i : ExternInterpretation} {r : Records}
    (hfits : compFits Witnesses.Cheval26WeakStateIdx1.setup i r) :
    ∀ p, parsePreKeyWire (wireAt 81) = some p → ¬ KyberMismatch i r p := not_kyberMismatch_at (Or.inr rfl) hfits

theorem wireAt_40_head_ne_whisper : (wireAt 40).head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag :=
  recvAt_head_ne_whisper (Or.inl rfl)

theorem wireAt_81_head_ne_whisper : (wireAt 81).head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag :=
  recvAt_head_ne_whisper (Or.inr rfl)

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
theorem explainsCli_take8_cut {r : Records} {S : Sem} {τ₁ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 8) τ₁ g ms) :
    ∃ b1 b2 : List MachineEvent,
      CoinSplit (seg 35 3) b1 ∧ CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2 ∧ τ₁ = (seg 0 35 ++ b1) ++ b2 := by
  have halice : r.alice = "alice" := Symbolic.BugInjection.Proofs.Common443.CompFitsNames.compFits_alice hfits
  have ⟨hcs, hmp, hof, hrng⟩ := hex; rw [cliTrace_take_8_eq] at hcs
  obtain ⟨τ1, rfl, hcs1⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs
  obtain ⟨p0, τ2, hp0_ne, hp0_pref, rfl, hcs2⟩ := coinSplit_rng_cons hcs1
  obtain ⟨τ3, rfl, hcs3⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs2
  obtain ⟨p1, τ4, hp1_ne, hp1_pref, rfl, hcs4⟩ := coinSplit_rng_cons hcs3
  obtain ⟨τ5, rfl, hcs5⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs4
  obtain ⟨τ6, rfl, hcs6⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs5
  obtain ⟨p2, τ7, hp2_ne, hp2_pref, rfl, hcs7⟩ := coinSplit_rng_cons hcs6
  obtain ⟨τ8, rfl, hcs8⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs7; cases hcs8
  let b0 : List MachineEvent := .recv (wireAt 0) :: p0.map .rng
  let b1 : List MachineEvent := .pt (ptAt 35) :: (p1.map .rng ++ [.send (sendAt 37)])
  let b2 : List MachineEvent := .pt (ptAt 38) :: (p2.map .rng ++ [.send (wireAt 40)])
  have hcs_b0 : CoinSplit [.recv (wireAt 0), .rng cliCoins0] b0 := by simpa [b0] using CoinSplit.keep (fun _ h => by cases h) (.split hp0_ne hp0_pref .nil)
  have hcs_b1 : CoinSplit (seg 35 3) b1 := .keep (fun _ h => by cases h) (.split hp1_ne hp1_pref (.keep (fun _ h => by cases h) .nil))
  have hcs_b2 : CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2 := by
    have hp2_pref' : p2.flatten <+: WsIdx1CensusDefs.cliCoins2Fast := Eq.mp (by rw [cliCoins2_eq_fast]; rfl) hp2_pref
    exact .keep (fun _ h => by cases h) (.split hp2_ne hp2_pref' (.keep (fun _ h => by cases h) .nil))
  have hmp_assoc : DY.Libsignal.Composed.Refinement.MatchedPrefix SpecTop.compI0 r S
      Witnesses.Cheval26WeakStateIdx1.who g ms ((b0 ++ b1) ++ b2) := by simpa [b0, b1, b2, List.append_assoc] using hmp
  obtain ⟨ms₂, δ₂, hms₂_eq, hmp₂_comp, _⟩ := matchedPrefix_split hmp_assoc (by intro e he; simp [b2] at he; subst he; exact Or.inr rfl)
  obtain ⟨ms₁, δ₁, hms₁_eq, hmp₁_comp, _⟩ := matchedPrefix_split hmp₂_comp (by intro e he; simp [b1] at he; subst he; exact Or.inr rfl)
  have hmp₁_nil : DY.Libsignal.Composed.Refinement.MatchedPrefix SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who g ms₁ ([] ++ b0) := hmp₁_comp
  obtain ⟨ms₀, δ₀, hms₀_eq, hmp₀_comp, hfor₀⟩ := matchedPrefix_split hmp₁_nil (by intro e he; simp [b0] at he; subst he; exact Or.inl rfl)
  have hms_from_0 : ms = (ms₀ ++ δ₀) ++ (δ₁ ++ δ₂) := by simp [hms₂_eq, hms₁_eq, hms₀_eq, List.append_assoc]
  have hb0_eq : b0 = seg 0 35 := by
    have h := init_blk_cut_eq cliCoins0_length hcs_b0 ⟨hmp₀_comp, hms₀_eq ▸ hmp₁_comp.2.1, hfor₀⟩
      (hms₀_eq ▸ hmp₁_nil) (hms_from_0 ▸ hof) (hms_from_0 ▸ hrng) (by rw [halice]; rfl) rfl
    rw [init_draws_cliCoins0_eq] at h; exact h
  refine ⟨b1, b2, hcs_b1, hcs_b2, ?_⟩; simp [b0, b1, b2, List.append_assoc] at hb0_eq ⊢; rw [← hb0_eq]; rfl

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct in
theorem explainsCli_take16_cut {r : Records} {S : Sem} {τ₁ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hex : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who
      Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 16) τ₁ g ms) :
    ∃ b1 b2 b5 : List MachineEvent, CoinSplit (seg 35 3) b1 ∧ CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2 ∧
      CoinSplit (seg 78 3) b5 ∧ τ₁ = ((((seg 0 35 ++ b1) ++ b2) ++ seg 40 3) ++ seg 43 35) ++ b5 := by
  have halice : r.alice = "alice" := Symbolic.BugInjection.Proofs.Common443.CompFitsNames.compFits_alice hfits
  have ⟨hcs, hmp, hof, hrng⟩ := hex; rw [cliTrace_take_16_eq] at hcs
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
  obtain ⟨τ14, rfl, hcs14⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs13
  obtain ⟨p5, τ15, hp5_ne, hp5_pref, rfl, hcs15⟩ := coinSplit_rng_cons hcs14
  obtain ⟨τ16, rfl, hcs16⟩ := coinSplit_nonRng_cons (fun _ h => by cases h) hcs15; cases hcs16
  let b0 : List MachineEvent := .recv (wireAt 0) :: p0.map .rng
  let b1 : List MachineEvent := .pt (ptAt 35) :: (p1.map .rng ++ [.send (sendAt 37)])
  let b2 : List MachineEvent := .pt (ptAt 38) :: (p2.map .rng ++ [.send (wireAt 40)])
  let b3 : List MachineEvent := .recv (wireAt 40) :: p3.map .rng ++ [.accept (acceptAt 42)]
  let b4 : List MachineEvent := .recv (wireAt 43) :: p4.map .rng
  let b5 : List MachineEvent := .pt (ptAt 78) :: (p5.map .rng ++ [.send (sendAt 80)])
  have hmp_assoc : DY.Libsignal.Composed.Refinement.MatchedPrefix SpecTop.compI0 r S
      Witnesses.Cheval26WeakStateIdx1.who g ms (((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5) := by simpa [b0, b1, b2, b3, b4, b5, List.append_assoc] using hmp
  obtain ⟨ms₅, δ₅, hms₅_eq, hmp₅_comp, _⟩ := matchedPrefix_split hmp_assoc (by intro e he; simp [b5] at he; subst he; exact Or.inr rfl)
  obtain ⟨ms₄, δ₄, hms₄_eq, hmp₄_comp, hfor₄⟩ := matchedPrefix_split hmp₅_comp (by intro e he; simp [b4] at he; subst he; exact Or.inl rfl)
  obtain ⟨ms₃, δ₃, hms₃_eq, hmp₃_comp, hfor₃⟩ := matchedPrefix_split hmp₄_comp (by intro e he; simp [b3] at he; subst he; exact Or.inl rfl)
  obtain ⟨ms₂, δ₂, hms₂_eq, hmp₂_comp, hfor₂⟩ := matchedPrefix_split hmp₃_comp (by intro e he; simp [b2] at he; subst he; exact Or.inr rfl)
  obtain ⟨ms₁, δ₁, hms₁_eq, hmp₁_comp, hfor₁⟩ := matchedPrefix_split hmp₂_comp (by intro e he; simp [b1] at he; subst he; exact Or.inr rfl)
  have hmp₁_nil : DY.Libsignal.Composed.Refinement.MatchedPrefix SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who g ms₁ ([] ++ b0) := hmp₁_comp
  obtain ⟨ms₀, δ₀, hms₀_eq, hmp₀_comp, hfor₀⟩ := matchedPrefix_split hmp₁_nil (by intro e he; simp [b0] at he; subst he; exact Or.inl rfl)
  have hcs_b0 : CoinSplit [.recv (wireAt 0), .rng cliCoins0] b0 := by simpa [b0] using CoinSplit.keep (fun _ h => by cases h) (.split hp0_ne hp0_pref .nil)
  have hcs_b1 : CoinSplit (seg 35 3) b1 := .keep (fun _ h => by cases h) (.split hp1_ne hp1_pref (.keep (fun _ h => by cases h) .nil))
  have hcs_b2 : CoinSplit WsIdx1CensusDefs.seg38SplitSrc b2 := by
    have hp2_pref' : p2.flatten <+: WsIdx1CensusDefs.cliCoins2Fast := Eq.mp (by rw [cliCoins2_eq_fast]; rfl) hp2_pref
    exact .keep (fun _ h => by cases h) (.split hp2_ne hp2_pref' (.keep (fun _ h => by cases h) .nil))
  have hcs_b3 : CoinSplit [.recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] b3 := .keep (fun _ h => by cases h) (.split hp3_ne hp3_pref (.keep (fun _ h => by cases h) .nil))
  have hcs_b4 : CoinSplit [.recv (wireAt 43), .rng cliCoins4] b4 := by simpa [b4] using CoinSplit.keep (fun _ h => by cases h) (.split hp4_ne hp4_pref .nil)
  have hcs_b5 : CoinSplit (seg 78 3) b5 := .keep (fun _ h => by cases h) (.split hp5_ne hp5_pref (.keep (fun _ h => by cases h) .nil))
  have hcs_pre4 : CoinSplit (cliTrace.take 11) (((b0 ++ b1) ++ b2) ++ b3) := by
    have htake11 : cliTrace.take 11 = [.recv (wireAt 0), .rng cliCoins0, .pt (ptAt 35), .rng (rngAt 36),
        .send (sendAt 37), .pt (ptAt 38), .rng cliCoins2, .send (wireAt 40), .recv (wireAt 40), .rng (rngAt 41), .accept (acceptAt 42)] := rfl
    rw [htake11]; simpa [b0, b1, b2, b3, List.append_assoc] using CoinSplit.keep (fun _ h => by cases h) (.split hp0_ne hp0_pref
      (.keep (fun _ h => by cases h) (.split hp1_ne hp1_pref (.keep (fun _ h => by cases h) (.keep (fun _ h => by cases h)
        (.split hp2_ne hp2_pref (.keep (fun _ h => by cases h) (.keep (fun _ h => by cases h)
          (.split hp3_ne hp3_pref (.keep (fun _ h => by cases h) .nil))))))))))
  have hms_from_0 : ms = (ms₀ ++ δ₀) ++ (δ₁ ++ δ₂ ++ δ₃ ++ δ₄ ++ δ₅) := by simp [hms₅_eq, hms₄_eq, hms₃_eq, hms₂_eq, hms₁_eq, hms₀_eq, List.append_assoc]
  have hb0_eq : b0 = seg 0 35 := by
    have h := init_blk_cut_eq cliCoins0_length hcs_b0 ⟨hmp₀_comp, hms₀_eq ▸ hmp₁_comp.2.1, hfor₀⟩
      (hms₀_eq ▸ hmp₁_nil) (hms_from_0 ▸ hof) (hms_from_0 ▸ hrng) (by rw [halice]; rfl) rfl
    rw [init_draws_cliCoins0_eq] at h; exact h
  have hcc_pre4 : (callStarts (((b0 ++ b1) ++ b2) ++ b3)).length = 4 := by rw [coinSplit_callStarts_eq hcs_pre4]; rfl
  have hms_from_4 : ms = (ms₄ ++ δ₄) ++ δ₅ := by simp [hms₅_eq, hms₄_eq]
  have hb4_eq : b4 = seg 43 35 := by
    have h := init_blk_cut_eq cliCoins4_length hcs_b4 ⟨hmp₄_comp, hms₄_eq ▸ hmp₅_comp.2.1, hfor₄⟩
      (hms₄_eq ▸ hmp₅_comp) (hms_from_4 ▸ hof) (hms_from_4 ▸ hrng) (by rw [hcc_pre4, halice]; rfl) (by rw [hcc_pre4]; rfl)
    rw [init_draws_cliCoins4_eq] at h; exact h
  obtain ⟨p40, hp40⟩ := wireAt40_parses
  have hb0_bd : AllBobDone (fun _ => False) (runTraceMoves r ms₁) := by
    rw [hms₀_eq]; exact allBobDone_xplBlock_ini ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₀_comp, hms₀_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₁_comp).2.1, hfor₀⟩
      map_rng_kind_local (allBobDone_matchedPrefix_nil (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₀_comp))
  have hb1_bd : AllBobDone (fun _ => False) (runTraceMoves r ms₂) := by
    rw [hms₁_eq]; exact allBobDone_xplBlock_send ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₁_comp, hms₁_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₂_comp).2.1, hfor₁⟩ map_rng_snoc_send_kind_local hb0_bd
  have hb2_bd : AllBobDone (fun _ => False) (runTraceMoves r ms₃) := by
    rw [hms₂_eq]; exact allBobDone_xplBlock_send ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₂_comp, hms₂_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₃_comp).2.1, hfor₂⟩ map_rng_snoc_send_kind_local hb1_bd
  have hnk40 : ¬ KnownBaseKey SpecTop.compI0 r S g ms₃ p40 := not_knownBaseKey_of_allBobDone_false hb2_bd
  have hms_from_3 : ms = (ms₃ ++ δ₃) ++ (δ₄ ++ δ₅) := by simp [hms₅_eq, hms₄_eq, hms₃_eq, List.append_assoc]
  have hb3_eq : b3 = seg 40 3 :=
    rpk_blk_cut_eq PtPrefixInv78b.rngAt41_length hcs_b3 wireAt40_head? hp40 hnk40
      ⟨Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₃_comp, hms₃_eq ▸ (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hmp₄_comp).2.1, hfor₃⟩ (hms_from_3 ▸ hrng)
  refine ⟨b1, b2, b5, hcs_b1, hcs_b2, hcs_b5, ?_⟩
  rw [← hb0_eq, ← hb3_eq, ← hb4_eq]; simp [b0, b1, b2, b3, b4, b5, List.append_assoc]

theorem runTraceMoves_encrypt_swap {r : Records} {P Q : List Move} {me : Participant}
    {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} :
    runTraceMoves r (P ++ .encrypt me s cl pq w₂ :: Q) = runTraceMoves r (P ++ .encrypt me s cl pq w₁ :: Q) := by
  have hk : (P ++ Move.encrypt me s cl pq w₁ :: Q)[P.length]? = some (.encrypt me s cl pq w₁) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hset : (P ++ Move.encrypt me s cl pq w₁ :: Q).set P.length (.encrypt me s cl pq w₂) =
      P ++ Move.encrypt me s cl pq w₂ :: Q := by
    rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]; rfl
  rw [← hset]; exact WsIdx1DecompSwap.runTrace_set_wrap hk

theorem honestKeysFrom_encrypt_swap :
    ∀ (P : List Move) (tr : ExecTrace) (Q : List Move) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)),
      honestKeysFrom tr (P ++ .encrypt me s cl pq w₂ :: Q) = honestKeysFrom tr (P ++ .encrypt me s cl pq w₁ :: Q)
  | [], _, _, _, _, _, _, _, _ => rfl
  | m :: P, tr, Q, me, s, cl, pq, w₁, w₂ => by
    simp only [List.cons_append, honestKeysFrom]
    rw [honestKeysFrom_encrypt_swap P (m.next tr) Q me s cl pq w₁ w₂]

theorem honestSalts_encrypt_swap {r : Records} {P Q : List Move} {me : Participant}
    {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} :
    honestSalts r (P ++ .encrypt me s cl pq w₂ :: Q) = honestSalts r (P ++ .encrypt me s cl pq w₁ :: Q) := by
  unfold honestSalts; congr 1; exact honestKeysFrom_encrypt_swap P (r.setupMove.next Trace.nil) Q me s cl pq w₁ w₂

theorem encSend_filter_pt (tr tr' : ExecTrace) (w : Option (Nat × Nat)) :
    (encSend tr tr' w).filter (·.kind == .pt) = [] := by
  unfold encSend; cases lastSent tr tr' <;> cases w <;> rfl

theorem encrypt_vis_filter_pt_wrap (tr : ExecTrace) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) :
    ((Move.encrypt me s cl pq w₂).vis tr).filter (·.kind == .pt) =
      ((Move.encrypt me s cl pq w₁).vis tr).filter (·.kind == .pt) := by
  simp only [Move.vis, WsIdx1DecompSwap.encrypt_next_eq_wrap tr me s cl pq w₂ w₁,
    encVis, ↓reduceIte, List.filter_append, encSend_filter_pt]

theorem runMoves_snd_filter_pt_encrypt_swap :
    ∀ (P : List Move) (tr : ExecTrace) (Q : List Move) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)),
      ((runMoves (P ++ .encrypt me s cl pq w₂ :: Q) tr).2).filter (·.kind == .pt) =
        ((runMoves (P ++ .encrypt me s cl pq w₁ :: Q) tr).2).filter (·.kind == .pt)
  | [], tr, Q, me, s, cl, pq, w₁, w₂ => by
    simp only [List.nil_append, runMoves, WsIdx1DecompSwap.encrypt_next_eq_wrap tr me s cl pq w₂ w₁,
      List.filter_append, encrypt_vis_filter_pt_wrap tr me s cl pq w₁ w₂]
  | m :: P, tr, Q, me, s, cl, pq, w₁, w₂ => by
    simp only [List.cons_append, runMoves, List.filter_append]
    rw [runMoves_snd_filter_pt_encrypt_swap P (m.next tr) Q me s cl pq w₁ w₂]

theorem plaintextTerms_runVis_encrypt_swap {r : Records} {P Q : List Move} {me : Participant}
    {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} :
    plaintextTerms (runVis r (P ++ .encrypt me s cl pq w₂ :: Q)) =
      plaintextTerms (runVis r (P ++ .encrypt me s cl pq w₁ :: Q)) := by
  unfold plaintextTerms runVis; simp only [runMoves, List.filter_append]
  rw [runMoves_snd_filter_pt_encrypt_swap P (r.setupMove.next Trace.nil) Q me s cl pq w₁ w₂]

open DY.Libsignal.TripleRatchet (parseTrSignalMsg)

theorem list_eq_seven_splits {α : Type} {a0 a1 a2 a3 a4 a5 a6 x : α} {xs ys : List α}
    (h : [a0, a1, a2, a3, a4, a5, a6] = xs ++ x :: ys) :
    (xs = [] ∧ x = a0 ∧ ys = [a1, a2, a3, a4, a5, a6]) ∨
    (xs = [a0] ∧ x = a1 ∧ ys = [a2, a3, a4, a5, a6]) ∨
    (xs = [a0, a1] ∧ x = a2 ∧ ys = [a3, a4, a5, a6]) ∨
    (xs = [a0, a1, a2] ∧ x = a3 ∧ ys = [a4, a5, a6]) ∨
    (xs = [a0, a1, a2, a3] ∧ x = a4 ∧ ys = [a5, a6]) ∨
    (xs = [a0, a1, a2, a3, a4] ∧ x = a5 ∧ ys = [a6]) ∨
    (xs = [a0, a1, a2, a3, a4, a5] ∧ x = a6 ∧ ys = []) := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, xs⟩⟩⟩⟩⟩⟩⟩ <;> simp at h
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))

theorem callsOf_cliEvents : callsOf cliEvents =
    [("alice", true), ("alice", true), ("alice", true), ("bob", true),
     ("alice", true), ("alice", true), ("bob", true)] := rfl

set_option linter.unnecessarySeqFocus false in
theorem schedFits_cliEvents : SchedFits (callsOf cliEvents)
    Witnesses.Cheval26WeakStateIdx1.who Witnesses.Cheval26WeakStateIdx1.ok := by
  rw [callsOf_cliEvents]; refine ⟨by decide, fun k p b hget => ?_⟩
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

theorem invisible_prefix_eq_of_party_local :
    ∀ {pre₁ pre₂ rest₁ rest₂ : List Step} {s₁ s₂ : Step},
      (∀ x ∈ pre₁, x.cls = .invisible) → (∀ x ∈ pre₂, x.cls = .invisible) →
      s₁.cls ≠ .invisible → s₂.cls ≠ .invisible →
      pre₁ ++ s₁ :: rest₁ = pre₂ ++ s₂ :: rest₂ → pre₁ = pre₂ ∧ s₁ = s₂ ∧ rest₁ = rest₂
  | [], [], _, _, _, _, _, _, _, _, h => ⟨rfl, (List.cons.inj h).1, (List.cons.inj h).2⟩
  | x :: _, [], _, _, _, _, h₁, _, _, hs₂, h => False.elim (hs₂ ((List.cons.inj h).1 ▸ h₁ x List.mem_cons_self))
  | [], y :: _, _, _, _, _, _, h₂, hs₁, _, h => False.elim (hs₁ ((List.cons.inj h).1.symm ▸ h₂ y List.mem_cons_self))
  | x :: pre₁, _ :: _, _, _, _, _, h₁, h₂, hs₁, hs₂, h => by
    obtain ⟨rfl, htail⟩ := List.cons.inj h
    obtain ⟨hp, hs, hr⟩ := invisible_prefix_eq_of_party_local
      (fun z hz => h₁ z (List.mem_cons_of_mem _ hz)) (fun z hz => h₂ z (List.mem_cons_of_mem _ hz)) hs₁ hs₂ htail
    exact ⟨congrArg (x :: ·) hp, hs, hr⟩

theorem runSteps_append_local (pre ss : List Step) (tr : ExecTrace) :
    runSteps (pre ++ ss) tr = runSteps ss (runSteps pre tr) := by
  induction pre generalizing tr with | nil => rfl | cons s pre ih => exact ih (s.next tr)

theorem stepsWF_of_append_local : ∀ {a b : List Step} {tr : ExecTrace}, StepsWF (a ++ b) tr → StepsWF a tr
  | [], _, _, _ => trivial
  | _ :: _, _, _, h => ⟨h.1, h.2.1, stepsWF_of_append_local h.2.2⟩

theorem stepsStateFaithful_of_append_local {r : ProtocolSetup} {a b : List Step}
    (h : StepsStateFaithful r (a ++ b)) : StepsStateFaithful r a := by
  intro i j si sj p k bb hij hi hj hload hok hload'
  have hilt : i < a.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjlt : j < a.length := (List.getElem?_eq_some_iff.mp hj).1
  refine h i j si sj p k bb hij (by rw [List.getElem?_append_left hilt]; exact hi)
    (by rw [List.getElem?_append_left hjlt]; exact hj) hload ?_ hload'
  rw [List.take_append_of_le_length (Nat.le_of_lt hilt)]; exact hok

theorem modelRunWF_of_append_local {r : ProtocolSetup} {a b : List Step}
    (h : ModelRunWF r (a ++ b)) : ModelRunWF r a :=
  ⟨h.1, h.2.1, stepsWF_of_append_local h.2.2.1, stepsStateFaithful_of_append_local h.2.2.2⟩

theorem matchesEventsClassical_prepend_invisible_local {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {pre : List Step}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsClassicalAt interp r S g initIds (runSteps pre tr) ss evs vis →
      MatchesEventsClassicalAt interp r S g initIds tr (pre ++ ss) evs vis
  | _, _, _, _, _, .nil h => .nil fun x hx => (List.mem_append.mp hx).elim (hinv x) (h x)
  | _, _, _, _, _, .run1 (pre := pre') hp hrm hrest => by
    have hp' : ∀ x ∈ pre ++ pre', x.cls = .invisible := fun x hx => (List.mem_append.mp hx).elim (hinv x) (hp x)
    rw [← runSteps_append_local] at hrm hrest; simpa [List.append_assoc] using MatchesEventsClassicalAt.run1 hp' hrm hrest
  | _, _, _, _, _, .run0 (pre := pre') hp hrej hrest => by
    have hp' : ∀ x ∈ pre ++ pre', x.cls = .invisible := fun x hx => (List.mem_append.mp hx).elim (hinv x) (hp x)
    rw [← runSteps_append_local] at hrest; simpa [List.append_assoc] using MatchesEventsClassicalAt.run0 hp' hrej hrest
  | _, _, _, _, _, .env (pre := pre') hp hem hrest => by
    have hp' : ∀ x ∈ pre ++ pre', x.cls = .invisible := fun x hx => (List.mem_append.mp hx).elim (hinv x) (hp x)
    rw [← runSteps_append_local] at hem hrest; simpa [List.append_assoc] using MatchesEventsClassicalAt.env hp' hem hrest

theorem matchesEventsClassical_split_party_sub {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ (evs₁ : List CliEvent) {initIds : Option BundlePreKeyIds} {tr₀ : ExecTrace} {ss₁ : List Step} {vis₁ : List VisEntry}
      {m : Step} {ss₂ : List Step} {ev : RunEvent} {evs₂ : List CliEvent} {vis : List VisEntry} {out : HwBytes},
      MatchesEventsClassicalAt interp r S g initIds tr₀ ss₁ evs₁ vis₁ → m.cls = .party → ev.exit = some (0, out) →
      MatchesEventsClassicalAt interp r S g initIds tr₀ (ss₁ ++ m :: ss₂) (evs₁ ++ .run ev :: evs₂) vis →
      (∀ ve ∈ vis₁, ve ∈ vis) ∧ ∃ v ids, RunMatches interp r S g (runSteps ss₁ tr₀) m ev v ids
  | [], _, _, ss₁, _, m, ss₂, _, _, _, out, .nil hinv₁, hm_cls, hexit, hme => by
    simp only [List.nil_append] at hme; generalize hss : ss₁ ++ m :: ss₂ = ss_tot at hme
    cases hme with
    | run0 _ hrej => exact False.elim (hrej out hexit)
    | @run1 _ _ pre₂ s _ _ _ v _ hinv₂ hrm _ =>
      have hm_ne : m.cls ≠ .invisible := by rw [hm_cls]; decide
      have hs_ne : s.cls ≠ .invisible := by rw [hrm.1]; decide
      obtain ⟨rfl, rfl, rfl⟩ := invisible_prefix_eq_of_party_local hinv₁ hinv₂ hm_ne hs_ne (by simpa [List.append_assoc] using hss)
      exact ⟨(fun _ h => nomatch h), v, _, hrm⟩
  | _ :: evs₁, _, _, ss₁, _, m, ss₂, _, _, _, out, hme₁, hm_cls, hexit, hme => by
    simp only [List.cons_append] at hme; generalize hss : ss₁ ++ m :: ss₂ = ss_tot at hme
    cases hme₁ with
    | @run0 _ _ _ _ _ _ _ hinv₁ hrej₁ hme_rem₁ =>
      cases hme with
      | run1 _ hrm₂ _ => obtain ⟨out₀, hexit₀⟩ := hrm₂.2.2.2.2.2.1; exact False.elim (hrej₁ out₀ hexit₀)
      | @run0 _ _ _ _ _ _ _ hinv₂ _ hme_rem₂ =>
        have h₁ := matchesEventsClassical_prepend_invisible_local hinv₁ hme_rem₁
        have h₂ := matchesEventsClassical_prepend_invisible_local hinv₂ hme_rem₂
        rw [← hss] at h₂; exact matchesEventsClassical_split_party_sub evs₁ h₁ hm_cls hexit h₂
    | @run1 _ _ _ s₁ _ _ _ v₁ vs₁ hinv₁ hrm₁ hme_rem₁ =>
      cases hme with
      | run0 _ hrej₂ _ => obtain ⟨out₀, hexit₀⟩ := hrm₁.2.2.2.2.2.1; exact False.elim (hrej₂ out₀ hexit₀)
      | @run1 _ _ _ s₂ _ _ _ v₂ vs₂ hinv₂ hrm₂ hme_rem₂ =>
        have hs₁_ne : s₁.cls ≠ .invisible := by rw [hrm₁.1]; decide
        have hs₂_ne : s₂.cls ≠ .invisible := by rw [hrm₂.1]; decide
        obtain ⟨rfl, rfl, rfl⟩ := invisible_prefix_eq_of_party_local hinv₁ hinv₂ hs₁_ne hs₂_ne (by simpa [List.append_assoc] using hss)
        have hv_eq : v₁ = v₂ := hrm₁.2.2.2.2.2.2.1.trans hrm₂.2.2.2.2.2.2.1.symm
        subst hv_eq; rw [runSteps_append_local, runSteps]
        obtain ⟨hsub, hrm_out⟩ := matchesEventsClassical_split_party_sub evs₁ hme_rem₁ hm_cls hexit hme_rem₂
        exact ⟨fun ve hve => (List.mem_append.mp hve).elim (List.mem_append_left _) (fun h => List.mem_append_right _ (hsub ve h)), hrm_out⟩
    | @env _ _ _ s₁ _ ev₀ _ v₁ vs₁ hinv₁ hem₁ hme_rem₁ =>
      cases hme with
      | @env _ _ _ s₂ _ _ _ v₂ vs₂ hinv₂ hem₂ hme_rem₂ =>
        have hs₁_ne : s₁.cls ≠ .invisible := by
          have hcls : s₁.cls = .env := by cases ev₀ <;> first | exact False.elim hem₁ | exact hem₁.1
          rw [hcls]; decide
        have hs₂_ne : s₂.cls ≠ .invisible := by
          have hcls : s₂.cls = .env := by cases ev₀ <;> first | exact False.elim hem₂ | exact hem₂.1
          rw [hcls]; decide
        obtain ⟨rfl, rfl, rfl⟩ := invisible_prefix_eq_of_party_local hinv₁ hinv₂ hs₁_ne hs₂_ne (by simpa [List.append_assoc] using hss)
        have hv_eq : v₁ = v₂ := by cases ev₀ <;> first | exact False.elim hem₁ | exact hem₁.2.2.2.1.trans hem₂.2.2.2.1.symm
        subst hv_eq; rw [runSteps_append_local, runSteps]
        obtain ⟨hsub, hrm_out⟩ := matchesEventsClassical_split_party_sub evs₁ hme_rem₁ hm_cls hexit hme_rem₂
        exact ⟨fun ve hve => (List.mem_append.mp hve).elim (List.mem_append_left _) (fun h => List.mem_append_right _ (hsub ve h)), hrm_out⟩

theorem not_readCollisionCliClassical_of_not_knownBaseKeyOn
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hex : ExplainsClassical interp r S g ss vis evs)
    (hrecv : ∀ evs₁ ev evs₂ out, evs = evs₁ ++ .run ev :: evs₂ → (∃ peer, ev.cmd = .recv peer) →
      ev.exit = some (0, out) → ∃ p, parsePreKeyWire ev.input = some p ∧
        ∀ ss₁ vis₁, ExplainsClassical interp r S g ss₁ vis₁ evs₁ → ¬ KnownBaseKeyOn interp S g (runTrace r ss₁) p) :
    ¬ ReadCollisionCliClassical interp r S g ss evs := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, body, w, hevs, hss, hcmd, hexit, _, hme₁, hdec, _, _⟩
  have hm_cls : m.cls = StepClass.party := by cases m <;> simp [Step.decryptMsgIdx?] at hdec <;> rfl
  have hme' : MatchesEventsClassical interp r S g (setupTrace r) (ss₁ ++ m :: ss₂) (evs₁ ++ .run ev :: evs₂) vis := by
    rw [← hss, ← hevs]; exact hex.2.2.2
  obtain ⟨hsub, v, _, hrm⟩ := matchesEventsClassical_split_party_sub evs₁ hme₁ hm_cls hexit hme'
  have hex₁ : ExplainsClassical interp r S g ss₁ vis₁ evs₁ :=
    ⟨hex.1, ⟨fun ve hve => hex.2.1.1 ve (hsub ve hve), hex.2.1.2.1, fun ve hve => hex.2.1.2.2 ve (hsub ve hve)⟩,
      modelRunWF_of_append_local (hss ▸ hex.2.2.1), hme₁⟩
  obtain ⟨p, hp, hnkb⟩ := hrecv evs₁ ev evs₂ out hevs hcmd hexit
  obtain ⟨_, _, _, _, _, _, _, _, hpf_all⟩ := hrm.2.2.2.2.2.2.2
  have hpf_p := hpf_all p hp
  cases m <;> simp [Step.decryptMsgIdx?] at hdec <;>
    (obtain ⟨ek, hek, heq⟩ := hpf_p; exact hnkb ss₁ vis₁ hex₁ ⟨ek, hek, heq.symm⟩)

theorem step_le_next_local (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

theorem runSteps_le_local : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => DY.Trace.le_refl tr
  | s :: ss, tr => DY.Trace.le_trans _ _ _ (step_le_next_local s tr) (runSteps_le_local ss (s.next tr))

theorem matchesEventsClassical_nil_vis_local {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (h : MatchesEventsClassicalAt interp r S g initIds tr ss [] vis) : vis = [] := by cases h; rfl

theorem matchesEventsClassical_run_exit0_inv_local {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {vis : List VisEntry} {out : HwBytes}
    (hexit : ev.exit = some (0, out)) (h : MatchesEventsClassicalAt interp r S g initIds tr ss (.run ev :: evs) vis) :
    ∃ pre s ss' v vs, ss = pre ++ s :: ss' ∧ vis = v ++ vs ∧
      RunMatches interp r S g (runSteps pre tr) s ev v initIds ∧
      MatchesEventsClassicalAt interp r S g (nextBundleIds initIds ev) (s.next (runSteps pre tr)) ss' evs vs := by
  cases h with
  | run0 _ hrej _ => exact False.elim (hrej out hexit)
  | run1 _ hrm hmev => exact ⟨_, _, _, _, _, rfl, rfl, hrm, hmev⟩

open Symbolic.Swarm.COMPOSED.CompTrace in
theorem exists_aliceDone_of_pendingPreKey_local {tr₀ tr : ExecTrace} {stateIdx : Nat}
    {ek ct : DY.Bytes} (hle : tr₀ ≤ tr) (hppk : pendingPreKey tr₀ stateIdx = some (ek, ct)) :
    ∃ d a b ikA ikB spk pqpk opk keys,
      tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a b ikA ikB spk pqpk opk ek ct keys) d := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt at hppk
  cases hat_st : (tr₀.at? stateIdx :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState))) with
  | none => rw [hat_st] at hppk; cases hppk
  | some e =>
    rw [hat_st] at hppk
    dsimp only [Option.map, Option.bind] at hppk
    split at hppk
    · cases hppk
    · rw [List.findSome?_eq_some_iff] at hppk
      obtain ⟨_, ev, _, heq_evs, hmatch, _⟩ := hppk
      have hev_mem : ev ∈ DY.Libsignal.Composed.Refinement.sessionHandshakeEvents tr₀
          (e.st.state.sessionInfo e.st.participant) := by
        rw [heq_evs]; simp
      unfold DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hev_mem
      obtain ⟨i, _, hev⟩ := List.mem_filterMap.mp hev_mem
      (split at hev <;> try simp at hev); rename_i s d hcev; obtain ⟨_, hev⟩ := hev
      cases ev <;> simp at hmatch
      rename_i a b ikA ikB spk pqpk opk ek' ct' keys; obtain ⟨rfl, rfl⟩ := hmatch
      have hat₀ : (tr₀.at? d : Option PQXDHEntry) =
          some ⟨.AliceDone a b ikA ikB spk pqpk opk ek' ct' keys⟩ := by
        rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
        rcases hat : (tr₀.at? d : Option PQXDHEntry) with _ | ⟨ev'⟩ <;> rw [hat] at hev
        · cases hev
        · injection hev with hev'; rw [← hev']
      exact ⟨d, a, b, ikA, ikB, spk, pqpk, opk, keys,
        (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_iff_at?
          DY.Libsignal.PQXDH.PQXDHEvent _ _ _).mpr (at?_le_some hle hat₀)⟩

theorem runWrapped_ev1 : runWrapped ev1 = true := by
  unfold runWrapped ev1; dsimp only; rw [PtPrefixInv38.sendAt37_eq_fast, PtPrefixInv38.wire37Fast_head?]; rfl
theorem runWrapped_ev2 : runWrapped ev2 = true := by unfold runWrapped ev2; dsimp only; rw [wireAt40_head?]; rfl
theorem runWrapped_ev5 : runWrapped ev5 = true := by unfold runWrapped ev5; dsimp only; rw [sendAt80_head?]; rfl

theorem matchesEventsClassical_take8_sendTerms
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hmev : MatchesEventsClassical SpecTop.compI0 r S g (setupTrace r) ss [.run ev0, .run ev1, .run ev2] vis) :
    ∃ tr₁ idx₁ ek₁ ct₁ m₁ tr₂ idx₂ ek₂ ct₂ m₂,
      tr₁ ≤ runTrace r ss ∧ pendingPreKey tr₁ idx₁ = some (ek₁, ct₁) ∧
      tr₂ ≤ runTrace r ss ∧ pendingPreKey tr₂ idx₂ = some (ek₂, ct₂) ∧
      (vis.filter (·.kind == .send)).flatMap (·.terms) = [ek₁, ct₁, m₁, ek₂, ct₂, m₂] := by
  obtain ⟨pre₀, s₀, ss₁, v₀, vs₁, rfl, rfl, hrm₀, hmev₁⟩ := matchesEventsClassical_run_exit0_inv_local (out := []) rfl hmev
  obtain ⟨pre₁, s₁, ss₂, v₁, vs₂, rfl, rfl, hrm₁, hmev₂⟩ := matchesEventsClassical_run_exit0_inv_local (out := sendAt 37) rfl hmev₁
  obtain ⟨pre₂, s₂, ss₃, v₂, vs₃, rfl, rfl, hrm₂, hmev₃⟩ := matchesEventsClassical_run_exit0_inv_local (out := wireAt 40) rfl hmev₂
  cases matchesEventsClassical_nil_vis_local hmev₃
  have hv₀ := runMatches_filter_send_init rfl hrm₀
  obtain ⟨idx₁, _, _, m₁, _, _, hwrap₁, _⟩ := runMatches_filter_send_send rfl hrm₁
  obtain ⟨ek₁, ct₁, hppk₁, hv₁⟩ := hwrap₁ runWrapped_ev1
  obtain ⟨idx₂, _, _, m₂, _, _, hwrap₂, _⟩ := runMatches_filter_send_send rfl hrm₂
  obtain ⟨ek₂, ct₂, hppk₂, hv₂⟩ := hwrap₂ runWrapped_ev2
  have htr_eq : runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: ss₃))) =
      runSteps ss₃ (s₂.next (runSteps pre₂ (s₁.next (runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r))))))) := by
    change runSteps (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: ss₃))) (setupTrace r) = _
    simp only [runSteps_append_local, runSteps]
  have hle₂ : runSteps pre₂ (s₁.next (runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r))))) ≤
      runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: ss₃))) := by
    rw [htr_eq]; exact DY.Trace.le_trans _ _ _ (step_le_next_local s₂ _) (runSteps_le_local ss₃ _)
  have hle₁ : runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r))) ≤
      runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: ss₃))) :=
    DY.Trace.le_trans _ _ _ (DY.Trace.le_trans _ _ _ (step_le_next_local s₁ _) (runSteps_le_local pre₂ _)) hle₂
  refine ⟨_, idx₁, ek₁, ct₁, m₁, _, idx₂, ek₂, ct₂, m₂, hle₁, hppk₁, hle₂, hppk₂, ?_⟩
  simp only [List.append_nil, List.filter_append, hv₀, hv₁, hv₂]; rfl

theorem matchesEventsClassical_take16_sendTerms
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hmev : MatchesEventsClassical SpecTop.compI0 r S g (setupTrace r) ss
      [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4, .run ev5] vis) :
    ∃ tr₁ idx₁ ek₁ ct₁ m₁ tr₂ idx₂ ek₂ ct₂ m₂ tr₅ idx₅ ek₅ ct₅ m₅,
      tr₁ ≤ runTrace r ss ∧ pendingPreKey tr₁ idx₁ = some (ek₁, ct₁) ∧
      tr₂ ≤ runTrace r ss ∧ pendingPreKey tr₂ idx₂ = some (ek₂, ct₂) ∧
      tr₅ ≤ runTrace r ss ∧ pendingPreKey tr₅ idx₅ = some (ek₅, ct₅) ∧
      (vis.filter (·.kind == .send)).flatMap (·.terms) = [ek₁, ct₁, m₁, ek₂, ct₂, m₂, ek₅, ct₅, m₅] := by
  obtain ⟨pre₀, s₀, ss₁, v₀, vs₁, rfl, rfl, hrm₀, hmev₁⟩ := matchesEventsClassical_run_exit0_inv_local (out := []) rfl hmev
  obtain ⟨pre₁, s₁, ss₂, v₁, vs₂, rfl, rfl, hrm₁, hmev₂⟩ := matchesEventsClassical_run_exit0_inv_local (out := sendAt 37) rfl hmev₁
  obtain ⟨pre₂, s₂, ss₃, v₂, vs₃, rfl, rfl, hrm₂, hmev₃⟩ := matchesEventsClassical_run_exit0_inv_local (out := wireAt 40) rfl hmev₂
  obtain ⟨pre₃, s₃, ss₄, v₃, vs₄, rfl, rfl, hrm₃, hmev₄⟩ := matchesEventsClassical_run_exit0_inv_local (out := acceptAt 42) rfl hmev₃
  obtain ⟨pre₄, s₄, ss₅, v₄, vs₅, rfl, rfl, hrm₄, hmev₅⟩ := matchesEventsClassical_run_exit0_inv_local (out := []) rfl hmev₄
  obtain ⟨pre₅, s₅, ss₆, v₅, vs₆, rfl, rfl, hrm₅, hmev₆⟩ := matchesEventsClassical_run_exit0_inv_local (out := sendAt 80) rfl hmev₅
  cases matchesEventsClassical_nil_vis_local hmev₆
  have hv₀ := runMatches_filter_send_init rfl hrm₀
  obtain ⟨idx₁, _, _, m₁, _, _, hwrap₁, _⟩ := runMatches_filter_send_send rfl hrm₁
  obtain ⟨ek₁, ct₁, hppk₁, hv₁⟩ := hwrap₁ runWrapped_ev1
  obtain ⟨idx₂, _, _, m₂, _, _, hwrap₂, _⟩ := runMatches_filter_send_send rfl hrm₂
  obtain ⟨ek₂, ct₂, hppk₂, hv₂⟩ := hwrap₂ runWrapped_ev2
  have hv₃ := runMatches_filter_send_recv rfl hrm₃
  have hv₄ := runMatches_filter_send_init rfl hrm₄
  obtain ⟨idx₅, _, _, m₅, _, _, hwrap₅, _⟩ := runMatches_filter_send_send rfl hrm₅
  obtain ⟨ek₅, ct₅, hppk₅, hv₅⟩ := hwrap₅ runWrapped_ev5
  let tr_s₁ := runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r)))
  let tr_s₂ := runSteps pre₂ (s₁.next tr_s₁)
  let tr_s₃ := runSteps pre₃ (s₂.next tr_s₂)
  let tr_s₄ := runSteps pre₄ (s₃.next tr_s₃)
  let tr_s₅ := runSteps pre₅ (s₄.next tr_s₄)
  have htr_eq : runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: (pre₃ ++ s₃ :: (pre₄ ++ s₄ :: (pre₅ ++ s₅ :: ss₆)))))) =
      runSteps ss₆ (s₅.next tr_s₅) := by
    change runSteps (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: (pre₃ ++ s₃ :: (pre₄ ++ s₄ :: (pre₅ ++ s₅ :: ss₆)))))) (setupTrace r) = _
    simp only [tr_s₅, tr_s₄, tr_s₃, tr_s₂, tr_s₁, runSteps_append_local, runSteps]
  have hle₅ : tr_s₅ ≤ runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: (pre₃ ++ s₃ :: (pre₄ ++ s₄ :: (pre₅ ++ s₅ :: ss₆)))))) := by
    rw [htr_eq]; exact DY.Trace.le_trans _ _ _ (step_le_next_local s₅ _) (runSteps_le_local ss₆ _)
  have hle₄ : tr_s₄ ≤ tr_s₅ := DY.Trace.le_trans _ _ _ (step_le_next_local s₄ _) (runSteps_le_local pre₅ _)
  have hle₃ : tr_s₃ ≤ tr_s₄ := DY.Trace.le_trans _ _ _ (step_le_next_local s₃ _) (runSteps_le_local pre₄ _)
  have hle₂ : tr_s₂ ≤ tr_s₃ := DY.Trace.le_trans _ _ _ (step_le_next_local s₂ _) (runSteps_le_local pre₃ _)
  have hle₁ : tr_s₁ ≤ tr_s₂ := DY.Trace.le_trans _ _ _ (step_le_next_local s₁ _) (runSteps_le_local pre₂ _)
  have hle₂_tot : tr_s₂ ≤ runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: (pre₃ ++ s₃ :: (pre₄ ++ s₄ :: (pre₅ ++ s₅ :: ss₆)))))) :=
    DY.Trace.le_trans _ _ _ hle₂ (DY.Trace.le_trans _ _ _ hle₃ (DY.Trace.le_trans _ _ _ hle₄ hle₅))
  have hle₁_tot : tr_s₁ ≤ runTrace r (pre₀ ++ s₀ :: (pre₁ ++ s₁ :: (pre₂ ++ s₂ :: (pre₃ ++ s₃ :: (pre₄ ++ s₄ :: (pre₅ ++ s₅ :: ss₆)))))) :=
    DY.Trace.le_trans _ _ _ hle₁ hle₂_tot
  refine ⟨tr_s₁, idx₁, ek₁, ct₁, m₁, tr_s₂, idx₂, ek₂, ct₂, m₂, tr_s₅, idx₅, ek₅, ct₅, m₅,
    hle₁_tot, hppk₁, hle₂_tot, hppk₂, hle₅, hppk₅, ?_⟩
  simp only [List.append_nil, List.filter_append, hv₀, hv₁, hv₂, hv₃, hv₄, hv₅]; rfl

open Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38
  Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
  Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs in
theorem filter_send_aliceStart_nil (tr : ExecTrace) (a b : Participant) (ik spk : Nat)
    (hb : DY.Libsignal.PQXDH.BundleHandles) (sh : Nat) :
    ((Move.aliceStart a b ik spk hb sh).vis tr).filter (·.kind == .send) = [] := by
  rw [aliceStart_vis_eq, List.filter_eq_nil_iff]; intro v hv; simp only [beq_iff_eq]
  rcases xpl_aliceVis_kind (List.mem_of_mem_take hv) with hk | hk <;> (rw [hk]; decide)
open Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs in
theorem filter_send_bobStart_nil (tr : ExecTrace) (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA : Nat)
    (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqrMsgIdx : UInt32) (sh : Nat) :
    ((Move.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx sh).vis tr).filter (·.kind == .send) = [] := by
  rw [WsIdx1Prefix81Enum.bobStart_vis_eq, List.filter_eq_nil_iff]; intro v hv; simp only [beq_iff_eq]
  rcases xpl_bobVis_kind (List.mem_of_mem_take hv) with hk | hk | hk <;> (rw [hk]; decide)
open Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38
  Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc in
theorem filter_send_encrypt_encNextTr {tr : ExecTrace} {me : Participant} {sIdx : Nat}
    {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq e c : Nat}
    (hm : (Move.encrypt me sIdx cl pq (some (e, c))).next tr = encNextTr tr me sIdx stA cl pq) :
    ((Move.encrypt me sIdx cl pq (some (e, c))).vis tr).filter (·.kind == .send) =
      [⟨.send, received tr [e, c] ++ [encOut tr stA cl pq], .preKeySend, none⟩] := by
  rw [encrypt_vis_eq, hm]; unfold encVis
  have hdr : (encDraws (newRandoms tr (encNextTr tr me sIdx stA cl pq))).filter (·.kind == .send) = [] := by
    rw [List.filter_eq_nil_iff]; intro v hv; simp only [beq_iff_eq]
    rcases mem_encDraws_encNextTr hv with rfl | rfl <;> intro h <;> cases h
  simp only [↓reduceIte, List.filter_append, hdr, List.nil_append]; unfold encSend; rw [lastSent_encNextTr]; rfl

open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a
  (bobStartTr bobStartSkipTr bobStartPreSkipTr bobOutOf at?_append_other_eq' at?_append_same_eq' at?_other_logSkippedKeys) in
theorem eventLoggedAt_aliceDone_bobStartTr {tr : ExecTrace} {b a : Participant}
    {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    (w : CompSetupSecrecy.BobStartOk tr b a kh regA mh pqIdx spqrMsgIdx) {a' b' : Participant} {ikA ikB spk pqpk : DY.Bytes}
    {opk : Option DY.Bytes} {ek ct : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys} {j : Nat}
    (h : (bobStartTr tr b a w).EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a' b' ikA ikB spk pqpk opk ek ct keys) j) :
    tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a' b' ikA ikB spk pqpk opk ek ct keys) j := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent)] at h ⊢
  unfold bobStartTr bobStartSkipTr bobStartPreSkipTr bobOutOf at h; dsimp only at h
  rw [at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TRStE _ _) rfl,
      at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TREvE _) rfl,
      at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TREvE _) rfl,
      at?_other_logSkippedKeys (fun _ => rfl),
      at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.CEvE _) rfl,
      at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TREvE _) rfl,
      at?_append_other_eq' _ (Symbolic.Swarm.COMPOSED.CompTrace.TREvE _) rfl] at h
  cases hopk : w.opk <;> simp only [hopk, Option.map] at h
  · rw [at?_append_same_eq', at?_append_other_eq' _ (Symbolic.Swarm.CREF.TR.NetE _) rfl,
        at?_append_other_eq' _ (Symbolic.Swarm.CREF.TR.RndE _) rfl] at h
    split_ifs at h <;> first | exact h | nomatch h
  · rw [at?_append_same_eq', at?_append_same_eq', at?_append_other_eq' _ (Symbolic.Swarm.CREF.TR.NetE _) rfl,
        at?_append_other_eq' _ (Symbolic.Swarm.CREF.TR.RndE _) rfl] at h
    split_ifs at h <;> first | exact h | nomatch h

open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
  Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
  Symbolic.BugInjection.Proofs.Common443.CompRVariantFree38 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv78a in
theorem aliceDone_split81_pin {r : Records} {pre₀ mid₁ mid₂ mid₃ mid₄ mid₅ post₅ : List Move}
    {m₁ m₂ m₃ m₄ m₅ : Move} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {a₀ b₀ b_bob a_bob : Participant}
    {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat} {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx : Nat} {spqrMsgIdx : UInt32}
    {w_bob : CompSetupSecrecy.BobStartOk tr_bob b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx}
    {o₁ o₂ : DY.Libsignal.PQXDH.AliceHandshakeOut} {me₁ me₂ me₅ : Participant}
    {s₁ cl₁ pq₁ s₂ cl₂ pq₂ s₅ cl₅ pq₅ : Nat} {stA₁ stA₁' stA₂ : DY.Libsignal.TripleRatchet.TRState}
    {a' b' : Participant} {ikA ikB spk pqpk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys} {j : Nat}
    (hNe : r.alice ≠ r.bob) (htr₁ : tr₁ = (runMoves pre₀ (setupTrace r)).1) (hpre₀ : MovesFrom InvisibleNoEffect (setupTrace r) pre₀)
    (htr₂ : tr₂ = (runMoves mid₁ (iniAliceStartTr tr₁ a₀ b₀ o₁)).1) (hmid₁ : MovesFrom InvisibleNoEffect (iniAliceStartTr tr₁ a₀ b₀ o₁) mid₁)
    (hm₁ : m₁.next tr₂ = encNextTr tr₂ me₁ s₁ stA₁ cl₁ pq₁)
    (htr₃ : tr₃ = (runMoves mid₂ (m₁.next tr₂)).1) (hmid₂ : MovesFrom InvisibleNoEffect (m₁.next tr₂) mid₂)
    (hm₂ : m₂.next tr₃ = encNextTr tr₃ me₂ s₂ stA₁' cl₂ pq₂)
    (htr_bob : tr_bob = (runMoves mid₃ (m₂.next tr₃)).1) (hmid₃ : MovesFrom InvisibleNoEffect (m₂.next tr₃) mid₃)
    (hm₃ : m₃.next tr_bob = bobStartTr tr_bob b_bob a_bob w_bob)
    (htr₄ : tr₄ = (runMoves mid₄ (m₃.next tr_bob)).1) (hmid₄ : MovesFrom InvisibleNoEffect (m₃.next tr_bob) mid₄)
    (hm₄ : m₄.next tr₄ = iniAliceStartTr tr₄ a₀ b₀ o₂)
    (htr₅ : tr₅ = (runMoves mid₅ (m₄.next tr₄)).1) (hmid₅ : MovesFrom InvisibleNoEffect (m₄.next tr₄) mid₅)
    (hm₅ : m₅.next tr₅ = encNextTr tr₅ me₅ s₅ stA₂ cl₅ pq₅) (hpost₅ : MovesFrom InvisibleNoEffect (m₅.next tr₅) post₅)
    (hEv : ((runMoves post₅ (m₅.next tr₅)).1).EventLoggedAt
      (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a' b' ikA ikB spk pqpk opk ek ct keys) j) :
    (ek = o₁.ek ∧ ct = o₁.ct) ∨ (ek = o₂.ek ∧ ct = o₂.ct) := by
  rw [eventLoggedAt_of_movesFrom_invisibleNoEffect hpost₅, hm₅] at hEv
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent),
      WsIdx1Prefix81Enum.at?_pqEv_encNextTr,
      ← Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent)] at hEv
  rw [htr₅, eventLoggedAt_of_movesFrom_invisibleNoEffect hmid₅, hm₄] at hEv
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent),
      WsIdx1Prefix81Enum.at?_pqEv_iniAliceStartTr] at hEv
  split at hEv
  · cases hEv; exact Or.inr ⟨rfl, rfl⟩
  · rw [← Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.eventLoggedAt_eq_at? (E := DY.Libsignal.PQXDH.PQXDHEvent),
        htr₄, eventLoggedAt_of_movesFrom_invisibleNoEffect hmid₄, hm₃] at hEv
    obtain ⟨_, _, _, _, _, _, _, _, rfl, rfl, _⟩ :=
      WsIdx1Prefix81Enum.aliceDone_tr_bob_pin hNe htr₁ hpre₀ htr₂ hmid₁ hm₁ htr₃ hmid₂ hm₂ htr_bob hmid₃
        (eventLoggedAt_aliceDone_bobStartTr w_bob hEv)
    exact Or.inl ⟨rfl, rfl⟩

open Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub in
theorem ek_ct_mem_prefixTerms_of_links81Own {r : Records} {ms' : List Move}
    {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hown : Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) :
    let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let o₂ := CompPrefixInvAlice.iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    o₁.ek ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧ o₁.ct ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    o₂.ek ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧ o₂.ct ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') := by
  intro o₁ o₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hk₁₂, _, _, hk₄₅,
    htr₁, hget₁, htr₂, hget₂, _, _, htr₄, hget₄, htr₅, hget₅, hnext₁, hnext₄, henc₂, _, henc₅⟩ := hown
  have hrecv₁ := received_own_wrap_eq (hnext₁ ▸ next_le_runTrace_take_of_lt hk₁₂ htr₁ hget₁ htr₂)
  have hrecv₂ := received_own_wrap_eq (hnext₄ ▸ next_le_runTrace_take_of_lt hk₄₅ htr₄ hget₄ htr₅)
  exact ⟨wrap_terms_mem_prefixTerms_of_getElem? htr₂ hget₂ henc₂ (by rw [hrecv₁]; exact List.mem_cons_self),
         wrap_terms_mem_prefixTerms_of_getElem? htr₂ hget₂ henc₂ (by rw [hrecv₁]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)),
         wrap_terms_mem_prefixTerms_of_getElem? htr₅ hget₅ henc₅ (by rw [hrecv₂]; exact List.mem_cons_self),
         wrap_terms_mem_prefixTerms_of_getElem? htr₅ hget₅ henc₅ (by rw [hrecv₂]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

def SendSwapRel (v₁ v₂ : VisEntry) : Prop :=
  v₁.terms.getLast? = v₂.terms.getLast? ∧ (v₂.terms.length ≤ 3 → v₁.terms.length ≤ 3)
theorem forall₂_append_local {R : VisEntry → VisEntry → Prop} :
    ∀ {xs₁ ys₁ xs₂ ys₂ : List VisEntry}, List.Forall₂ R xs₁ ys₁ → List.Forall₂ R xs₂ ys₂ → List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂)
  | _, _, _, _, .nil, h₂ => h₂
  | _, _, _, _, .cons h hs, h₂ => .cons h (forall₂_append_local hs h₂)
theorem forall₂_sendSwapRel_refl : ∀ (vs : List VisEntry), List.Forall₂ SendSwapRel vs vs
  | [] => .nil
  | _ :: vs => .cons ⟨rfl, id⟩ (forall₂_sendSwapRel_refl vs)
theorem forall₂_sendSwapRel_trans :
    ∀ {vs₁ vs₂ vs₃ : List VisEntry}, List.Forall₂ SendSwapRel vs₁ vs₂ → List.Forall₂ SendSwapRel vs₂ vs₃ → List.Forall₂ SendSwapRel vs₁ vs₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ hs₁, .cons h₂ hs₂ => .cons ⟨h₁.1.trans h₂.1, h₁.2 ∘ h₂.2⟩ (forall₂_sendSwapRel_trans hs₁ hs₂)
theorem getLast?_append_singleton_local : ∀ (xs : List DY.Bytes) (y : DY.Bytes), (xs ++ [y]).getLast? = some y
  | [], _ | [_], _ => rfl
  | _ :: b :: xs, y => getLast?_append_singleton_local (b :: xs) y

theorem encSend_sendSwapRel (tr tr' : ExecTrace) (w₁ w₂ : Option (Nat × Nat)) :
    List.Forall₂ SendSwapRel
      ((encSend tr tr' w₁).filter (·.kind == .send)) ((encSend tr tr' w₂).filter (·.kind == .send)) := by
  unfold encSend; cases lastSent tr tr'
  · exact .nil
  · rename_i msg
    have hlen : ∀ e c, (received tr [e, c] ++ [msg]).length ≤ 3 := fun e c => by
      have := received_two_length_le tr e c; simp only [List.length_append, List.length_singleton]; omega
    cases w₁ <;> cases w₂ <;> refine .cons ⟨?_, fun _ => ?_⟩ .nil
    · rfl
    · simp
    · exact (getLast?_append_singleton_local _ _).symm
    · simp
    · exact getLast?_append_singleton_local _ _
    · exact hlen _ _
    · exact (getLast?_append_singleton_local _ _).trans (getLast?_append_singleton_local _ _).symm
    · exact hlen _ _

theorem encrypt_vis_filter_send_swap (tr : ExecTrace) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)) :
    List.Forall₂ SendSwapRel (((Move.encrypt me s cl pq w₁).vis tr).filter (·.kind == .send))
      (((Move.encrypt me s cl pq w₂).vis tr).filter (·.kind == .send)) := by
  simp only [Move.vis, WsIdx1DecompSwap.encrypt_next_eq_wrap tr me s cl pq w₁ w₂]
  unfold encVis; simp only [↓reduceIte, List.filter_append]
  exact forall₂_append_local
    (forall₂_append_local (forall₂_sendSwapRel_refl _) (encSend_sendSwapRel _ _ w₁ w₂))
    (forall₂_sendSwapRel_refl _)

theorem runMoves_snd_filter_send_encrypt_swap :
    ∀ (P : List Move) (tr : ExecTrace) (Q : List Move) (me : Participant) (s cl pq : Nat) (w₁ w₂ : Option (Nat × Nat)),
      List.Forall₂ SendSwapRel (((runMoves (P ++ .encrypt me s cl pq w₁ :: Q) tr).2).filter (·.kind == .send))
        (((runMoves (P ++ .encrypt me s cl pq w₂ :: Q) tr).2).filter (·.kind == .send))
  | [], tr, Q, me, s, cl, pq, w₁, w₂ => by
    simp only [List.nil_append, runMoves, WsIdx1DecompSwap.encrypt_next_eq_wrap tr me s cl pq w₁ w₂, List.filter_append]
    exact forall₂_append_local (encrypt_vis_filter_send_swap tr me s cl pq w₁ w₂) (forall₂_sendSwapRel_refl _)
  | m :: P, tr, Q, me, s, cl, pq, w₁, w₂ => by
    simp only [List.cons_append, runMoves, List.filter_append]
    exact forall₂_append_local (forall₂_sendSwapRel_refl _) (runMoves_snd_filter_send_encrypt_swap P (m.next tr) Q me s cl pq w₁ w₂)

theorem runVis_filter_send_encrypt_swap {r : Records}
    {P Q : List Move} {me : Participant} {s cl pq : Nat} {w₁ w₂ : Option (Nat × Nat)} :
    List.Forall₂ SendSwapRel ((runVis r (P ++ .encrypt me s cl pq w₁ :: Q)).filter (·.kind == .send))
      ((runVis r (P ++ .encrypt me s cl pq w₂ :: Q)).filter (·.kind == .send)) := by
  unfold runVis; simp only [runMoves, List.filter_append]
  exact forall₂_append_local (forall₂_sendSwapRel_refl _) (runMoves_snd_filter_send_encrypt_swap P (r.setupMove.next Trace.nil) Q me s cl pq w₁ w₂)

theorem split_three_of_append_eq {a b c d : DY.Bytes} {xs ys ys' : List DY.Bytes}
    (h : xs ++ ys = a :: b :: c :: ys') (hxs : xs.length ≤ 3) (hys : ys.length ≤ ys'.length) (hlast : xs.getLast? = some d) :
    c = d ∧ ys = ys' := by
  have hlen := congrArg List.length h; simp only [List.length_append, List.length_cons] at hlen
  rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | ⟨x₄, xs⟩⟩⟩⟩ <;> simp only [List.length] at hxs hlen <;> try omega
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h; simp only [List.getLast?] at hlast
  exact ⟨h.2.2.1.symm.trans (Option.some.inj hlast), h.2.2.2⟩

theorem sendSwapRel_mkPreKeySend {v : VisEntry} {tr : ExecTrace} {e c : Nat} {msg : DY.Bytes}
    (h : SendSwapRel v ⟨.send, received tr [e, c] ++ [msg], .preKeySend, none⟩) :
    v.terms.getLast? = some msg ∧ v.terms.length ≤ 3 := by
  refine ⟨h.1.trans (getLast?_append_singleton_local _ _), h.2 ?_⟩
  have := received_two_length_le tr e c; simp only [List.length_append, List.length_singleton]; omega

theorem forall₂_sendSwapRel_two_eq {vs : List VisEntry}
    {tr₂ tr₃ : ExecTrace} {e₁ c₁ e₂ c₂ : Nat} {out₁ out₂ a₁ b₁ m₁ a₂ b₂ m₂ : DY.Bytes}
    (hrel : List.Forall₂ SendSwapRel vs
      [⟨.send, received tr₂ [e₁, c₁] ++ [out₁], .preKeySend, none⟩, ⟨.send, received tr₃ [e₂, c₂] ++ [out₂], .preKeySend, none⟩])
    (heq : vs.flatMap (·.terms) = [a₁, b₁, m₁, a₂, b₂, m₂]) : m₁ = out₁ ∧ m₂ = out₂ := by
  rcases hrel with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
  obtain ⟨hl₁, hlen₁⟩ := sendSwapRel_mkPreKeySend h₁; obtain ⟨hl₂, hlen₂⟩ := sendSwapRel_mkPreKeySend h₂
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at heq
  obtain ⟨hm₁, heq₂⟩ := split_three_of_append_eq heq hlen₁ (by simp only [List.length_cons, List.length_nil]; omega) hl₁
  obtain ⟨hm₂, _⟩ := split_three_of_append_eq (ys := []) (by simpa using heq₂) hlen₂ (Nat.zero_le _) hl₂
  exact ⟨hm₁, hm₂⟩

theorem forall₂_sendSwapRel_three_eq {vs : List VisEntry}
    {tr₂ tr₃ tr₅ : ExecTrace} {e₁ c₁ e₂ c₂ e₅ c₅ : Nat} {out₁ out₂ out₅ a₁ b₁ m₁ a₂ b₂ m₂ a₅ b₅ m₅ : DY.Bytes}
    (hrel : List.Forall₂ SendSwapRel vs
      [⟨.send, received tr₂ [e₁, c₁] ++ [out₁], .preKeySend, none⟩,
       ⟨.send, received tr₃ [e₂, c₂] ++ [out₂], .preKeySend, none⟩,
       ⟨.send, received tr₅ [e₅, c₅] ++ [out₅], .preKeySend, none⟩])
    (heq : vs.flatMap (·.terms) = [a₁, b₁, m₁, a₂, b₂, m₂, a₅, b₅, m₅]) : m₁ = out₁ ∧ m₂ = out₂ ∧ m₅ = out₅ := by
  rcases hrel with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | _⟩⟩⟩
  obtain ⟨hl₁, hlen₁⟩ := sendSwapRel_mkPreKeySend h₁; obtain ⟨hl₂, hlen₂⟩ := sendSwapRel_mkPreKeySend h₂
  obtain ⟨hl₃, hlen₃⟩ := sendSwapRel_mkPreKeySend h₃
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at heq
  obtain ⟨hm₁, heq₂⟩ := split_three_of_append_eq heq hlen₁ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hl₁
  obtain ⟨hm₂, heq₃⟩ := split_three_of_append_eq heq₂ hlen₂ (by simp only [List.length_cons, List.length_nil]; omega) hl₂
  obtain ⟨hm₃, _⟩ := split_three_of_append_eq (ys := []) (by simpa using heq₃) hlen₃ (Nat.zero_le _) hl₃
  exact ⟨hm₁, hm₂, hm₃⟩

theorem noBscCliAt_8_sub {r : Records} {S : Sem} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {p : PreKeyFields} {τ : List MachineEvent} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2]) (hp : parsePreKeyWire (wireAt 40) = some p)
    (hex_cli : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 8) τ g ms)
    (hnb : CompSetupSecrecy.NoBrk r ms) (htr : runTraceMoves r ms = runTrace r ss) (hsalts : honestSalts r ms = honestSaltsOf r ss)
    (hpre : prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis)
    (hpt : plaintextTerms (runVis r ms) = plaintextTerms vis) :
    ∃ (ms' : List Move) (x : PreKeyRep),
      runTraceMoves r ms' = runTrace r ss ∧ honestSalts r ms' = honestSaltsOf r ss ∧
      (∀ u ∈ (vis.filter (·.kind == .send)).flatMap (·.terms), u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms')) ∧
      plaintextTerms (runVis r ms') = plaintextTerms vis ∧
      x ∈ preKeyRepresentations SpecTop.compI0 r S g ms' (wireAt 40) ∧ ¬ BobStartCollision SpecTop.compI0 r S g ms' p x := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  obtain ⟨b1, b2, hc1, hc2, rfl⟩ := explainsCli_take8_cut hfits hex_cli
  obtain ⟨ms', tr₁, tr₂, tr₃, cl₁, cl₂, hex',
    ⟨P₁, mid₂, post, me, s₁, pq₁, s₂, pq₂, w₁, w₂, w₁', w₂', hms_eq, hms'_eq⟩, _, hinv, hown, hx⟩ :=
    WsIdx1Decomp40.split40DecompSwapRep_split_of WsIdx1PrefSafe40.pref40 hfits hnb hc1 hc2 ⟨hex_cli.2.1, hex_cli.2.2.1.1⟩ hp
  have hA : ∀ (u₁ u₂ : Option (Nat × Nat)),
      P₁ ++ .encrypt me s₁ cl₁ pq₁ u₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ u₂ :: post =
      P₁ ++ .encrypt me s₁ cl₁ pq₁ u₁ :: (mid₂ ++ .encrypt me s₂ cl₂ pq₂ u₂ :: post) := by intros; simp only [List.append_assoc, List.cons_append]
  have htr' : runTraceMoves r ms' = runTrace r ss := by
    rw [hms'_eq, runTraceMoves_encrypt_swap (w₁ := w₂), hA, runTraceMoves_encrypt_swap (w₁ := w₁), ← hA, ← hms_eq, htr]
  have hsalts' : honestSalts r ms' = honestSaltsOf r ss := by
    rw [hms'_eq, honestSalts_encrypt_swap (w₁ := w₂), hA, honestSalts_encrypt_swap (w₁ := w₁), ← hA, ← hms_eq, hsalts]
  have hpt' : plaintextTerms (runVis r ms') = plaintextTerms vis := by
    rw [hms'_eq, plaintextTerms_runVis_encrypt_swap (w₁ := w₂), hA, plaintextTerms_runVis_encrypt_swap (w₁ := w₁), ← hA, ← hms_eq, hpt]
  refine ⟨ms', _, htr', hsalts', ?_, hpt', hx, ?_⟩
  · obtain ⟨pre₀, mid₁, mid₂', post', hb₁, sh₁, s₁', s₂', hms'_decomp, htr₁, htr₂, htr₃, hpre₀, hmid₁, hmid₂', hpost', hm₀, hm₁', hm₂', -⟩ :=
      WsIdx1Prefix40Enum.decomp40_of_mp_links hc1 hc2 (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hex'.1) hown
    let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
    let stA₁' := CompPrefixInvEnc.encSt tr₂ stA₁ cl₁
    have hvis_ms' : (runVis r ms').filter (·.kind == .send) =
        [⟨.send, received tr₂ [tr₁.length + 3, tr₁.length + 4] ++ [CompPrefixInvEnc.encOut tr₂ stA₁ cl₁ (tr₂.length + 2)], .preKeySend, none⟩,
         ⟨.send, received tr₃ [tr₁.length + 3, tr₁.length + 4] ++ [CompPrefixInvEnc.encOut tr₃ stA₁' cl₂ (tr₃.length + 2)], .preKeySend, none⟩] := by
      rw [hms'_decomp, WsIdx1Prefix40Enum.runVis_split40 hNe htr₁ htr₂ htr₃ hpre₀ hmid₁ hmid₂' hpost',
        List.filter_append, List.filter_append, filter_send_aliceStart_nil,
        filter_send_encrypt_encNextTr hm₁', filter_send_encrypt_encNextTr hm₂']; rfl
    have hrel : List.Forall₂ SendSwapRel ((runVis r ms).filter (·.kind == .send)) ((runVis r ms').filter (·.kind == .send)) := by
      rw [hms_eq, hms'_eq]
      refine forall₂_sendSwapRel_trans ?_ (runVis_filter_send_encrypt_swap (w₁ := w₂) (w₂ := w₂'))
      rw [hA w₁ w₂, hA w₁' w₂]; exact runVis_filter_send_encrypt_swap (w₁ := w₁) (w₂ := w₁')
    obtain ⟨tr_s₁, idx₁, ek₁, ct₁, m₁, tr_s₂, idx₂, ek₂, ct₂, m₂, hle₁, hppk₁, hle₂, hppk₂, hvis_send⟩ :=
      matchesEventsClassical_take8_sendTerms hex.2.2.2
    obtain ⟨rfl, rfl⟩ := forall₂_sendSwapRel_two_eq (hvis_ms' ▸ hrel) ((sendTerms_eq_of_prefixTerms_eq hpre hpt).trans hvis_send)
    have htr_ms' : runTrace r ss = (runMoves post' ((Move.encrypt r.alice s₂' cl₂ (tr₃.length + 2)
        (some (tr₁.length + 3, tr₁.length + 4))).next tr₃)).1 := by
      rw [← htr', hms'_decomp, WsIdx1Prefix40Enum.runTrace_split40 htr₁ htr₂ htr₃]
    obtain ⟨_, _, _, _, _, _, _, _, _, hEv₁⟩ := exists_aliceDone_of_pendingPreKey_local (htr_ms' ▸ hle₁) hppk₁
    obtain ⟨_, _, _, _, _, _, _, _, rfl, rfl, _⟩ :=
      WsIdx1Prefix81Enum.aliceDone_tr_bob_pin hNe htr₁ hpre₀ (hm₀ ▸ htr₂) (hm₀ ▸ hmid₁) hm₁' htr₃ hmid₂' hm₂' rfl hpost' hEv₁
    obtain ⟨_, _, _, _, _, _, _, _, _, hEv₂⟩ := exists_aliceDone_of_pendingPreKey_local (htr_ms' ▸ hle₂) hppk₂
    obtain ⟨_, _, _, _, _, _, _, _, rfl, rfl, _⟩ :=
      WsIdx1Prefix81Enum.aliceDone_tr_bob_pin hNe htr₁ hpre₀ (hm₀ ▸ htr₂) (hm₀ ▸ hmid₁) hm₁' htr₃ hmid₂' hm₂' rfl hpost' hEv₂
    obtain ⟨hek_mem, hct_mem⟩ := WsIdx1Split40MemoNewSub.ek_ct_mem_prefixTerms_of_links40Own hown
    obtain ⟨hm₁_mem, hm₂_mem, _, _⟩ := WsIdx1Split40MemoNewSub.prefixTerms_mem_of_ws40Idx1RunInv hinv
    rw [WsIdx1Prefix40Enum.census_iniAliceOut_eq] at hek_mem hct_mem hm₁_mem hm₂_mem
    rw [WsIdx1Prefix40Enum.census_iniAliceStartState_eq, WsIdx1Prefix40Enum.census_encOut_eq] at hm₁_mem hm₂_mem
    rw [WsIdx1Prefix40Enum.census_encSt_eq] at hm₂_mem
    intro u hu; rw [hvis_send] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · have hM' := WsIdx1Split40MemoCloseFinal.split40MemoCensusOwn r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown
    intro h; unfold BobStartCollision BobSessionStartCollidesOrImplicitRejects at h; dsimp only at h
    rcases hP : parseTrSignalMsg (WsIdx1CensusDefs.x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂).msg with _ | msg <;>
      simp only [WsIdx1Split40Census.split40NewTerms, hP] at h hM'
    · exact hM' h
    · exact h.elim (fun hm => hM' (Symbolic.BugInjection.Proofs.Common443.CompExcuse.memoCollisionOn_bobTrials_to_bobTerms hP hm)) (WsIdx1Split40OwnSalt.split40OwnSaltMac r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ msg hfits hp hinv hP)

theorem noBscCliAt_16_sub {r : Records} {S : Sem} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {p : PreKeyFields} {τ : List MachineEvent} {ms : List Move}
    (hfits : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4, .run ev5])
    (hp : parsePreKeyWire (wireAt 81) = some p)
    (hex_cli : ExplainsCli SpecTop.compI0 r S Witnesses.Cheval26WeakStateIdx1.who Witnesses.Cheval26WeakStateIdx1.ok (cliTrace.take 16) τ g ms)
    (hnb : CompSetupSecrecy.NoBrk r ms) (htr : runTraceMoves r ms = runTrace r ss) (hsalts : honestSalts r ms = honestSaltsOf r ss)
    (hpre : prefixTerms r (runTrace r ss) (runVis r ms) = prefixTerms r (runTrace r ss) vis)
    (hpt : plaintextTerms (runVis r ms) = plaintextTerms vis) :
    ∃ (ms' : List Move) (x : PreKeyRep),
      runTraceMoves r ms' = runTrace r ss ∧ honestSalts r ms' = honestSaltsOf r ss ∧
      (∀ u ∈ (vis.filter (·.kind == .send)).flatMap (·.terms), u ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms')) ∧
      plaintextTerms (runVis r ms') = plaintextTerms vis ∧
      x ∈ preKeyRepresentations SpecTop.compI0 r S g ms' (wireAt 81) ∧ ¬ BobStartCollision SpecTop.compI0 r S g ms' p x := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1
  have hO := WsIdx1Split81Census.split81OwnSaltMac_of_pin WsIdx1Split81MemoDefs.split81PinObl
  obtain ⟨b1, b2, b5, hc1, hc2, hc5, rfl⟩ := explainsCli_take16_cut hfits hex_cli
  obtain ⟨ms', tr₁, tr₂, tr₃, tr₄, tr₅, cl₁, cl₂, cl₅, hex',
    ⟨P₁, mid₂, P₂, post₅, me, s₁, pq₁, s₂, pq₂, s₅, pq₅, w₁, w₂, w₅, w₁', w₂', w₅', hms_eq, hms'_eq⟩, _, hinv, hown, hx⟩ :=
    WsIdx1Decomp81.split81DecompSwapRep_split_of
      (WsIdx1PrefSafe81.pref81_of_enum fun hpre_ws => WsIdx1Prefix81Enum.split81PrefixEnum_of_pre hpre_ws)
      hfits hc1 hc2 hc5 ⟨hex_cli.2.1, hex_cli.2.2.1.1⟩ hnb hp
  have hA₁ : ∀ (u₁ u₂ u₅ : Option (Nat × Nat)),
      P₁ ++ .encrypt me s₁ cl₁ pq₁ u₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ u₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ u₅ :: post₅ =
      P₁ ++ .encrypt me s₁ cl₁ pq₁ u₁ :: (mid₂ ++ .encrypt me s₂ cl₂ pq₂ u₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ u₅ :: post₅) := by
    intros; simp only [List.append_assoc, List.cons_append]
  have hA₂ : ∀ (u₁ u₂ u₅ : Option (Nat × Nat)),
      P₁ ++ .encrypt me s₁ cl₁ pq₁ u₁ :: mid₂ ++ .encrypt me s₂ cl₂ pq₂ u₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ u₅ :: post₅ =
      (P₁ ++ .encrypt me s₁ cl₁ pq₁ u₁ :: mid₂) ++ .encrypt me s₂ cl₂ pq₂ u₂ :: (P₂ ++ .encrypt me s₅ cl₅ pq₅ u₅ :: post₅) := by
    intros; simp only [List.append_assoc, List.cons_append]
  have htr' : runTraceMoves r ms' = runTrace r ss := by
    rw [hms'_eq, runTraceMoves_encrypt_swap (w₁ := w₅), hA₂, runTraceMoves_encrypt_swap (w₁ := w₂), ← hA₂, hA₁,
      runTraceMoves_encrypt_swap (w₁ := w₁), ← hA₁, ← hms_eq, htr]
  have hsalts' : honestSalts r ms' = honestSaltsOf r ss := by
    rw [hms'_eq, honestSalts_encrypt_swap (w₁ := w₅), hA₂, honestSalts_encrypt_swap (w₁ := w₂), ← hA₂, hA₁,
      honestSalts_encrypt_swap (w₁ := w₁), ← hA₁, ← hms_eq, hsalts]
  have hpt' : plaintextTerms (runVis r ms') = plaintextTerms vis := by
    rw [hms'_eq, plaintextTerms_runVis_encrypt_swap (w₁ := w₅), hA₂, plaintextTerms_runVis_encrypt_swap (w₁ := w₂), ← hA₂, hA₁,
      plaintextTerms_runVis_encrypt_swap (w₁ := w₁), ← hA₁, ← hms_eq, hpt]
  refine ⟨ms', _, htr', hsalts', ?_, hpt', hx, ?_⟩
  · obtain ⟨pre₀, mid₁', mid₂', mid₃', mid₄', mid₅', post₅',
      hb₀, hb₄, sh₀, sh₄, cl₁', e₁, c₁, cl₂', e₂, c₂, cl₅', e₅, c₅,
      b_bob, a_bob, kh, regIdxA, mh, pqIdx, spqrMsgIdx, sh_bob,
      tr₁', tr₂', tr₃', tr_bob, tr₄', tr₅', w_bob, _, _, _, _,
      htr₁', -, -, htr₂', htr₃', htr_bob, htr₄', -, -, htr₅',
      hms'_decomp, -, -, -, hm₃', -, -, hpre₀, hmid₁', hmid₂', hmid₃', hmid₄', hmid₅', hpost₅', -⟩ :=
      WsIdx1Decomp81Core.decomp81_full hfits hown.1 hc1 hc2 hc5 (Symbolic.Swarm.CREF.MatchedPrefix.of_composed hex'.1)
    let m₀ := Move.aliceStart r.alice r.bob 4 6 hb₀ sh₀
    let m₁ := Move.encrypt r.alice (tr₁'.length + 8) cl₁' (tr₂'.length + 2) (some (e₁, c₁))
    let m₂ := Move.encrypt r.alice (tr₂'.length + 5) cl₂' (tr₃'.length + 2) (some (e₂, c₂))
    let m₃ := Move.bobStart b_bob a_bob kh regIdxA mh pqIdx spqrMsgIdx sh_bob
    let m₄ := Move.aliceStart r.alice r.bob 4 6 hb₄ sh₄
    let m₅ := Move.encrypt r.alice (tr₄'.length + 8) cl₅' (tr₅'.length + 2) (some (e₅, c₅))
    have hmid₁_p : MovesFrom InvisibleNoEffect (m₀.next (runMoves pre₀ (setupTrace r)).1) mid₁' := by rw [← htr₁']; exact hmid₁'
    have hmid₂_p : MovesFrom InvisibleNoEffect (m₁.next (runMoves mid₁' (m₀.next (runMoves pre₀ (setupTrace r)).1)).1) mid₂' := by
      rw [← htr₁', ← htr₂']; exact hmid₂'
    have hmid₃_p : MovesFrom InvisibleNoEffect (m₂.next (runMoves mid₂' (m₁.next (runMoves mid₁' (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1) mid₃' := by
      rw [← htr₁', ← htr₂', ← htr₃']; exact hmid₃'
    have hmid₄_p : MovesFrom InvisibleNoEffect (m₃.next (runMoves mid₃' (m₂.next (runMoves mid₂' (m₁.next (runMoves mid₁' (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1) mid₄' := by
      rw [← htr₁', ← htr₂', ← htr₃', ← htr_bob]; exact hmid₄'
    have hmid₅_p : MovesFrom InvisibleNoEffect (m₄.next (runMoves mid₄' (m₃.next (runMoves mid₃' (m₂.next (runMoves mid₂' (m₁.next (runMoves mid₁' (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1)).1) mid₅' := by
      rw [← htr₁', ← htr₂', ← htr₃', ← htr_bob, ← htr₄']; exact hmid₅'
    have hpost₅_p : MovesFrom InvisibleNoEffect (m₅.next (runMoves mid₅' (m₄.next (runMoves mid₄' (m₃.next (runMoves mid₃' (m₂.next (runMoves mid₂' (m₁.next (runMoves mid₁' (m₀.next (runMoves pre₀ (setupTrace r)).1)).1)).1)).1)).1)).1) post₅' := by
      rw [← htr₁', ← htr₂', ← htr₃', ← htr_bob, ← htr₄', ← htr₅']; exact hpost₅'
    obtain ⟨hb₁, hb₂, sh₁, sh₂, s₁', s₂', s₅', hm₀_eq, hm₁_eq, hm₂_eq, hm₄_eq, hm₅_eq,
      htr₁, htr₂, htr₃, htr₄, htr₅, hm₀, hm₁', hm₂', hm₄, hm₅'⟩ :=
      WsIdx1Prefix81Enum.decomp81_links_pin (m₀ := m₀) (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) (m₄ := m₄) (m₅ := m₅)
        hms'_decomp hpre₀ hmid₁_p hmid₂_p hmid₃_p hmid₄_p hmid₅_p hpost₅_p
        (fun _ _ _ _ _ _ h => by dsimp only [m₃] at h; cases h) (fun _ _ _ _ _ h => by dsimp only [m₃] at h; cases h) hown
    dsimp only [m₀, m₁, m₂, m₃, m₄, m₅] at hm₀_eq hm₁_eq hm₂_eq hm₄_eq hm₅_eq htr₂ htr₃ htr₄ htr₅ hm₀ hm₁' hm₂' hm₄ hm₅'
    have htr₁_eq : tr₁' = tr₁ := htr₁'.trans htr₁.symm
    rw [htr₁_eq] at htr₂' htr₃' htr₃ hmid₁' hmid₂' hm₁_eq hm₁' hms'_decomp
    have htr₂_eq : tr₂' = tr₂ := htr₂'.trans htr₂.symm
    rw [htr₂_eq] at htr₃' htr₃ htr_bob htr₄ hmid₂' hmid₃' hm₁_eq hm₁' hm₂_eq hm₂' hms'_decomp
    have htr₃_eq : tr₃' = tr₃ := htr₃'.trans htr₃.symm
    rw [htr₃_eq] at htr_bob htr₄ hmid₃' hm₂_eq hm₂' hms'_decomp; rw [← htr_bob] at htr₄
    have htr₄_eq : tr₄' = tr₄ := htr₄'.trans htr₄.symm
    rw [htr₄_eq] at htr₅' hmid₅' hpost₅' hm₅_eq hm₅' hms'_decomp
    have htr₅_eq : tr₅' = tr₅ := htr₅'.trans htr₅.symm
    rw [htr₅_eq] at hpost₅' hm₅_eq hm₅' hms'_decomp
    rw [hm₀_eq] at hmid₁' htr₂ hm₀; rw [hm₁_eq] at hmid₂' htr₃ hm₁'
    rw [hm₂_eq] at hmid₃' htr_bob hm₂'; rw [hm₄_eq] at hmid₅' htr₅ hm₄; rw [hm₅_eq] at hpost₅' hm₅'
    have hms'_pin : ms' = pre₀ ++ Move.aliceStart r.alice r.bob 4 6 hb₁ sh₁ :: mid₁' ++
        Move.encrypt r.alice s₁' cl₁ (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₂' ++
        Move.encrypt r.alice s₂' cl₂ (tr₃.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: mid₃' ++ m₃ :: mid₄' ++
        Move.aliceStart r.alice r.bob 4 6 hb₂ sh₂ :: mid₅' ++
        Move.encrypt r.alice s₅' cl₅ (tr₅.length + 2) (some (tr₄.length + 3, tr₄.length + 4)) :: post₅' := by
      dsimp only [m₃]; rw [← hm₀_eq, ← hm₁_eq, ← hm₂_eq, ← hm₄_eq, ← hm₅_eq]; exact hms'_decomp
    let o₁ := CompPrefixInvAlice.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := CompPrefixInvAlice.iniAliceStartState tr₁ r.bob o₁
    let stA₁' := CompPrefixInvEnc.encSt tr₂ stA₁ cl₁
    let o₂ := CompPrefixInvAlice.iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₂ := CompPrefixInvAlice.iniAliceStartState tr₄ r.bob o₂
    have hvis_ms' : (runVis r ms').filter (·.kind == .send) =
        [⟨.send, received tr₂ [tr₁.length + 3, tr₁.length + 4] ++ [CompPrefixInvEnc.encOut tr₂ stA₁ cl₁ (tr₂.length + 2)], .preKeySend, none⟩,
         ⟨.send, received tr₃ [tr₁.length + 3, tr₁.length + 4] ++ [CompPrefixInvEnc.encOut tr₃ stA₁' cl₂ (tr₃.length + 2)], .preKeySend, none⟩,
         ⟨.send, received tr₅ [tr₄.length + 3, tr₄.length + 4] ++ [CompPrefixInvEnc.encOut tr₅ stA₂ cl₅ (tr₅.length + 2)], .preKeySend, none⟩] := by
      rw [hms'_pin, WsIdx1Prefix81Enum.runVis_split81 hNe htr₁ htr₂ htr₃ htr_bob htr₄ htr₅
        hpre₀ hmid₁' hmid₂' hmid₃' hmid₄' hmid₅' hpost₅']
      simp only [List.filter_append, filter_send_aliceStart_nil, filter_send_bobStart_nil,
        filter_send_encrypt_encNextTr hm₁', filter_send_encrypt_encNextTr hm₂', filter_send_encrypt_encNextTr hm₅']; rfl
    have hrel₁ := by
      have h := runVis_filter_send_encrypt_swap (r := r) (P := P₁)
        (Q := mid₂ ++ .encrypt me s₂ cl₂ pq₂ w₂ :: P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅)
        (me := me) (s := s₁) (cl := cl₁) (pq := pq₁) (w₁ := w₁) (w₂ := w₁')
      rwa [← hA₁ w₁ w₂ w₅, ← hA₁ w₁' w₂ w₅] at h
    have hrel₂ := by
      have h := runVis_filter_send_encrypt_swap (r := r) (P := P₁ ++ .encrypt me s₁ cl₁ pq₁ w₁' :: mid₂)
        (Q := P₂ ++ .encrypt me s₅ cl₅ pq₅ w₅ :: post₅) (me := me) (s := s₂) (cl := cl₂) (pq := pq₂) (w₁ := w₂) (w₂ := w₂')
      rwa [← hA₂ w₁' w₂ w₅, ← hA₂ w₁' w₂' w₅] at h
    have hrel : List.Forall₂ SendSwapRel ((runVis r ms).filter (·.kind == .send)) ((runVis r ms').filter (·.kind == .send)) := by
      rw [hms_eq, hms'_eq]
      exact forall₂_sendSwapRel_trans (forall₂_sendSwapRel_trans hrel₁ hrel₂) (runVis_filter_send_encrypt_swap (w₁ := w₅) (w₂ := w₅'))
    obtain ⟨tr_s₁, idx₁, ek₁, ct₁, m₁_out, tr_s₂, idx₂, ek₂, ct₂, m₂_out, tr_s₅, idx₅, ek₅, ct₅, m₅_out,
      hle₁, hppk₁, hle₂, hppk₂, hle₅, hppk₅, hvis_send⟩ := matchesEventsClassical_take16_sendTerms hex.2.2.2
    obtain ⟨rfl, rfl, rfl⟩ := forall₂_sendSwapRel_three_eq (hvis_ms' ▸ hrel) ((sendTerms_eq_of_prefixTerms_eq hpre hpt).trans hvis_send)
    have htr_ms' : runTrace r ss = (runMoves post₅' ((Move.encrypt r.alice s₅' cl₅ (tr₅.length + 2)
        (some (tr₄.length + 3, tr₄.length + 4))).next tr₅)).1 := by
      rw [← htr', hms'_pin, WsIdx1Prefix81Enum.runTrace_split81 htr₁ htr₂ htr₃ htr_bob htr₄ htr₅]
    obtain ⟨_, _, _, _, _, _, _, _, _, hEv₁⟩ := exists_aliceDone_of_pendingPreKey_local (htr_ms' ▸ hle₁) hppk₁
    have hpin₁ := aliceDone_split81_pin hNe htr₁ hpre₀ (hm₀ ▸ htr₂) (hm₀ ▸ hmid₁') hm₁' htr₃ hmid₂' hm₂'
      htr_bob hmid₃' hm₃' htr₄ hmid₄' hm₄ htr₅ hmid₅' hm₅' hpost₅' hEv₁
    obtain ⟨_, _, _, _, _, _, _, _, _, hEv₂⟩ := exists_aliceDone_of_pendingPreKey_local (htr_ms' ▸ hle₂) hppk₂
    have hpin₂ := aliceDone_split81_pin hNe htr₁ hpre₀ (hm₀ ▸ htr₂) (hm₀ ▸ hmid₁') hm₁' htr₃ hmid₂' hm₂'
      htr_bob hmid₃' hm₃' htr₄ hmid₄' hm₄ htr₅ hmid₅' hm₅' hpost₅' hEv₂
    obtain ⟨_, _, _, _, _, _, _, _, _, hEv₅⟩ := exists_aliceDone_of_pendingPreKey_local (htr_ms' ▸ hle₅) hppk₅
    have hpin₅ := aliceDone_split81_pin hNe htr₁ hpre₀ (hm₀ ▸ htr₂) (hm₀ ▸ hmid₁') hm₁' htr₃ hmid₂' hm₂'
      htr_bob hmid₃' hm₃' htr₄ hmid₄' hm₄ htr₅ hmid₅' hm₅' hpost₅' hEv₅
    obtain ⟨hek₁_mem, hct₁_mem, hek₂_mem, hct₂_mem⟩ := ek_ct_mem_prefixTerms_of_links81Own hown
    obtain ⟨hm₁_mem, hm₂_mem, hm₅_mem, _⟩ := WsIdx1Split81MemoNewSubDefs.prefixTerms_mem_of_ws81Idx1RunInv hinv
    intro u hu; rw [hvis_send] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hpin₁ with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
    · rcases hpin₁ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
    · exact hm₁_mem
    · rcases hpin₂ with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
    · rcases hpin₂ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
    · exact hm₂_mem
    · rcases hpin₅ with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
    · rcases hpin₅ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
    · exact hm₅_mem
  · have hM' := WsIdx1Split81MemoCloseFinal.split81MemoCensusOwn r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown
    intro h; unfold BobStartCollision BobSessionStartCollidesOrImplicitRejects at h; dsimp only at h
    rcases hP : parseTrSignalMsg (WsIdx1CensusDefs.x81Idx1 r tr₁ tr₂ tr₄ cl₁).msg with _ | msg <;>
      simp only [WsIdx1Split81Census.split81NewTerms, hP] at h hM'
    · exact hM' h
    · exact h.elim (fun hm => hM' (Symbolic.BugInjection.Proofs.Common443.CompExcuse.memoCollisionOn_bobTrials_to_bobTerms hP hm)) (hO r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ msg hfits hp hinv hP)

theorem callsOf_append_local : ∀ (a b : List CliEvent), callsOf (a ++ b) = callsOf a ++ callsOf b
  | [], _ => rfl
  | .run _ :: a, b => by simp only [List.cons_append, callsOf, callsOf_append_local a b]; split <;> rfl
  | .env _ :: a, b => by simp only [List.cons_append, callsOf, callsOf_append_local a b]

theorem schedFits_prefix_cliEvents {evs₁ evs₂ : List CliEvent} (h : cliEvents = evs₁ ++ evs₂) :
    SchedFits (callsOf evs₁) Witnesses.Cheval26WeakStateIdx1.who Witnesses.Cheval26WeakStateIdx1.ok := by
  have h0 := schedFits_cliEvents; rw [h, callsOf_append_local] at h0
  refine ⟨?_, fun k p b hk => h0.2 k p b ?_⟩
  · obtain ⟨t, ht⟩ := h0.1; exact ⟨(callsOf evs₂).map Prod.fst ++ t, by simpa [List.map_append, List.append_assoc] using ht⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]; exact hk

theorem not_readCollisionCliClassical_sub_take3 {r : Records} {S : Sem} {g : Ghost}
    {ss : List Step} {evs : List CliEvent}
    (hsub : ∀ e ∈ evs, e ∈ ([.run ev0, .run ev1, .run ev2] : List CliEvent)) :
    ¬ ReadCollisionCliClassical SpecTop.compI0 r S g ss evs := by
  refine not_readCollisionCliClassical_of_no_recv fun ev' _ hev' ⟨_, hcmd'⟩ _ => ?_
  have hmem := hsub (.run ev') hev'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h <;> (injection h with h'; subst h'; cases hcmd')

theorem not_knownBaseKeyOn_take3 {r : Records} {S : Sem} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {p : PreKeyFields} (hwf : ProtocolSetupWF r)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2]) :
    ¬ KnownBaseKeyOn SpecTop.compI0 S g (runTrace r ss) p := by
  obtain ⟨τ, ms, hex_cli, _, _, htr, _⟩ :=
    xlate_inv_with_noBrk hwf (schedFits_prefix_cliEvents (evs₂ := [.run ev3, .run ev4, .run ev5, .run ev6]) rfl)
      hex (not_readCollisionCliClassical_sub_take3 fun _ h => h)
  have hnk := not_knownBaseKey_cli_8 (p := p) hex_cli; unfold KnownBaseKey at hnk; rwa [htr] at hnk

theorem not_readCollisionCliClassical_take5 {r : Records} {S : Sem} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} (hwf : ProtocolSetupWF r)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4]) :
    ¬ ReadCollisionCliClassical SpecTop.compI0 r S g ss [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4] := by
  refine not_readCollisionCliClassical_of_not_knownBaseKeyOn hex fun evs₁ ev evs₂ _ hevs ⟨_, hcmd⟩ _ => ?_
  rcases evs₁ with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, evs₁⟩⟩⟩⟩⟩ <;> simp at hevs
  · obtain ⟨rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, rfl, rfl, _⟩ := hevs; obtain ⟨p40, hp40⟩ := wireAt40_parses
    exact ⟨p40, hp40, fun _ _ hex₁ => not_knownBaseKeyOn_take3 hwf hex₁⟩
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := hevs; cases hcmd

theorem not_readCollisionCliClassical_take6 {r : Records} {S : Sem} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} (hwf : ProtocolSetupWF r)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4, .run ev5]) :
    ¬ ReadCollisionCliClassical SpecTop.compI0 r S g ss [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4, .run ev5] := by
  refine not_readCollisionCliClassical_of_not_knownBaseKeyOn hex fun evs₁ ev evs₂ _ hevs ⟨_, hcmd⟩ _ => ?_
  rcases evs₁ with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, evs₁⟩⟩⟩⟩⟩⟩ <;> simp at hevs
  · obtain ⟨rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, rfl, rfl, _⟩ := hevs; obtain ⟨p40, hp40⟩ := wireAt40_parses
    exact ⟨p40, hp40, fun _ _ hex₁ => not_knownBaseKeyOn_take3 hwf hex₁⟩
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, _⟩ := hevs; cases hcmd
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩ := hevs; cases hcmd

theorem not_knownBaseKeyOn_take6 {r : Records} {S : Sem} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {p : PreKeyFields}
    (hwf : ProtocolSetupWF r) (hp : parsePreKeyWire (wireAt 81) = some p)
    (hex : ExplainsClassical SpecTop.compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4, .run ev5]) :
    ¬ KnownBaseKeyOn SpecTop.compI0 S g (runTrace r ss) p := by
  obtain ⟨τ, ms, hex_cli, _, _, htr, _⟩ :=
    xlate_inv_with_noBrk hwf (schedFits_prefix_cliEvents (evs₂ := [.run ev6]) rfl)
      hex (not_readCollisionCliClassical_take6 hwf hex)
  have hnk := not_knownBaseKey_cli_16 hp hex_cli; unfold KnownBaseKey at hnk; rwa [htr] at hnk

theorem spec_half_pinned :
    cliCompShape.SpecHalf (cliCompFitsPinned Witnesses.Cheval26WeakStateIdx1Cli.setup)
      Witnesses.Cheval26WeakStateIdx1Cli.trace := by
  intro (iw : cliCompShape.Interp) (r : Records) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = SpecTop.compI0 := hfits.1.2.1
  have hfits0 : compFitsPinned Witnesses.Cheval26WeakStateIdx1.setup SpecTop.compI0 r := hiw ▸ cliSetup_eq.symm ▸ hfits.1
  refine ⟨hwf, fun (S : Sem) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis Witnesses.Cheval26WeakStateIdx1Cli.trace) ∨
    CollisionAfterExplainedPrefix iw.1 r S Witnesses.Cheval26WeakStateIdx1Cli.trace at hdisj
  rw [← cliEvents_eq, hiw] at hdisj
  rcases hdisj with ⟨g, ss, vis, hex⟩ | hcol
  · have hex_cl := explainsClassical_of hex cliEvents_breakFree
    have hnrc : ¬ ReadCollisionCliClassical SpecTop.compI0 r S g ss cliEvents := by
      refine not_readCollisionCliClassical_of_not_knownBaseKeyOn hex_cl fun evs₁ ev evs₂ _ hevs ⟨_, hcmd⟩ _ => ?_
      rcases list_eq_seven_splits hevs with
        ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ |
        ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ <;> injection hev with hev' <;> subst hev'
      · cases hcmd
      · cases hcmd
      · cases hcmd
      · obtain ⟨p40, hp40⟩ := wireAt40_parses; exact ⟨p40, hp40, fun _ _ hex₁ => not_knownBaseKeyOn_take3 hwf hex₁⟩
      · cases hcmd
      · cases hcmd
      · obtain ⟨p81, hp81⟩ := wireAt81_parses; exact ⟨p81, hp81, fun _ _ hex₁ => not_knownBaseKeyOn_take6 hwf hp81 hex₁⟩
    obtain ⟨τ, ms, hex_cli, _, hnb, _⟩ := xlate_inv_with_noBrk hwf schedFits_cliEvents hex_cl hnrc
    exact no_coinSplit_matchedPrefix hfits0 hnb hex_cli.1 hex_cli.2.1
  · refine not_collisionAfterExplainedPrefix_of_splits cliEvents_breakFree ?_ hcol
    intro evs₁ ev evs₂ g ss vis hevs hex
    rcases list_eq_seven_splits hevs with
      ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ |
      ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ <;> injection hev with hev' <;> subst hev'
    · exact not_nextEventCollidesClassical_init rfl
    · refine not_nextEventCollidesClassical_send hwf
        (schedFits_prefix_cliEvents (evs₂ := [.run ev1, .run ev2, .run ev3, .run ev4, .run ev5, .run ev6]) rfl)
        hex (not_readCollisionCliClassical_sub_take3 fun _ h => by simp at h ⊢; tauto) rfl
        fun τ ms hex_cli _ hnb hbme hmcol => not_pt_cli_2_self hfits0 hnb hex_cli
          ⟨rfl, by simpa [BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt, ev1, eventBytes] using hbme⟩ hmcol
    · refine not_nextEventCollidesClassical_send hwf
        (schedFits_prefix_cliEvents (evs₂ := [.run ev2, .run ev3, .run ev4, .run ev5, .run ev6]) rfl)
        hex (not_readCollisionCliClassical_sub_take3 fun _ h => by simp at h ⊢; tauto) rfl
        fun τ ms hex_cli _ hnb hbme hmcol => not_pt_cli_5_self hfits0 hnb hex_cli
          ⟨rfl, by simpa [BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt, ev2, eventBytes] using hbme⟩ hmcol
    · obtain ⟨p40, hp40⟩ := wireAt40_parses; rcases hmsg : wireAt 40 with _ | ⟨tag, body⟩
      · rw [hmsg] at hp40; cases hp40
      · have htag : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag :=
          fun h => wireAt_40_head_ne_whisper (by rw [hmsg, h]; rfl)
        refine not_nextEventCollidesClassical_recv_preKey_sub hwf
          (schedFits_prefix_cliEvents (evs₂ := [.run ev3, .run ev4, .run ev5, .run ev6]) rfl)
          hex (not_readCollisionCliClassical_sub_take3 fun _ h => h) rfl hmsg htag (hmsg ▸ hp40)
          (not_knownBaseKeyOn_take3 hwf hex) (not_kyberMismatch_cli_8 hfits0.1 p40 hp40)
          fun τ ms hex_cli _ hnb htr hsalts hpre hpt => ?_
        simpa [hmsg] using noBscCliAt_8_sub hfits0 hex hp40 hex_cli hnb htr hsalts hpre hpt
    · exact not_nextEventCollidesClassical_init rfl
    · refine not_nextEventCollidesClassical_send hwf
        (schedFits_prefix_cliEvents (evs₂ := [.run ev5, .run ev6]) rfl)
        hex (not_readCollisionCliClassical_take5 hwf hex) rfl
        fun τ ms hex_cli _ hnb hbme hmcol => not_pt_cli_13_self hfits0 hnb hex_cli
          ⟨rfl, by simpa [BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt, ev5, eventBytes] using hbme⟩ hmcol
    · obtain ⟨p81, hp81⟩ := wireAt81_parses; rcases hmsg : wireAt 81 with _ | ⟨tag, body⟩
      · rw [hmsg] at hp81; cases hp81
      · have htag : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag :=
          fun h => wireAt_81_head_ne_whisper (by rw [hmsg, h]; rfl)
        refine not_nextEventCollidesClassical_recv_preKey_sub hwf
          (schedFits_prefix_cliEvents (evs₂ := [.run ev6]) rfl)
          hex (not_readCollisionCliClassical_take6 hwf hex) rfl hmsg htag (hmsg ▸ hp81)
          (not_knownBaseKeyOn_take6 hwf hp81 hex) (not_kyberMismatch_cli_16 hfits0.1 p81 hp81)
          fun τ ms hex_cli _ hnb htr hsalts hpre hpt => ?_
        simpa [hmsg] using noBscCliAt_16_sub hfits0 hex hp81 hex_cli hnb htr hsalts hpre hpt

theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, cliCompFitsPinned Witnesses.Cheval26WeakStateIdx1Cli.setup iw r :=
  Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.cliCompFitsPinned_satisfiable_ws1

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CliBridge
